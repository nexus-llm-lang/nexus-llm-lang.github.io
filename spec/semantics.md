---
layout: default
title: Semantics
---

# Semantics

This document describes the execution model of Nexus.

## Evaluation Strategy

Nexus is **call-by-value**. All expressions are fully evaluated before being passed to functions or constructors.

### Evaluation Order

Strict **left-to-right**:
- Function arguments: `f(a: e1, b: e2)` evaluates `e1` before `e2`
- Binary operators: `e1 + e2` evaluates `e1` before `e2`
- Records and constructors: fields evaluated in source order

### Label Order Independence

Labeled arguments at call sites may appear in any order. `f(b: 2, a: 1)` and `f(a: 1, b: 2)` pass the same values. Argument expressions are evaluated left-to-right in source order regardless of label names.

## Scoping

**Lexical scoping.** Bindings are visible in the block where they are defined and in nested blocks.

**Shadowing** is permitted. An inner `let` can reuse a name from an outer scope, masking it until the inner block ends.

## Sigil Behavioral Semantics

Sigils are not annotations -- they impose runtime behavioral constraints.

### Mutability (`~`)

- **Stack-confined**: mutable bindings exist only on the stack of the defining function
- **No escape**: cannot be returned, stored in heap structures, or captured by closures
- **Assignment**: `~x <- expr` updates the value
- **Concurrency**: cannot be captured into a thunk (`@`) that may evaluate in parallel — preserves stack confinement and prevents data races (see [lazy.md](./lazy))

### Linearity (`%`)

- **Exactly-once consumption** (composites): must be consumed via function call, pattern match, or return
- **Auto-drop** (primitives): `i64`, `f64`, `bool`, `string`, `unit` are released at scope end
- **Static enforcement**: the type checker tracks linear bindings and rejects programs that leak or double-use them
- **No discard**: `_` cannot discard composite linear values
- **No mutable ref**: `~` cannot hold linear types

### Borrowing (`&`)

- **Immutable view**: read-only access without consumption
- **Non-consuming**: the source binding remains live
- **Coercion**: `&T` coerces to `T` for reading operations

## Closures and Captures

- **Lexical captures**: lambdas capture immutable bindings from enclosing scope
- **No mutable capture**: closures cannot capture `~` bindings
- **Linearity propagation**: capturing a `%` binding makes the closure linear (single-use)
- **Recursive lambdas**: must use an immutable `let` binding with explicit type annotation

## Exception Propagation

`raise` immediately terminates the current computation and unwinds the call stack until it reaches a `try/catch` block. The `Exn` value is passed to the `catch` parameter:

```nexus
try
  raise NotFound(msg: "key")
catch e ->
  // e : Exn
  match e do
    | NotFound(msg: m) -> ()
    | _ -> ()
  end
end
```

Exceptions are checked -- any function that may raise must declare `throws { Exn }`. `try/catch` discharges `Exn` from the protected region.

## Loops

### While Loop

```nexus
while condition do
  body
end
```

Evaluates `condition` before each iteration. If the condition is `false`, exits. The condition must be `bool`. Returns `unit`.

### For Loop

```nexus
for var = start to end_expr do
  body
end
```

Desugared to:

```nexus
let ~var = start
let ~__end = end_expr
while ~var < ~__end do
  body
  ~var <- ~var + 1
end
```

`start` and `end_expr` must be `i64`. The loop variable is immutable within the body. The range is `[start, end_expr)` (exclusive upper bound). If `start >= end_expr`, the body never executes.

## Match as Expression

Match can appear in expression position. Each arm body produces a value:

```nexus
let result = match x do
  | 1 -> 10
  | 2 -> 20
  | _ -> 30
end
```

All non-diverging arm bodies must produce the same type. An arm **diverges** — and is excluded from the unified result type — when its last statement is:

- `return e` (function-level return)
- `raise e` used as an expression statement
- `let μx = raise e'` (the binding's RHS never produces a value)

If every arm diverges, the match expression's type is a fresh type variable (left to be pinned by surrounding context). See the `tail`/`branchType` definitions in [type-system-formal.md](./type-system-formal#T-Match) for the formal carve-out reused by `if`/`else` and pattern-let.

```nexus
let result = match x do
  | A -> 5
  | B -> raise NotFound(path: "x")   // diverges — `B` does not pin the result type
end  // result : i64 (from arm A)
```

## Concurrency Model

Nexus expresses parallelism through the `@` (thunk) sigil rather than a dedicated `conc`/`task` block — the latter was removed during the migration to data-dependency-driven scheduling. Independent thunks within a force expression evaluate in parallel via DAG scheduling; data dependencies determine execution order, not lexical position.

```nexus
let @p1 = compute1()
let @p2 = compute2()
let r   = @{ r1: p1, r2: p2 }   // both thunks forced in parallel
```

- `@` thunks are unevaluated until forced (`@x`, `@{...}`)
- A force expression with N independent thunks may evaluate them concurrently
- Thunks cannot capture mutable (`~`) bindings — the `~` stack-confinement rule rules out cross-thread aliasing
- Compiled WASM uses OS-thread parallelism via WASI threads; see [lazy.md](./lazy) for the full force / DAG scheduling semantics

## Implicit Unit Return

Functions with return type `unit` may omit the trailing `return ()`. If the function body does not contain any `return` statement, the compiler implicitly appends `return ()`:

```nexus
let greet = fn (name: string) -> unit require { Console } do
  Console.println(val: "Hello, " ++ name)
  // implicit return ()
end
```

Functions with non-`unit` return types still require explicit `return`.

## Entrypoint

### `main` Function

Every Nexus program must define a `main` function with these constraints:

- **Signature**: `() -> unit`
- **Effects**: must be empty (all exceptions handled internally)
- **Requirements**: may include any subset of `{ PermFs, PermNet, PermConsole, PermRandom, PermClock, PermProc, PermEnv }`
- **Visibility**: must not be `export`

```nexus
let main = fn () -> unit require { PermConsole } do
  inject stdio.system_handler do
    Console.println(val: "Hello")
  end
  return ()
end
```

The runtime calls `main`, which performs all side effects via injected handlers. Exit code is `0` on success, non-zero on unhandled error.
