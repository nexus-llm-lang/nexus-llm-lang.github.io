---
layout: default
title: Semantics
---

# Semantics

This document describes the execution model of Nexus.

## Evaluation Strategy

Nexus is **call-by-value**. Each expression runs in full before its result reaches a function or constructor.

### Evaluation Order

Strict **left-to-right**:
- Function arguments: `f(a: e1, b: e2)` evaluates `e1` before `e2`
- Binary operators: `e1 + e2` evaluates `e1` before `e2`
- Records and constructors: fields evaluated in source order

### Label Order Independence

Labeled arguments at call sites may appear in any order. The calls `f(b: 2, a: 1)` and `f(a: 1, b: 2)` end up with the same pairing. Argument expressions still evaluate left-to-right in source order, regardless of which labels they carry.

## Scoping

**Lexical scoping.** Bindings are visible in the block where they are defined and in nested blocks.

**Shadowing** is permitted. An inner `let` can reuse a name from an outer scope, masking it until the inner block ends.

## Sigil Behavioral Semantics

Sigils are no mere annotations; they pin down runtime behavior.

### Mutability (`~`)

- **Stack-confined**: mutable bindings exist only on the stack of the defining function
- **No escape**: cannot be returned, stored in heap structures, or captured by closures
- **Assignment**: `~x <- expr` updates the value
- **Concurrency**: cannot be captured into a thunk (`@`) that may evaluate in parallel — preserves stack confinement and prevents data races (see [lazy.md](./lazy))

### Linearity (`%`)

- **Exactly-once consumption** (composites): must be consumed via function call, pattern match, or return
- **Auto-drop** (primitives): `i32`, `i64`, `f32`, `f64`, `bool`, `char`, `string`, `unit` (plus their `%`/`&`/`~` wrappers) are released at scope end. See [drop.md](./drop) §Auto-Droppable Types for the full predicate.
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

A `throw` ends the current computation at once and unwinds the call stack up to the nearest `try/catch`. The `Exn` value lands in the `catch` parameter:

```nexus
try
  throw NotFound(msg: "key")
catch e ->
  // e : Exn
  match e do
    | NotFound(msg: m) -> ()
    | _ -> ()
  end
end
```

Exceptions are checked. Any function that may throw must declare `throws { Exn }`. A `try/catch` clears `Exn` from the protected region.

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

`start` and `end_expr` must be `i64`. The loop variable is immutable in the body. The range is `[start, end_expr)`, so the upper bound is exclusive. When `start >= end_expr`, the body never runs.

## Match as Expression

Match can appear in expression position. Each arm body produces a value:

```nexus
let result = match x do
  | 1 -> 10
  | 2 -> 20
  | _ -> 30
end
```

Every non-diverging arm body must produce the same type. An arm **diverges**, and so drops out of the unified result type, when its last statement is one of:

- `return e` (function-level return)
- `throw e` used as an expression statement
- `let μx = throw e'` (the binding's RHS never produces a value)

When every arm diverges, the match expression takes a fresh type variable, which the surrounding context pins. See the `tail` and `branchType` definitions in [type-system-formal.md](./type-system-formal#T-Match) for the formal carve-out, which `if`/`else` and pattern-let reuse.

```nexus
let result = match x do
  | A -> 5
  | B -> throw NotFound(path: "x")   // diverges — `B` does not pin the result type
end  // result : i64 (from arm A)
```

## Concurrency Model

Nexus expresses deferred computation through the `@` (thunk) sigil. A thunk `let @x = expr` suspends `expr` until forced via `@x`. To force a list of thunks side by side, opt in through `force_all`, exported from the lazy stdlib module.

```nexus
let @p1 = compute1()
let @p2 = compute2()
let xs  = force_all(tasks: [p1, p2])
```

- `@` thunks are unevaluated until forced (`@x`)
- Thunks cannot capture mutable (`~`) bindings — the `~` stack-confinement rule rules out cross-thread aliasing
- The current runtime forces each `force_all` task in turn. Parallel execution over WASI threads is tracked as future work. See [lazy.md](./lazy) for the dispatch primitives and the migration plan.

## Implicit Unit Return

A function whose return type is `unit` may omit the trailing `return ()`. When the body has no `return` at all, the compiler tacks on a `return ()` for you:

```nexus
let greet = fn (name: string) -> unit require { Console } do
  Console.println(val: "Hello, " ++ name)
  // implicit return ()
end
```

A function with a non-`unit` return type still needs an explicit `return`.

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

The runtime calls `main`. Side effects flow through injected handlers. The exit code is `0` on success and non-zero on any error left unhandled.
