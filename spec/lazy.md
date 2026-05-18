---
layout: default
title: Lazy Evaluation, Concurrency, and Parallelism
---

# Lazy Evaluation, Concurrency, and Parallelism (`@`)

The `@` sigil is Nexus's unified primitive for lazy evaluation, concurrency, and parallelism, designed around **one-shot delimited continuations** and **linear types**.

A lazy binding `let @x = expr` suspends `expr` as an unevaluated thunk. Forcing with `@x` evaluates it. Independent thunks within a force expression are evaluated in parallel via DAG scheduling — data dependencies determine execution order, not left-to-right evaluation.

## Design Rationale

- **No async/await keywords**: `@` integrates into the existing sigil system (`%` linear, `&` borrow, `@` lazy) rather than adding new syntax
- **Lazy, not eager**: Unlike JS Promises (eager evaluation, implicit error swallowing), `@` thunks are unevaluated until forced
- **One-shot continuation**: Internally based on one-shot delimited continuations (cf. OCaml 5). Linear types guarantee single-use — no copying, no multi-shot
- **Exception propagation**: No separate rejection channel. `throw` inside a thunk propagates via standard `try/catch` at the force site

## Sigil Table

| Sigil | Meaning | Evaluation | Linearity |
|---|---|---|---|
| (none) | Value | Eager | Non-linear |
| `%` | Linear value | Eager | Linear |
| `@` | Suspended computation | Lazy | Linear |
| `&` | Borrow | — | Borrow |

## Syntax

```nexus
let @x = expensive_computation()  // creates thunk, NOT evaluated
let result = @x                    // forces thunk, evaluates now
```

`@T` is the type of a suspended computation producing `T`:

```nexus
let delayed: @string = @("hello" ++ " world")
```

## Parallel Evaluation

`@x` forces a single thunk. Parallel evaluation of a *list* of thunks is opt-in via the stdlib helper `force_all` (`std:lazy`):

```nexus
let @p1 = compute1()
let @p2 = compute2()
let xs = force_all(tasks: [p1, p2])   // [p1's result, p2's result]
```

Each thunk is dispatched as a task (one struct in linear memory) and joined left-to-right. The dispatch primitives `lazy_spawn` / `lazy_join` live in `nxlib/stdlib/runtime/lazy.nx`.

> **Status note.** The current `lazy_spawn` implementation is *sequential* — it forces each thunk inline and stores the result, so `force_all` runs all tasks one after another. A `wasi:threads` worker entry point (`wasi_thread_start`) is exported for compatibility with `wasmtime -S threads` runs, but the sequential `lazy_spawn` does not invoke it. True parallel execution via the component-model `future<T>` migration is tracked as future work.

## Linearity

`@T` is inherently linear — a one-shot continuation must be consumed exactly once. Three consumption operations:

| Operation | Executes? | Waits? | Use case |
|---|---|---|---|
| `@x` (force) | Yes | Yes | Normal evaluation |
| `detach(a: x)` | Yes | No | Fire-and-forget |
| `cancel(a: x)` | No | — | Discard unneeded computation |

Unconsumed `@T` is a compile error. Copying is forbidden (not multi-shot).

`@`'s linearity is orthogonal to the result's linearity:

```nexus
let @a = compute_string()   // @string — result is copyable
let @b = acquire_server()   // @%Server — result is linear
let s = @a                  // s: string (non-linear binding)
let %srv = @b               // %srv: %Server (linear binding)
```

Capturing `@x` in a closure makes the closure itself linear:

```nexus
let @x = heavy_compute()
let f = fn () -> i64 do @x end   // f captures @x → f is linear
f()   // OK: consumes f
f()   // ERROR: f already consumed
```

## Deadlock Freedom

Linear types structurally prevent deadlock:

1. **No forward references**: `let` bindings are sequential — a thunk cannot reference a later-defined `@` value, so simple cycles are syntactically impossible
2. **No sharing**: `@T` is non-copyable — two thunks cannot depend on the same `@` value, so circular dependencies cannot be constructed
3. **Acyclic DAG**: The parallel evaluation DAG is derived from the AST, which is structurally a tree (acyclic)

## Data Race Freedom

The existing borrow checker prevents data races during parallel force:

```nexus
let %arr = [| 0, 0 |]
let @a = do let lock = &%arr; lock[0] <- 1 end
let @b = do let lock = &%arr; lock[1] <- 2 end   // ERROR: %arr already borrowed
```

Shared mutable state across parallel thunks requires explicit concurrency primitives (channels, atomics).

## Exception Semantics

Exceptions thrown inside a thunk propagate at the force site via standard `try/catch`:

```nexus
let @result = do
  throw NotFound(path: "/missing")
end

try
  let v = @result   // force → exception propagates here
catch
  | NotFound(path: p) -> handle(p: p)
end
```

When `force_all` is used and one of the forced thunks throws, the exception propagates at the join point and the remaining thunks' results are discarded; linear types guarantee no resource leak.

## Standard Library (`std:lazy`)

Only the `@` sigil is built into the language. Combinators are provided as stdlib functions:

| Function | Signature | Description |
|---|---|---|
| `force_all` | `(tasks: [@T]) -> [T]` | Forces every thunk and returns the results in input order (currently sequential; see "Parallel Evaluation" above) |
| `detach` | `(a: @T) -> unit` | Forces the thunk and discards the result |
| `cancel` | `(a: @T) -> unit` | Forces the thunk and discards the result (no runtime drop hook exists — `cancel` and `detach` are observationally equivalent) |
| `race` | `(a: @T, b: @T) -> T` | Forces `a` then `b` sequentially, returns `a`'s result (no first-of-two arbiter — both arguments run) |

## Current Implementation Status

The `@` sigil is fully implemented:
- **Thunk creation**: `let @x = expr` — desugars to zero-argument closures
- **Force**: `@x` — evaluates and consumes the thunk (one-shot)
- **Type system**: `@T` tracked as linear; unconsumed `@T` is a compile error (including primitives like `@i64`)
- **Bare-name access**: `x` (without `@`) references the thunk without forcing — enables `cancel(a: x)` / `detach(a: x)`
- **Closure linearization**: Capturing `@x` in a closure makes the closure linear
- **`std:lazy`**: `race`, `cancel`, `detach`, `force_all` combinators — all currently sequential. See `nxlib/stdlib/runtime/lazy.nx` for the task-struct dispatch primitives (`lazy_spawn` / `lazy_join`).

---

See also: [Exception Groups](../exception-groups), [Types](../types), [Syntax](../syntax)
