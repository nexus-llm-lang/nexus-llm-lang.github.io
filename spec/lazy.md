---
layout: default
title: Lazy Evaluation, Concurrency, and Parallelism
---

# Lazy evaluation, concurrency, and parallelism (`@`)

The `@` sigil rolls lazy evaluation, concurrency, and parallelism into one primitive. The shape rests on **one-shot delimited continuations** and **linear types**.

A lazy binding `let @x = expr` suspends `expr` as an unevaluated thunk. Forcing with `@x` runs it. Within a force expression, thunks with no data dependency on each other run side by side under DAG scheduling; the source order has no say in what fires when.

## Design rationale

- **No async/await keywords**: `@` slots into the sigil system already in place (`%` linear, `&` borrow, `@` lazy), so no new keywords show up.
- **Lazy, then forced**: JS Promises evaluate eagerly and swallow errors quietly. An `@` thunk waits until you force it.
- **One-shot continuation**: The runtime uses one-shot delimited continuations (compare OCaml 5). Linear types keep the use to one, so there's no copy and no multi-shot.
- **Exception propagation**: There's no separate rejection channel. A `throw` inside a thunk surfaces at the force site through the standard `try/catch`.

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

`@x` forces a single thunk. To run a *list* of thunks side by side, opt in through the stdlib helper `force_all`. The wrapper ships in the lazy stdlib module.

```nexus
let @p1 = compute1()
let @p2 = compute2()
let xs = force_all(tasks: [p1, p2])   // [p1's result, p2's result]
```

Each thunk is dispatched as a task — one struct in linear memory — and joined left-to-right. The dispatch primitives `lazy_spawn` and `lazy_join` live in `nxlib/stdlib/runtime/lazy.nx`.

> **Status note.** The current `lazy_spawn` runs *sequentially*. It forces each thunk inline and stores the result, so `force_all` runs the tasks one after the other. A `wasi:threads` worker entry point (`wasi_thread_start`) is exported for runs under `wasmtime -S threads`, but the sequential `lazy_spawn` does not invoke it. The plan is to switch over to the component-model `future<T>` for real parallel execution. That switch is tracked as future work.

## Linearity

`@T` is linear. A one-shot continuation must be consumed exactly once. The three consume forms are:

| Operation | Executes? | Waits? | Use case |
|---|---|---|---|
| `@x` (force) | Yes | Yes | Normal evaluation |
| `detach(a: x)` | Yes | No | Fire-and-forget |
| `cancel(a: x)` | No | — | Discard unneeded computation |

An unconsumed `@T` is a build error. Copying is forbidden, so a thunk runs at most once.

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

Linear types prevent deadlock by construction.

1. **No forward references.** `let` bindings run in order. A thunk cannot reach a later `@` value, so a simple cycle never lands in the source.
2. **No sharing.** `@T` cannot be copied. Two thunks cannot share an `@` value, so a circular dependency is unreachable.
3. **Acyclic DAG.** The parallel evaluation DAG comes from the AST. The AST is a tree, and a tree has no cycles.

## Data Race Freedom

The existing borrow checker prevents data races during parallel force:

```nexus
let %arr = [| 0, 0 |]
let @a = do let lock = &%arr; lock[0] <- 1 end
let @b = do let lock = &%arr; lock[1] <- 2 end   // ERROR: %arr already borrowed
```

Sharing mutable state across parallel thunks requires explicit concurrency primitives — channels, atomics, and the like.

## Exception Semantics

A throw inside a thunk surfaces at the force site, where the usual `try/catch` picks it up:

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

When `force_all` runs and one of its thunks throws, the exception surfaces at the join point. The other thunks' results are then discarded. Linear types keep this leak-free.

## Standard Library (`std:lazy`)

Only the `@` sigil is built into the language. The rest ship as stdlib functions.

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
