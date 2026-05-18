---
layout: default
title: Drop Semantics
---

# Drop Semantics

This page sets out when a Nexus value stops being observable. The cases: a binding leaves scope, code drops a value on purpose, or the runtime claws back memory. The rules sit in different places — [semantics.md](semantics), [types.md](types), [lazy.md](lazy), and [type-system-formal.md](type-system-formal) — so this page gathers them.

## Design Summary

Nexus has **no runtime drop**. The compiler emits no destructor, no finalizer, no RAII binder, and no `Drop` op in MIR or LIR. Linear duties are *proven away at type-check time*. The **bump arena** that backs heap data handles all memory cleanup.

Three rules cover the whole story.

1. **Auto-drop.** A fixed list of types may fall out of scope without an explicit consume (§Auto-Droppable Types).
2. **Linear use-once.** Every other linear binding must reach a known consume site once before scope ends. The shapes that count as linear are `%T`, `@T`, and any record or closure that holds one (§Linear Consumption).
3. **Arena reclaim.** Heap values are released as a batch when the arena frame around them is reset. There is no per-value `free` (§Memory Reclamation).

The type checker rejects any program that breaks rule 2. Rule 1 carves out the cases where the checker can stay silent. Rule 3 explains why the compiler emits no per-value cleanup code.

## Auto-Droppable Types

The predicate `is_auto_droppable(τ)` (`src/typecheck/linearity.nx`) names the set of types that may slide out of scope. It is the **sole** way a binding can vanish without an explicit consume.

```
auto_droppable(τ) ≡
  τ ∈ { i32, i64, f32, f64, IntLit, FloatLit, bool, char, string, unit }
∨ τ = %σ ∧ auto_droppable(σ)     — linear wrapper around a droppable inner
∨ τ = &σ ∧ auto_droppable(σ)     — borrow wrapper
∨ τ = ~σ ∧ auto_droppable(σ)     — mutable wrapper
∧ τ ≠ @σ                          — lazy thunks are never auto-droppable
∧ τ ≠ [|σ|]                       — arrays are never auto-droppable
```

The recursion clauses make `%i64`, `&string`, and `~bool` auto-droppable. They do not make `%Handle` (a record) auto-droppable. The negative clause for `@σ` holds even when `σ` is auto-droppable; an `@i64` must still be forced or routed through an explicit consume form.

Arrays `[|σ|]` are never auto-droppable, no matter the element type. The linear contents — cells and captured handles — must be released by hand (see [type-system-formal.md §Linearity](./type-system-formal#section-1)). The immutable list type `[σ]` is also **not** auto-droppable.

## Linear Consumption

A linear value must reach one of the channels below before its function ends. These are the *only* paths that close out a non-auto-droppable linear obligation.

| Channel | Form | Notes |
|---|---|---|
| Function call | `f(x: %v)` | `%v` is consumed by the call argument |
| Pattern match | `match %v do \| C(...) -> ... end` | The scrutinee is consumed; bindings in the pattern carry the obligation forward (see [types.md](types)) |
| Return | `return %v` | Transfers obligation to the caller |
| Assignment | `~r <- %v` | Transfers obligation into the mutable cell (subject to `~` rules) |
| Throw | `throw SomeExn(payload: %v)` | The payload is consumed; control leaves the scope |

`let _ = e` is **not** a consume; it works only when the right-hand side is auto-droppable. See [Wildcard Discard](#wildcard-discard) below.

### Function-end check

`require_empty_or_droppable` (`src/typecheck/linearity.nx`) runs at the end of every `EagerBody`. The check looks at the live linear set. Either the set is empty, or every name in it is a parameter whose declared inner type is auto-droppable. Otherwise the checker throws `LinearUnused(name, span)`.

### Throwable-call leak guard

A call whose `throws` row is non-empty counts as a possible exit. Take any linear binding live at such a site. If a catch arm does not re-consume it, the call is rejected as `LinearLeakAcrossThrowableCall`. The rule shows up in [semantics.md](semantics) §Exception Propagation, and the code lives in `src/typecheck/linearity.nx`.

> **Note**: there is no runtime cleanup on unwind. The leak guard rests on a static proof. By the time `throw` runs, no linear obligation is still live in the abandoned scope.

## Wildcard Discard

The form `let _ = e` parses as a `Let` whose binder name is `"_"`. The linearity checker gives that name no special status.

- `check_expr(e)` runs first and consumes any linear ref inside `e`. So `let _ = consume(x: %y)` consumes `%y` via the call.
- When `let_binds_linear(e)` returns true — `e` is a `Call` whose return type is `%T` or `@T` — the binder `_` joins the live linear set. The function-end check flags it later. Since `_` is no parameter, the auto-droppable carve-out cannot save it.
- When `let_binds_linear(e)` returns false, `_` stays untracked. That is the legit "primitive auto-drop" idiom.

`match %v do | _ -> () end` consumes the scrutinee through the match channel. The wildcard binds nothing, so no follow-up duty remains.



## Lazy Thunks (`@T`)

`@T` is the one shape that is *always* linear, no matter the inner type. The only consume that runs the body is the **force** form `@x`. The stdlib combinators in `nxlib/stdlib/lazy.nx` are sugar over force.

```nexus
export let cancel = fn <T>(a: @T) -> unit do
  let _ = @a       // forces and discards
  return ()
end

export let detach = fn <T>(a: @T) -> unit do
  let _ = @a       // forces and discards
  return ()
end
```


## Memory Reclamation

Nexus does **not** garbage-collect, refcount, or per-value-`free`. Heap memory comes from a bump arena and gets reclaimed in bulk through the runtime arena module. The relevant intrinsic externals live there.

| Intrinsic | Effect |
|---|---|
| `heap_mark()` | Snapshot the arena's bump pointer |
| `heap_reset(mark)` | Rewind the bump pointer to `mark`; everything allocated since is gone |
| `heap_swap(base)` | Atomically install `base` as the new arena head and return the prior value (used to route allocations to a scratch arena) |

Codegen for these lives in `src/backend/codegen.nx` (`emit_heap_mark` and `emit_heap_reset`). The compiler emits no per-value cleanup. At the next reset, closures, records, and linear handles all go unreachable in one shot.

> **Consequence**: a future destructor type would need one of two paths. One is a new MIR/LIR drop op with codegen support. The other is explicit `dispose(...)` calls at the user level, guarded by linearity. Neither exists today.

## WASM `op_drop` Emissions

The WASM `drop` opcode (`0x1A`) shows up in the emitter purely as **stack housekeeping**. It is never a value-cleanup op. Every site today is:

| Site | Purpose |
|---|---|
| `src/backend/codegen/atom.nx:119` | After packing a `unit` into i64, drop the pre-pack stack slot |
| `src/backend/codegen/atom.nx:141`, `:165` | Field store/load for `unit`-typed record fields — drop the placeholder |
| `src/backend/codegen/atom.nx:205` | Discard `memory.grow` return value (`-1` on failure) |
| `src/backend/codegen.nx` | Let-binder whose declared type is `unit` — drop a non-unit RHS result |
| `src/backend/codegen.nx` | `_start` shim drops the `main` return value when non-unit |

None of these run user cleanup logic. They balance the WASM operand stack and nothing more.

## Closures and Captures

A closure stores its captures as fields of a heap object (`emit_closure_captures`, `src/backend/codegen.nx`). The closure's *linearity* comes from capture. If the body refs any outer linear binding, the closure is itself linear (`collect_captured_linears`, `src/typecheck/linearity.nx`).

When a linear closure is consumed, codegen does **not** free the heap object. The next `heap_reset` reclaims it. There is no per-closure destructor. A closure that captures `%h` runs no "release" on `%h`. The capture was the consume for `%h`, done at closure-creation time.

## Exceptions and Drop

A `throw` in Nexus emits WASM `op_throw`, paired with a `try_table` for catch. It runs no cleanup landingpads. The static guarantee: no linear is live across a throwable boundary unless every catch arm re-consumes it. The runtime never sees a chance to "drop" anything on unwind, since nothing is left to drop.

The shape is structural rather than aspirational. Adding a destructor type later would need landing-pad codegen that the compiler does not emit today.

## Cross-Reference Summary

| Concern | Authoritative location |
|---|---|
| Set of auto-droppable types | `src/typecheck/linearity.nx` |
| Function-end consumption check | `src/typecheck/linearity.nx` |
| Throwable-call leak guard | `src/typecheck/linearity.nx` |
| `_` wildcard binder semantics | `src/typecheck/linearity.nx` |
| Lazy combinators | `nxlib/stdlib/lazy.nx` |
| Arena intrinsics | `src/backend/codegen.nx` |
| Spec rules | [semantics.md](semantics), [types.md](types), [type-system-formal.md](type-system-formal) §T-Proj, §T-Seq-Cons |

