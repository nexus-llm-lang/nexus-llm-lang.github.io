---
layout: default
title: Drop Semantics
---

# Drop Semantics

This document specifies how Nexus values cease to be observable: when a binding goes out of scope, when a value is explicitly discarded, and when the runtime reclaims memory. It collects rules that are otherwise scattered across [semantics.md](semantics), [types.md](types), [lazy.md](lazy), and [type-system-formal.md](type-system-formal).

## Design Summary

Nexus has **no runtime drop mechanism**. There is no destructor, finalizer, RAII binder, or `Drop` instruction in MIR/LIR. Cleanup of linear obligations is *proven at type-check time*; cleanup of memory is delegated to the **bump-allocated arena** that backs heap allocations.

Three rules cover everything:

1. **Auto-drop**: a closed list of types may go out of scope without explicit consumption (§Auto-Droppable Types).
2. **Linear use-once**: every other binding that is structurally linear (`%T`, `@T`, or a record/closure transitively containing one) must be consumed exactly once via a documented consumption channel before its scope ends (§Linear Consumption).
3. **Arena reclamation**: heap-resident values are released wholesale when their enclosing arena frame is reset; per-value `free` does not exist (§Memory Reclamation).

The type checker rejects any program that violates rule 2; rule 1 carves out the cases where the checker may stay silent; rule 3 explains why no per-value cleanup code is emitted.

## Auto-Droppable Types

The predicate `is_auto_droppable(τ)` (`src/typecheck/linearity.nx:147`) defines the set of types that may silently fall out of scope. It is the **sole** mechanism by which a binding disappears without an explicit consumption channel.

```
auto_droppable(τ) ≡
  τ ∈ { i32, i64, f32, f64, IntLit, FloatLit, bool, char, string, unit }
∨ τ = [σ]                        — array (any element type, see Bug 1)
∨ τ = %σ ∧ auto_droppable(σ)     — linear wrapper around a droppable inner
∨ τ = &σ ∧ auto_droppable(σ)     — borrow wrapper
∨ τ = ~σ ∧ auto_droppable(σ)     — mutable wrapper
∧ τ ≠ @σ                          — lazy thunks are never auto-droppable
```

The recursion clauses imply `%i64`, `&string`, and `~bool` are auto-droppable; `%Handle` (a record) is not. The negative clause for `@σ` holds even when `σ` is itself auto-droppable: `@i64` must still be forced or threaded through an explicit consumption form.

> **Spec coverage gap (`nexus-218q`)**: `semantics.md` §Linearity bullet 2 currently lists only `i64, f64, bool, string, unit`. The actual implementation accepts `i32, f32, IntLit, FloatLit, char, [σ]` plus the three wrapper recursions. The arrays-of-anything carve-out is also under audit (see Bug 1 below).

## Linear Consumption

A value of structurally-linear type must reach exactly one of the following channels before the enclosing function body ends. These are the *only* means by which a non-auto-droppable linear obligation is discharged.

| Channel | Form | Notes |
|---|---|---|
| Function call | `f(x: %v)` | `%v` is consumed by the call argument |
| Pattern match | `match %v do \| C(...) -> ... end` | The scrutinee is consumed; bindings in the pattern carry the obligation forward (see [types.md](types)) |
| Return | `return %v` | Transfers obligation to the caller |
| Assignment | `~r <- %v` | Transfers obligation into the mutable cell (subject to `~` rules) |
| Raise | `raise SomeExn(payload: %v)` | The payload is consumed; control leaves the scope |

`let _ = e` is **not** a consumption channel. It is allowed only when the right-hand side is auto-droppable. See [Wildcard Discard](#wildcard-discard) below.

### Function-end check

`require_empty_or_droppable` (`src/typecheck/linearity.nx:670`) runs at the end of every `EagerBody`. If the live linear set is non-empty and any name is *not* a parameter whose declared inner type is auto-droppable, the checker raises `LinearUnused(name, span)`.

### Throwable-call leak guard

A call whose `throws` row is non-empty is treated as a potential exit. Any linear binding live at such a call site that is not also re-consumed inside every catch arm is rejected with `LinearLeakAcrossThrowableCall`. The rule is documented in [semantics.md](semantics) §Exception Propagation and implemented at `src/typecheck/linearity.nx:1032-1043`.

> **Note**: there is no runtime cleanup on unwind. The leak guard relies on the fact that, by the time `raise` actually executes, no linear obligation can be live in the abandoned scope — the type checker has proven it.

## Wildcard Discard

The form `let _ = e` parses as a `Let` with binder name `"_"`. The linearity checker treats this name with no special privilege:

- `check_expr(e)` is walked first, consuming any linear references inside `e` (e.g. `let _ = consume(x: %y)` consumes `%y` via the call).
- If `let_binds_linear(e)` returns true — i.e. `e` is a `Call` to a function whose return type is `%T` or `@T` — the binder `_` is added to the live linear set, and the function-end check will eventually flag it (because `_` is not a parameter, the auto-droppable carve-out does not apply).
- If `let_binds_linear(e)` returns false, `_` is *not* tracked. This is the legitimate "primitive auto-drop" idiom.

`match %v do | _ -> () end` consumes the scrutinee via the match channel; the wildcard pattern binds nothing, so there is no follow-up obligation.

> **Open bug (`nexus-x5ww`)**: `let_binds_linear` only inspects the *outer* type wrapper. A value whose linearity is *structural* — for example, a record `Handle(fd: %i64)` returned from a function whose declared return type is `Handle` rather than `%Handle` — slips past the predicate, and `let _ = make()` silently discards it. The same hole affects closures whose linearity is induced by capture rather than by an outer `%`.

> **Open bug (`nexus-218q`, array clause)**: `is_auto_droppable` returns `true` for `[σ]` regardless of whether `σ` is linear. Combined with the wildcard hole above, `let _ = make_handles()` returning `[%Handle]` would be silently discarded.

## Lazy Thunks (`@T`)

`@T` is the one shape that is *always* linear regardless of inner type. The only consumption channel that actually evaluates the body is the **force** form `@x`. Stdlib combinators in `nxlib/stdlib/lazy.nx` are surface sugar over force:

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

> **Open bug (`nexus-qhms`)**: [lazy.md](lazy) §Standard Library documents `cancel` as "discard without evaluating" and `race` as "loser is cancelled", but the stdlib implementations of both *force* their arguments (sequential evaluation only). `force_all` is listed in the spec table but does not exist in `nxlib/stdlib/`. Until a parallel runtime with a cooperative-cancel hook ships, the spec must either be rewritten to match the sequential reality or the runtime extended.

## Memory Reclamation

Nexus does **not** garbage-collect, reference-count, or per-value-`free`. Heap memory is allocated from a bump arena and reclaimed in bulk via the `nexus:runtime/arena` host module:

| Intrinsic | Effect |
|---|---|
| `__nx_heap_mark()` | Snapshot the arena's bump pointer (and routed-allocator outstanding count, when wired) |
| `__nx_heap_reset(mark)` | Rewind the bump pointer to `mark`; everything allocated since is gone |
| `__nx_heap_swap(...)` | Switch between primary and routed allocator |

Codegen for these is in `src/backend/codegen.nx:357-423` (`emit_heap_mark` / `emit_heap_reset`). The compiler does not emit per-value cleanup; closures, records, and linear handles all become unreachable wholesale at the next reset.

> **Consequence**: any future destructor-bearing type would need either (a) a new MIR/LIR drop instruction with codegen support, or (b) explicit user-level `dispose(...)` calls protected by linearity. Neither exists today.

## WASM `op_drop` Emissions

The WASM `drop` opcode (`0x1A`) appears in the emitter only as **stack housekeeping**, never as a value-cleanup operation. All current sites:

| Site | Purpose |
|---|---|
| `src/backend/codegen/atom.nx:119` | After packing a `unit` into i64, drop the pre-pack stack slot |
| `src/backend/codegen/atom.nx:141`, `:165` | Field store/load for `unit`-typed record fields — drop the placeholder |
| `src/backend/codegen/atom.nx:205` | Discard `memory.grow` return value (`-1` on failure) |
| `src/backend/codegen.nx:1959` | Let-binder whose declared type is `unit` — drop a non-unit RHS result |
| `src/backend/codegen.nx:2226` | `_start` shim drops the `main` return value when non-unit |

None of these run user-defined cleanup logic. They exist purely to balance the WASM operand stack.

## Closures and Captures

A closure stores its captures as fields of a heap-allocated object (`emit_closure_captures`, `src/backend/codegen.nx:850`). The closure's *linearity* is induced by capture: if the body references any outer linear binding, the resulting closure is itself linear (`collect_captured_linears`, `src/typecheck/linearity.nx:368`).

When a linear closure is consumed, the heap object is **not** freed by codegen; it is reclaimed at the next `__nx_heap_reset`. There is no per-closure destructor, so a closure that captures `%h` does not run any "release" logic on `%h` — the capture itself was the consumption channel for `%h`, performed at closure-creation time.

## Exceptions and Drop

`raise` in Nexus emits WASM `op_throw` (with a `try_table` for catch); it does not run any cleanup landingpads. The static guarantee that "no linear is live across a throwable boundary unless re-consumed in every catch arm" is what keeps the program leak-free; the runtime never gets a chance to "drop" anything on unwind because, by construction, there is nothing to drop.

This shape is structural, not aspirational: adding a destructor type later would require landing-pad codegen that does not currently exist.

## Cross-Reference Summary

| Concern | Authoritative location |
|---|---|
| Set of auto-droppable types | `src/typecheck/linearity.nx:147` |
| Function-end consumption check | `src/typecheck/linearity.nx:670` |
| Throwable-call leak guard | `src/typecheck/linearity.nx:1032` |
| `_` wildcard binder semantics | `src/typecheck/linearity.nx:718` |
| Lazy combinators | `nxlib/stdlib/lazy.nx` |
| Arena intrinsics | `src/backend/codegen.nx:357-423` |
| Spec rules | [semantics.md](semantics), [types.md](types), [type-system-formal.md](type-system-formal) §T-Proj, §T-Seq-Cons |

## Open Bugs Tracked

| ID | Summary |
|---|---|
| `nexus-x5ww` | Wildcard-bind `let _ = e` silently discards structurally-linear values (record/closure carrying linear field) |
| `nexus-qhms` | `std:lazy` `cancel`/`race`/`force_all` diverge from `lazy.md` (cancel forces, race is sequential, force_all is missing) |
| `nexus-218q` | `semantics.md` Auto-drop bullet is incomplete vs. implementation; arrays-of-linears clause may be over-permissive |
| `nexus-8tee` | T-Proj `¬linear(τ)` not enforced — interacts with structural-linearity classification |
