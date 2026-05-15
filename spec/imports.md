---
title: "Imports and Module Resolution"
order: 9
---

{% raw %}

# Imports and Module Resolution

This page specifies the cross-module declaration model that the per-module typing rules in [type-system-formal.md](./type-system-formal) reference under the name `imports.md`. Surface syntax for import statements lives in [syntax.md](./syntax) §Imports; this page covers the **resolution semantics** — module identity, import order, visibility filtering, and the cross-module obligations of the per-rule judgments.

## 1. Modules and Identity

A **module** is a single `.nx` source file. Every declaration lives in exactly one module. We write $M$ for a module and $\text{decls}(M)$ for the declaration sequence inside its source file.

The **defining module** of a declaration $D$ is the unique $M$ such that $D \in \text{decls}(M)$. This identity is referenced by [D-Type-Sum-Opaque](./type-system-formal#D-Type-Sum-Opaque) — the only typing rule whose effect on $\mathcal{T}$ depends on which module is currently being type-checked. All other rules are module-local in the trivial sense (their conclusions apply inside whichever module is being processed; the rule itself does not branch on module identity).

A module's identity is its **canonical absolute path** (after any pkg-resolution mapping per [packaging](../packaging) — beyond the scope of this page). Two import statements in the same file that resolve to the same path refer to the same module; the importing module sees the imported module's exports exactly once regardless of repeated `import` lines.

## 2. Import Statement Forms

The surface forms (from [syntax.md](./syntax) §Imports):

```nexus
import * as math from "path/to/math.nx"                // namespace alias
import { add, sub } from "path/to/math.nx"             // named items
import { add as my_add, sub } from "path/to/math.nx"   // named with renaming
import { add, sub }, * as math from "path/to/math.nx"  // named + namespace
import external "path/to/lib.wasm"                     // raw Wasm module
```

For the formal description below, we treat all four as projections of a single form

$$\textbf{import}~\textit{spec}~\textbf{from}~M' \quad\text{where}~\textit{spec}~\text{selects a subset of}~M'\text{'s exported entries}$$

with $M'$ the imported module. The renaming and namespace-aliasing forms map exported names to the importer's local namespace; the `import external` form binds Wasm-side symbols and is consumed by the codegen — it produces no $\mathcal{T}$ updates beyond what [D-External](./type-system-formal#D-External) would on a per-symbol basis.

## 3. Visibility and Export

The `export` prefix on a declaration is the **inter-module visibility gate**. Inside the defining module $M$, `export` and non-`export` declarations have identical effects on $\mathcal{T}$ (the per-rule conclusions are the same — see [type-system-formal.md](./type-system-formal) §Visibility). The modifier governs which declarations enter the *importing* module's $\mathcal{T}$ when an `import` statement is resolved.

Concretely, when type-checking module $M$ that contains `import { name_1, …, name_k } from M'`:

1. $M'$ is type-checked first (see §4 Resolution Order).
2. After $M'$'s declaration fold, its tables $\mathcal{T}_{M'}$ are projected onto only the exported entries:

$$\mathcal{T}_{M'}^{\text{export}} = \langle \Gamma_{M'} \restriction \overline{\text{exports}},\; \text{typedef}_{M'} \restriction \overline{\text{exports}},\; \text{methods}_{M'} \restriction \overline{\text{exports}},\; \text{variants}_{M'},\; \text{members}_{M'} \restriction \overline{\text{exports}} \rangle$$

   The `variants(Exn)` table is *not* restricted — exception declarations always extend the global $\texttt{Exn}$ sum (see §6).
3. The selected entries (those in `name_1, …, name_k`, with renaming applied) are merged into $M$'s starting $\mathcal{T}$.

The rename map and namespace alias affect only how the imported names appear in $M$'s $\Gamma$ / $\text{typedef}$ / etc.; the underlying scheme, variant set, methods table is unchanged.

## 4. Resolution Order

For any module $M$, the type-checker resolves $M$'s imports **transitively, depth-first, in declaration order**, before running $M$'s own declaration fold. Concretely:

1. For each `import ... from M'` in $M$ (in source order):
   - If $M'$ has not yet been processed: recursively process $M'$ (same algorithm).
   - Project $M'$'s exports per §3 and merge them into $M$'s starting $\mathcal{T}$.
2. After all imports are resolved, run the **two-phase fold** on $M$'s own declarations (see [type-system-formal.md](./type-system-formal) §3): $\vdash_d^{\text{pre}}$ for forward registration, then $\vdash_d$ for body resolution.

The two-phase fold scope is **a single module**: $\vdash_d^{\text{pre}}$ on $M$ does not pre-register $M'$'s declarations a second time (they were already merged in step 1's projection of $\mathcal{T}_{M'}^{\text{export}}$). Mutual recursion across module boundaries is therefore *not* supported through the type-system layer — the importer must already have all imported names resolved before its own fold begins.

### Cycles

A cycle in the import graph (`A` imports `B`, `B` imports `A`) is **rejected at resolution time** as `CircularImport`. Cycle detection is by visiting the in-progress set during recursion in step 1; revisiting a module already on the in-progress stack triggers the rejection. There is no "interface file" mechanism that would allow circular references between modules.

## 5. Two-Phase Fold Scope

The forward-registration judgment $\vdash_d^{\text{pre}}$ ([type-system-formal.md](./type-system-formal) §3) operates **per module**. Within a single module's source file, $\vdash_d^{\text{pre}}$ runs once across all declarations to seed `typedef` placeholders ([D-Type-Forward](./type-system-formal#D-Type-Forward)) and recursive-fn signatures ([D-Let-Forward](./type-system-formal#D-Let-Forward)) before the body-pass $\vdash_d$ runs.

Across module boundaries, the seeding is achieved by §4's import projection — the importer sees imported types and functions at their *resolved* schemes, not at placeholders. So:

- Self-recursion and mutual-recursion **within a module** work via $\vdash_d^{\text{pre}}$.
- Cross-module recursion is **not supported** — it would require a fixed-point across module boundaries, which the cycle-rejection rule of §4 forecloses.

## 6. Exception Extensibility Across Modules

[D-Exception](./type-system-formal#D-Exception) is the only typing rule that mutates a *pre-existing* $\mathcal{T}$ entry: $\text{variants}(\texttt{Exn})$ accumulates every exception constructor declared anywhere in the program. This is the cross-module hazard called out in [T-TryCatch](./type-system-formal#T-TryCatch):

> A closed-enumeration catch over a $\texttt{Exn}$ row becomes inexhaustive when a downstream module adds a new variant.

Concretely: module $A$ declares `exception NotFound`, then writes a `try ... catch | NotFound -> ... end`. The catch is exhaustive at $A$'s typing time. Later, module $B$ imports $A$ and declares `exception PermDenied`; because $\text{variants}(\texttt{Exn})$ is global, $A$'s catch is now no longer exhaustive over the full $\texttt{Exn}$ sum — but the catch site in $A$ was already type-checked and emitted. The static defence is the [hasCatchAll](./type-system-formal#T-TryCatch) requirement: a syntactic wildcard arm is the *only* way to discharge a catch-all sentinel; closed-variant enumeration never satisfies it. T-TryCatch reads the locally-visible $\text{variants}(\texttt{Exn})$ at typing time but the residual-row computation uses the catch-all sentinel for any unenumerated path, so a future-extending module's new variants are absorbed without changing $A$'s emitted code.

## 7. Out-of-Scope Topics

These are intentionally not specified on this page:

- **Compile cache.** Whether module type-check results are persisted across runs is an implementation concern; the spec assumes each run resolves imports freshly. See `src/typecheck/check.nx` for the current cache behaviour.
- **Versioning / API compatibility.** The spec gives no semantic-versioning rules for `export`ed schemes. Adding an `export` is always safe; removing or narrowing the type of an exported entry breaks every importer's type-check (no compatibility shim).
- **Diamond imports.** When two import paths reach the same module $M''$ transitively, $M''$'s tables are merged once (deduplicated by canonical path). The order of merge does not affect the resulting $\mathcal{T}$ because each module's exports are deterministic in its own declarations.
- **Wasm imports** (`import external "..."`). These are runtime-side imports consumed by the codegen; they produce no Nexus-level type information beyond what individual `external` declarations would.

{% endraw %}
