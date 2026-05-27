---
title: "Imports and Module Resolution"
order: 9
---

{% raw %}

# Imports and Module Resolution

This page sets out the cross-module model. The rules in [type-system-formal.md](./type-system-formal) call this page "`imports.md`". Surface syntax lives in [syntax.md](./syntax) §Imports. The scope here is **how imports resolve**. The page covers module identity, order, export, and the cross-module duties of each rule.

## 1. Modules and identity

A **module** is one `.nx` source file. Each decl lives in one module. We write $M$ for a module. We write $\text{decls}(M)$ for the decls in its source file.

The **defining module** of a decl $D$ is the $M$ with $D \in \text{decls}(M)$. Rule [D-Type-Sum-Opaque](./type-system-formal#D-Type-Sum-Opaque) reads this tag. It is the only rule whose effect on $\mathcal{T}$ turns on which module is in play. Every other rule is module-local. Its conclusion fires inside the current module. It does not branch on module tag.

A module's tag is its **canonical absolute path**. Take the path after any pkg-resolve step. ([packaging](../packaging) describes that step, which lives outside this page.) Two `import` lines in one file that resolve to the same path point at the same module. The importer sees its exports once, no matter how often the `import` repeats.

## 2. Import statement forms

The surface forms (from [syntax.md](./syntax) §Imports):

```nexus
import * as math from "path/to/math.nx"                // namespace alias
import { add, sub } from "path/to/math.nx"             // named items
import { add as my_add, sub } from "path/to/math.nx"   // named with renaming
import { add, sub }, * as math from "path/to/math.nx"  // named + namespace
import external "path/to/lib.wasm"                     // raw Wasm module
```

For the rest of this page, take all four as projections of a single form:

$$\textbf{import}~\textit{spec}~\textbf{from}~M' \quad\text{where}~\textit{spec}~\text{selects a subset of}~M'\text{'s exported entries}$$

where $M'$ is the imported module. The renaming and namespace forms map exported names into the importer's local space. The `import external` form binds Wasm-side symbols. Codegen consumes it. The form makes no $\mathcal{T}$ updates beyond what [D-External](./type-system-formal#D-External) would yield per symbol.

## 3. Export gate

The `export` prefix is the **cross-module gate**. Inside the defining module $M$, an `export` decl and a non-`export` decl affect $\mathcal{T}$ in the same way (see [type-system-formal.md](./type-system-formal) §Visibility for matching per-rule conclusions). The gate picks which decls enter the *importer's* $\mathcal{T}$ when an `import` is resolved.

Concretely, when type-checking module $M$ that contains `import { name_1, …, name_k } from M'`:

1. $M'$ is type-checked first (see §4 Resolution Order).
2. After $M'$'s decl fold, project its tables $\mathcal{T}_{M'}$ onto the exported entries only. Let $E_{M'} \equiv \overline{\text{exports}_{M'}}$ name that set; then:

$$\mathcal{T}_{M'}^{\text{export}} = \langle \Gamma_{M'} \restriction E_{M'},\; \mathit{typedef}_{M'} \restriction E_{M'},\; \mathit{methods}_{M'} \restriction E_{M'},\; \mathit{variants}_{M'},\; \mathit{members}_{M'} \restriction E_{M'} \rangle$$

   The `variants(Exn)` table is *not* trimmed. Each `exception` adds to the global $\texttt{Exn}$ sum (see §6).
3. Merge the selected entries into $M$'s starting $\mathcal{T}$. The selected entries are `name_1` through `name_k`, with any renaming applied.

The rename map and namespace alias change only how names appear in $M$. Their targets in $\Gamma$, $\text{typedef}$, and the like are unchanged. Each scheme, variant set, and methods table stays as it is.

## 4. Resolution order

For any module $M$, the checker resolves $M$'s imports first, then runs $M$'s own decl fold. The walk is **transitive, depth-first, in source order**. Concretely:

1. For each `import ... from M'` in $M$ (in source order):
   - When $M'$ is not yet processed, recurse into $M'$ with the same algorithm.
   - Project $M'$'s exports per §3, then merge them into $M$'s starting $\mathcal{T}$.
2. Once every import is resolved, run the **two-phase fold** on $M$'s own decls (see [type-system-formal.md](./type-system-formal) §3). The first phase $\vdash_d^{\text{pre}}$ handles forward registration. The second phase $\vdash_d$ handles body resolution.

The two-phase fold scope is **one module**. $\vdash_d^{\text{pre}}$ on $M$ does not re-register $M'$'s decls. Step 1 merged them through the projection of $\mathcal{T}_{M'}^{\text{export}}$. So the type-system layer rules out mutual recursion across module bounds. Every imported name must be resolved before the importer's own fold begins.

### Cycles

A cycle in the import graph is **rejected at resolve time** as `CircularImport`. (Say `A` imports `B`, and `B` imports `A`.) The check uses an in-progress set during step 1's recursion. If a module is already on the in-progress stack, a revisit fails. There is no "interface file" path; modules cannot reference each other in a cycle.

## 5. Two-phase fold scope

The forward-registration judgment $\vdash_d^{\text{pre}}$ ([type-system-formal.md](./type-system-formal) §3) runs **per module**. In one source file, $\vdash_d^{\text{pre}}$ runs once across every decl. It seeds `typedef` placeholders ([D-Type-Forward](./type-system-formal#D-Type-Forward)) and recursive-fn signatures ([D-Let-Forward](./type-system-formal#D-Let-Forward)). Then the body pass $\vdash_d$ runs.

Across module bounds, §4's import projection seeds the tables. The importer sees imported types and functions at their *resolved* schemes; no placeholder shows up. So:

- Self-recursion and mutual recursion **within a module** work through $\vdash_d^{\text{pre}}$.
- Cross-module recursion is **not supported**. A fixed-point across module bounds would be needed, and the cycle rule of §4 shuts that down.

## 6. Exception extensibility across modules

[D-Exception](./type-system-formal#D-Exception) is the only rule that mutates a *pre-existing* $\mathcal{T}$ entry. The set $\text{variants}(\texttt{Exn})$ grows with each `exception` ctor in the program. So [T-TryCatch](./type-system-formal#T-TryCatch) carries a cross-module hazard:

> A closed-enumeration catch over a $\texttt{Exn}$ row becomes inexhaustive when a downstream module adds a new variant.

Take a concrete case. Module $A$ declares `exception NotFound`. It then writes a `try ... catch | NotFound -> ... end`. At $A$'s typing time, the handler covers every variant in scope.

Later, module $B$ imports $A$ and declares `exception PermDenied`. Since $\text{variants}(\texttt{Exn})$ is global, $A$'s handler no longer covers the full $\texttt{Exn}$ sum. Yet the call site in $A$ was already type-checked and emitted.

The static defence is the [hasCatchAll](./type-system-formal#T-TryCatch) rule. A syntactic wildcard arm is the *only* way to discharge a catch-all sentinel; a closed-variant list never does. T-TryCatch reads the local $\text{variants}(\texttt{Exn})$ at typing time. The residual-row step routes any unenumerated path through the catch-all sentinel. So a downstream module's new variants land in the sentinel, and $A$'s emitted code stays as it was.

## 7. Out-of-scope topics

The items below sit outside this page on purpose:

- **Compile cache.** Whether type-check results persist across runs is an impl point. The spec assumes each run resolves imports from scratch. See `src/typecheck/check.nx` for the current cache shape.
- **Versioning and API compat.** The spec gives no SemVer rules for `export`ed schemes. Adding an `export` is always safe. Removing or narrowing an `export` breaks every importer's type-check; there is no compat shim.
- **Diamond imports.** When two import paths reach the same module $M''$ transitively, $M''$'s tables are merged once. The canonical path is the dedupe key. The merge order does not change the resulting $\mathcal{T}$, since each module's exports come from its own decls in a fixed order.
- **Wasm imports** (`import external "..."`). These are runtime-side imports consumed by codegen. They yield no Nexus-level type info beyond what each `external` decl would.

{% endraw %}
