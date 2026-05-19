---
layout: default
title: Type System — Formal Rules
---

{% raw %}
# Type system — formal rules

This document defines the typing rules of Nexus as inference rules. It serves as a specification for property-based testing and as a reference for future mechanization.

## 1. Syntax

The abstract syntax of the core calculus. See [Syntax](../syntax) for the full surface syntax.

### Terms

<div markdown="0">
$$\begin{array}{rcll}
\mu & ::= & \varepsilon \mid \% \mid \mathord{\sim} \mid @ \mid \& & \text{modality (plain / linear / ref / lazy / borrow)} \\[6pt]
e & ::= & \mu\,x \mid c & \text{variable with modality / constructor} \\
  & \mid & n \mid f \mid ch \mid b \mid s \mid () & \text{literals (int, float, char, bool, string, unit)} \\
  & \mid & e_1 \oplus e_2 & \text{binary operation} \\
  & \mid & f(\overline{\ell : e}) & \text{application} \\
  & \mid & \textbf{fn}~(\overline{\ell : \tau}) \to \tau;\,\rho;\,\rho~\textbf{do}~\overline{s}~\textbf{end} & \text{lambda} \\
  & \mid & \textbf{if}~e~\textbf{then}~\overline{s}~\textbf{else}~\overline{s} & \text{conditional} \\
  & \mid & \textbf{match}~e~\lbrace \overline{p \to s} \rbrace & \text{pattern match} \\
  & \mid & \lbrace \overline{\ell : e} \rbrace & \text{record} \\
  & \mid & e.\ell & \text{projection} \\
  & \mid & \textbf{throw}~e & \text{throw exception} \\
  & \mid & \textbf{handler}~x~[\textbf{require}~\rho]~\textbf{do}~\overline{\ell = e}~\textbf{end} & \text{handler (each } e \text{ is a lambda)} \\[6pt]
s & ::= & \textbf{let}~\mu\,x = e & \text{binding} \\
  & \mid & \textbf{let}~p = e & \text{destructuring} \\
  & \mid & \textbf{return}~e & \text{return} \\
  & \mid & \mathord{\sim}x \leftarrow e & \text{assignment} \\
  & \mid & \textbf{inject}~\overline{h}~\textbf{do}~\overline{s}~\textbf{end} & \text{capability injection} \\
  & \mid & \textbf{try}~\overline{s}~\textbf{catch}~\overline{p \to s}~\textbf{end} & \text{exception handling} \\
  & \mid & \textbf{while}~e~\textbf{do}~\overline{s}~\textbf{end} & \text{while loop} \\
  & \mid & e & \text{expression statement} \\[6pt]
p & ::= & \mu\,x & \text{variable pattern, } \mu \in \lbrace \varepsilon, \%, \mathord{\sim}, \& \rbrace \text{ (} x \notin \text{dom}(\Gamma)~\text{or}~\Gamma(x)~\text{is not a constructor scheme)} \\
  & \mid & \_ \mid n & \text{wildcard / literal pattern} \\
  & \mid & \mu\,c & \text{nullary constructor pattern, } \mu \in \lbrace \varepsilon, \%, \& \rbrace \text{ (} c \in \text{dom}(\Gamma),~\text{arity 0)} \\
  & \mid & \mu\,c(\overline{\ell : p}) & \text{constructor pattern, } \mu \in \lbrace \varepsilon, \%, \& \rbrace \text{ (} c \in \text{dom}(\Gamma),~\text{arity} \geq 1 \text{)} \\
  & \mid & \lbrace \overline{\ell : p} \rbrace & \text{record pattern} \\
  & \mid & p_1 \mathbin{\vert} p_2 & \text{or-pattern (alternation)}
\end{array}$$
</div>

Bare identifiers in pattern position are disambiguated **by Γ-lookup**: if the identifier resolves to a constructor scheme in Γ, it parses as a nullary constructor pattern (via [P-CtorNullary](#P-CtorNullary)); otherwise it parses as a variable binder (via [P-Var](#P-Var)). The split mirrors the surface convention "zero-field exceptions omit parentheses both at declaration and at match" (see [Exception Groups](../exception-groups)) and matches `src/typecheck/exhaustive.nx`'s pattern dispatch, which checks `variants` before treating a bare identifier as a binder.

The core calculus omits several surface language features that are either desugared or handled as environment preconditions:

- **Constructors** ($c$) — assumed predefined in Γ with a function type (n-ary) or a value type (nullary). Application $f(\overline{\ell : e})$ covers both function calls and constructor application. In patterns, $c$ is syntactically distinguished from variable patterns $x$.
- **Cap declarations** — top-level declarations that populate Γ with method signatures. Not terms; they are preconditions on Γ.
- **Exception / exception group declarations** — extend the `Exn` sum type in Γ. Same status as cap declarations.
- **For loops** — present in the surface syntax but desugared to a **while** with an explicit index counter and bound; the formal rule covers only **while** (see [T-While](#T-While)).
- **Import statements** — resolved before type checking; not modeled here.
- **List literals and the $\mathord{::}$ cons operator** — desugared to the prelude `List` enum: $[\,]$ becomes `Nil`, $e_h :: e_t$ becomes $\texttt{Cons}(v: e_h,\, \text{rest}: e_t)$, $[e_1, \ldots, e_n]$ becomes a right-associated chain of `Cons` ending in `Nil`. The list type $[\tau]$ is an alias for $\texttt{List}\langle\tau\rangle$. List patterns desugar identically. Typing and exhaustiveness are then handled by [T-App](#T-App) (constructor application), [P-Ctor](#P-Ctor), and [Exh-Sum](#Exh-Sum) — no list-specific rules are needed.
- **Array values** — the linear type $[\lvert\tau\rvert]$ has no in-core introduction or elimination rule. Construction, indexing, length, mutation, and iteration go through stdlib intrinsic functions (e.g. $\texttt{array\_init} : (n: \texttt{i64}, v: \tau) \to [\lvert\tau\rvert]$, $\texttt{array\_get} : (a: \&[\lvert\tau\rvert], i: \texttt{i64}) \to \tau$) that are populated into Γ as preconditions. The type system observes only their declared signatures via [T-App](#T-App). Array exhaustiveness in [match](#T-Match) is handled by allowing only wildcard-like patterns (a value-level constructor for arrays is not exposed).

### Types

<div markdown="0">
$$\begin{array}{rcll}
\tau & ::= & b \mid \texttt{intlit} \mid \texttt{floatlit} & \text{base type / inference-internal numeric} \\
    & \mid & \alpha \mid {?}\alpha & \text{type variable / unification variable} \\
    & \mid & (\overline{\ell : \tau}) \to \tau;\, \rho;\, \rho & \text{function (params, return, capability, effect)} \\
    & \mid & \lbrace \overline{\ell : \tau} \rbrace & \text{record} \\
    & \mid & x\langle \overline{\tau} \rangle & \text{named type (e.g.\ } \texttt{Option}\langle\texttt{i64}\rangle\text{)} \\
    & \mid & [\tau] \mid [\lvert\,\tau\,\rvert] & \text{list / array (array is always linear)} \\
    & \mid & \%\tau \mid \mathord{\sim}\tau \mid \&\tau \mid @\tau & \text{linear / mutable ref / borrow / lazy} \\
    & \mid & \textbf{handler}\;x\;\rho & \text{handler for cap } x \\[6pt]
b & ::= & \texttt{i32} \mid \texttt{i64} \mid \texttt{f32} \mid \texttt{f64} \mid {} & \\
  &     & \texttt{bool} \mid \texttt{char} \mid \texttt{string} \mid \texttt{unit} & \\[2pt]
  & \multicolumn{3}{l}{\text{Surface-level alias: }\texttt{float} \equiv \texttt{f64}~\text{(resolved at parse-time before any rule fires)}} & \\[6pt]
\eta & ::= & X \mid \texttt{Exn} & \text{row entry (an identifier or the catch-all sentinel)} \\[6pt]
\rho & ::= & \lbrace \overline{\eta} \rbrace \mid \lbrace \overline{\eta} \mid {?}r \rbrace & \text{row (closed / open with row variable } {?}r\text{)}
\end{array}$$
</div>

We write $\overline{X}$ for a finite sequence $X_1, \ldots, X_n$. $\alpha, \beta, \gamma$ range over type variables; ${?}\alpha$ denotes a type unification variable introduced during inference (the distinction matters in generalization). $r, s$ range over **row variables** (the tail position of an open row $\lbrace \overline{\tau} \mid r \rbrace$); ${?}r$ denotes a row unification variable. $\lvert\overline{X}\rvert$ denotes the length of a sequence.

The statement judgment $\Gamma;\,\rho_q;\,\tau_r \vdash_s s : \Gamma' \mathbin{!} \rho_e$ uses an **extended return-context** $\tau_r \in \tau \cup \lbrace \bot \rbrace$. The sentinel $\bot$ marks "no enclosing function": it appears only at top-level statement contexts ([D-Let-Top](#D-Let-Top), [D-LetPat-Top](#D-LetPat-Top)) where there is no function to return to. $\bot$ is *not* a type — it is not a member of τ in the grammar above and never appears in Γ, in row entries, or as the result of [inst](#inst). The only rule that inspects $\tau_r$ is [T-Return](#T-Return), which carries the side condition $\tau_r \neq \bot$ to reject **return** statements at module scope.

`intlit` and `floatlit` are **kind-restricted grammar symbols** assigned to integer and float literals before their concrete type is known. They are the same metavariable at every literal occurrence (no per-occurrence freshening), but resolution against a concrete type is **local** to each unification site — the typing context never broadcasts an $\texttt{intlit} := \tau$ refinement across occurrences. Resolution proceeds two ways: (1) at a unification site, [U-IntLit](#U-IntLit) / [U-FloatLit](#U-FloatLit) admits `intlit` against any $\tau \in \text{kind}(\texttt{intlit})$ with the *empty* substitution, treating that occurrence as τ for the rest of the derivation; (2) if a literal still types at `intlit` when it reaches a [T-Let](#T-Let) binding site, `default` pins it to `i64` (`f64` for `floatlit`). The independent-occurrence behaviour is **necessary** for compositionality: `let x: i32 = 1; let y: i64 = 2` is well-typed precisely because resolving the first literal at `i32` does not rewrite the second's `intlit` to `i32` before it meets `i64`. The $\text{kind}(\cdot)$ of `intlit` is $\lbrace \texttt{i32}, \texttt{i64} \rbrace$ and of `floatlit` is $\lbrace \texttt{f32}, \texttt{f64} \rbrace$ — unification with any other type fails.

**Literal range.** Integer literals lex as *unsigned* digit strings; the surface form `-n` parses as unary-minus applied to `n`. Lexed digit strings must fit `i64::MAX` ($2^{63}-1 = 9223372036854775807$). Writing `-9223372036854775808` (i.e. `i64::MIN`) therefore fails — the unsigned digits exceed `i64::MAX` by one and lex as `integer literal out of range`. Workaround in expression position: `let min_i64: i64 = -9223372036854775807 - 1`, where the subtraction underflows by design. Pattern position inherits the same constraint and must use a const binding instead of the bare literal.

### Modalities

The modality μ determines how a binding is introduced and used. ε (plain) is elided in notation; we write $x$ for $\varepsilon\,x$. The modalities $\%$, $\mathord{\sim}$, $\&$, $@$ correspond to the surface sigils `%x`, `~x`, `&x`, `@x`. A binding with type $\%\tau$, $@\tau$, or $[\lvert\,\tau\,\rvert]$ has usage $q = 1$ (linear); all others have $q = \omega$. $@\tau$ denotes a suspended computation (one-shot thunk). $\mathord{\sim}\tau$ is a mutable reference cell. $\&\tau$ is a read-only borrow.

In expression position, $\mu\,x$ with $\mu \in \{\varepsilon, \%, \mathord{\sim}\}$ is a variable reference. $@e$ (force) and $\&x$ (borrow) subsume the $\mu = @$ and $\mu = \&$ cases and are listed as separate expression forms since force applies to any expression.

### Row Types

The row type ρ is used for both the effect position ($\rho_e$, in **throws**) and the capability position ($\rho_q$, in **require**) of function types. Both positions share the same structure — row extension, unification, row variable instantiation — so no separate syntactic category is needed. The distinction is semantic: $\rho_e$ ranges over exception types, $\rho_q$ ranges over a **mixed alphabet** of system capabilities and user-declared cap names (defined immediately below). No kind system enforces the row-position invariant; it is maintained by the introduction rules (T-Throw adds to $\rho_e$; [T-Inject](#T-Inject) and cap declarations add to $\rho_q$).

In the current language, the only effect is checked exceptions. $\rho_e$ is a row of **exception-constructor names**: each user `exception C(...)` declaration extends the global `Exn` sum with constructor $C$ and simultaneously introduces $C$ as a row-entry symbol usable in **throws** rows. So $\rho_e$ may be $\lbrace\rbrace$ (pure), a closed set of specific variants $\lbrace C_1, \ldots, C_n \rbrace$, an open variant row $\lbrace C_1, \ldots, C_n \mid {?}r \rbrace$, or contain the catch-all sentinel `Exn` (see below).

`Exn` itself is the **top of the exception lattice** — the type assigned to a binding that captures *any* exception (e.g. $\textbf{catch}~e \to \ldots$ binds $e : \texttt{Exn}$). `Exn` surfaces as a row entry only when re-throwing such a catch-all binding: $\textbf{throw}~e$ for $e : \texttt{Exn}$ emits $\lbrace \texttt{Exn} \rbrace$, indicating "may throw any variant". Specific-variant rows $\lbrace C_i \rbrace$ are subsumed by $\lbrace \texttt{Exn} \rbrace$ via [U-Row-Exn](#U-Row-Exn) below; otherwise rows unify by entry equality (no implicit subtyping).

Exception groups (`exception group G = C_1 | C_2 | \ldots`, see [Exception Groups](../exception-groups)) are syntactic shortcuts: anywhere $G$ appears in a row position or a catch-arm pattern, it expands to its declared member set $\lbrace C_1, C_2, \ldots \rbrace$ at parse time. The formal rules never observe groups directly — only their expansions.

The capability row $\rho_q$ admits two disjoint sources of entries:

1. **System capabilities** — the closed set $\lbrace \texttt{PermFs}, \texttt{PermNet}, \texttt{PermConsole}, \texttt{PermRandom}, \texttt{PermClock}, \texttt{PermProc}, \texttt{PermEnv} \rbrace$ — corresponding to WASI interface grants at runtime. See [WASM and WASI](../../env/wasm) for the complete mapping.
2. **User-declared cap names** — each $\textbf{cap}\;X\;\textbf{do}\;\ldots\;\textbf{end}$ introduces $X$ as a row-entry symbol usable in **require** rows. [T-Inject](#T-Inject) extends $\rho_q$ with $X$ when an $X$-implementing handler is injected; [T-CapCall](#T-CapCall) reads $x \in \rho_q$ off this row to authorize the call.

These two sources share the row vocabulary because $\rho_q$ unification, weakening, and `require` checking treat both kinds of entries uniformly. The disjointness is by declaration site: system-capability names are reserved (parser rejects redeclaration); cap names are user-defined and live in the same namespace as type/term identifiers.

**Reserved names.** `Exn` is reserved across both row positions: it must never appear as a user-declared cap name or as an exception-constructor name, and the freshness premises on [D-Cap](#D-Cap) and [D-Exception](#D-Exception) enforce this at the declaration boundary. The reservation is what keeps [U-Row-Exn](#U-Row-Exn)'s throws-position activation premise ($\texttt{Exn} \in \overline{\tau}$) by-construction unreachable on $\rho_q$ — without it, `cap Exn do … end` would let `Exn` legally enter a require row and U-Row-Exn would mis-fire on a non-throws context. The same reservation applies to `SysCaps` names (`PermFs`, …) by the existing reserved-name handling: redeclaration as a cap, exception, type, or term identifier is rejected.

Let $\texttt{SysCaps} = \lbrace \texttt{PermFs}, \texttt{PermNet}, \texttt{PermConsole}, \texttt{PermRandom}, \texttt{PermClock}, \texttt{PermProc}, \texttt{PermEnv} \rbrace$. The well-formedness predicate

<div markdown="0">
$$\text{wfCap}(\rho_q) \;\Longleftrightarrow\; \forall X \in \overline{\eta}.\;X \in \texttt{SysCaps} \cup \text{dom}(\text{methods}) \quad\text{where}~\rho_q = \lbrace \overline{\eta} \rbrace~\text{or}~\lbrace \overline{\eta} \mid {?}r \rbrace$$
</div>

requires every named entry of a capability row to be either a system capability or a cap previously declared by [D-Cap](#D-Cap) (which populates `methods`). Row tail variables ${?}r$ are unconstrained — they stand for "any further entries" and are pinned by unification against a closed-row context, where the pinned content is itself well-formed by transitivity.

`wfCap` is checked at every **introduction site** of a $\rho_q$ row: the require clause on a **fn** arrow ([T-Lambda](#T-Lambda)), the optional require annotation on a **handler** ([T-Handler](#T-Handler)), and the per-method declared require row inside [D-Cap](#D-Cap). Use sites ([T-App](#T-App), [T-CapCall](#T-CapCall), [T-Inject](#T-Inject)) operate on already-well-formed rows and need not re-check. Without `wfCap` at the introduction sites, a typo such as `require { Logr }` (intended `Logger`) would propagate as an uninhabitable row entry and surface only at a use site that happens to look it up — moving the diagnostic far from the source of the typo.

**Inline handler expressions.** When a handler appears as an *expression* (rather than a top-level `let h = handler ...` binding), its optional `require` annotation is restricted to `SysCaps` only — user-declared cap names (entries of $\text{dom}(\text{methods})$) may not appear in the require row of an inline handler expression. Formally, the `wfCap` check at an inline-handler site uses the tightened predicate:

<div markdown="0">
$$\text{wfCap}_\text{inline}(\rho_q) \;\Longleftrightarrow\; \forall X \in \overline{\eta}.\;X \in \texttt{SysCaps}$$
</div>

This is strictly stronger than the general `wfCap` — it disallows user-declared cap names in the require row of an inline handler. The restriction is by design: an inline handler expression has no enclosing cap declaration context (it is not bound at a top-level `let` site where the surrounding `cap X do ... end` declarations would be visible and injected), so naming a user cap in its require row would be an uninhabitable constraint with no injection mechanism to satisfy it. Implementation: `src/typecheck/infer.nx` passes `ports: []` to `tcwf.wf_cap` for inline handler expressions, whereas top-level handler bindings in `src/typecheck/check.nx::check_handler_arm_throw_rows` also pass `caps: []` for per-arm require rows (arm-level require declarations are not yet surface-syntactically supported).

**Notation note.** Earlier sections (and most rules below) write row entries as $\overline{\tau}$ rather than the precise $\overline{\eta}$. The two conventions are interchangeable: η is the metavariable for "row entry" (an identifier or the `Exn` sentinel), and the τ notation is a legacy from when rows were typed at the outer-syntactic level. Wherever a row appears, the entries are semantically constrained to be identifiers; type-grammar productions like $\%\sigma$ or $(\overline{\ell:\tau}) \to \tau_r$ never appear as row entries and are rejected by the parser. The wf-checks above pin this constraint formally.

$\rho_e$ (throws row) carries an analogous well-formedness condition: every named entry must be a constructor of `Exn` — i.e.\ in $\text{variants}(\texttt{Exn})$ — or the catch-all sentinel `Exn` itself. We write this as $\text{wfThrow}(\rho_e)$ and rely on the same introduction-site discipline (every **throws** annotation passes through one of the introduction rules).

### Row Set Operations

The typing rules use three set-like operations on rows: subset ($\subseteq$), entry-name set difference ($\setminus$), and membership ($\in$). Each is defined uniformly over closed and open rows. Where a row tail variable ${?}r$ appears, the operation is interpreted *up to row unification*: it holds iff there is a substitution of the unification tails that makes the closed-row equation hold, and that substitution is committed as a side-effect (the same convention as elsewhere in §Unification).

**Subset** ($\rho_1 \subseteq \rho_2$).

<div markdown="0">
$$\begin{array}{rcl}
\lbrace \overline{\tau_1} \rbrace \subseteq \lbrace \overline{\tau_2} \rbrace & \Longleftrightarrow & \overline{\tau_1} \subseteq \overline{\tau_2}~\text{(multiset inclusion)} \\
\lbrace \overline{\tau_1} \rbrace \subseteq \lbrace \overline{\tau_2} \mid {?}r \rbrace & \Longleftrightarrow & \exists \overline{\tau'}.\;{?}r \mathrel{:=} \overline{\tau'},\;\overline{\tau_1} \subseteq \overline{\tau_2} \cup \overline{\tau'} \\
\lbrace \overline{\tau_1} \mid {?}r \rbrace \subseteq \lbrace \overline{\tau_2} \rbrace & \Longleftrightarrow & {?}r \mathrel{:=} \lbrace\rbrace,\;\overline{\tau_1} \subseteq \overline{\tau_2} \\
\lbrace \overline{\tau_1} \mid {?}r_1 \rbrace \subseteq \lbrace \overline{\tau_2} \mid {?}r_2 \rbrace & \Longleftrightarrow & \overline{\tau_1} \subseteq \overline{\tau_2} \cup \overline{\tau'},\;{?}r_1 \mathrel{:=} \lbrace \overline{\tau''} \mid {?}r_2 \rbrace
\end{array}$$
</div>

The open-on-the-right cases refine ${?}r$ to absorb the entries missing on its side; the open-on-the-left cases pin ${?}r_1$ so that its (yet unknown) entries can only come from what the right side already provides (closed) or from ${?}r_2$ (open). Concretely: at the call to [T-Inject](#T-Inject), $\rho_i \subseteq \rho_q$ with $\rho_i = \lbrace \texttt{Logger} \mid {?}r_1 \rbrace$ and $\rho_q = \lbrace \texttt{Logger}, \texttt{Fs} \rbrace$ refines ${?}r_1 \mathrel{:=} \lbrace\rbrace$ — the handler's row-poly tail collapses because the ambient row is closed.

**Set difference** ($\rho \setminus S$ where $S$ is a name set). This is a syntactic transformation; it does not constrain unification variables. The tail (if any) is preserved verbatim:

<div markdown="0">
$$\rho \setminus S = \begin{cases}
\lbrace \overline{\tau} \setminus S \rbrace & \text{if}~\rho = \lbrace \overline{\tau} \rbrace \\
\lbrace (\overline{\tau} \setminus S) \mid {?}r \rbrace & \text{if}~\rho = \lbrace \overline{\tau} \mid {?}r \rbrace
\end{cases}$$
</div>

Reading: a catch arm subtracts caught-variant names from the *known* part of the try-body's throws row; whatever the tail ${?}r$ stands for (variants the body could throw that the typer hasn't pinned yet) is forwarded unchanged into the residual. [T-TryCatch](#T-TryCatch)'s $\rho_\text{residual}$ uses exactly this operation; the catch-all carve-out additionally subtracts `Exn`.

**Membership** ($x \in \rho$).

<div markdown="0">
$$\begin{array}{rcl}
x \in \lbrace \overline{\tau} \rbrace & \Longleftrightarrow & x \in \overline{\tau}~\text{(set membership)} \\
x \in \lbrace \overline{\tau} \mid {?}r \rbrace & \Longleftrightarrow & x \in \overline{\tau} \quad\text{or}\quad {?}r \mathrel{:=} \lbrace x \mid {?}r' \rbrace~(\text{fresh}~{?}r')
\end{array}$$
</div>

The open-row branch may pin ${?}r$ to expose the missing entry; this matches the way [T-CapCall](#T-CapCall)'s $x \in \rho_q$ premise admits a call whose cap is not yet visible in the ambient row but can be introduced by refining the row tail.

These three definitions all reduce to row unification at base; their separate names exist only because the typing rules read more naturally when "is in / is contained / minus" appear instead of bare `unify`.

---

## 2. Typing Rules

### Environment and Usage

<div markdown="0">
$$S ::= \forall \overline{\alpha}.\,\tau \qquad q \in \lbrace 1, \omega \rbrace \qquad \Gamma ::= \lbrace\; \overline{x :^{q} S} \;\rbrace$$
</div>

$S$ is a type scheme. Each binding in Γ carries a **usage** annotation $q$: $1$ (must be used exactly once) or ω (may be used any number of times). The sigils $\%$ and $@$ introduce bindings with $q = 1$; all others have $q = \omega$.

The split operation $\Gamma_1 \otimes \Gamma_2 = \Gamma$ distributes bindings to sub-derivations. For each $x :^{q} S \in \Gamma$, the split assigns $x :^{q_1} S \in \Gamma_1$ and $x :^{q_2} S \in \Gamma_2$ according to:

<div markdown="0">
$$\begin{array}{c|ccc}
q_1 + q_2 = q & q_2 = \cdot & q_2 = 1 & q_2 = \omega \\
\hline
q_1 = \cdot & \cdot & 1 & \omega \\
q_1 = 1 & 1 & — & — \\
q_1 = \omega & \omega & — & \omega
\end{array}$$
</div>

$\cdot$ means the binding is absent from that side of the split. A linear binding ($q = 1$) splits as $(1, \cdot)$ or $(\cdot, 1)$ — the choice of which side receives it is arbitrary (determined by the derivation). An unrestricted binding ($q = \omega$) splits as $(\omega, \omega)$ — both sides share it. "$—$" is forbidden ($1 + 1$ would use a linear resource twice).

Γ is a **finite partial map** from binder names to $(q, S)$ pairs. There is at most one entry per name; shadowing within a single Γ does not occur because env extension by comma overwrites a same-name binding (the inner binder hides the outer at the term-syntax level; the sequence-level `fv` already strips shadowed names from a tail's free set, see §Free Variables). The following operations are defined on Γ and used throughout the typing rules:

<div markdown="0">
$$\begin{array}{rcl}
\text{dom}(\Gamma) & = & \lbrace x \mid (x :^q S) \in \Gamma \rbrace \quad\text{(a name set)} \\[2pt]
\Gamma(x) & = & \text{the unique } (q, S)~\text{such that}~(x :^q S) \in \Gamma; \text{ undefined if}~x \notin \text{dom}(\Gamma) \\[2pt]
\Gamma \setminus \lbrace x \rbrace & = & \lbrace y :^q S \in \Gamma \mid y \neq x \rbrace \\[2pt]
\Gamma_1 \setminus \Gamma_2 & = & \lbrace x :^q S \in \Gamma_1 \mid x \notin \text{dom}(\Gamma_2) \rbrace \\[2pt]
\Gamma_1 \uplus \Gamma_2 & = & \begin{cases} \Gamma_1 \cup \Gamma_2 & \text{if}~\text{dom}(\Gamma_1) \cap \text{dom}(\Gamma_2) = \emptyset \\ \text{undefined} & \text{otherwise} \end{cases} \\[2pt]
\Gamma,\, x :^q S & = & (\Gamma \setminus \lbrace x \rbrace) \cup \lbrace x :^q S \rbrace \quad\text{(comma is overwriting extension)}
\end{array}$$
</div>

Two readings follow from these definitions:

- **$\Gamma_i \setminus \Gamma$ in the pattern rules** ([P-Ctor](#P-Ctor), [P-Record](#P-Record), [P-Or](#pattern-matching)) reads as "the bindings $\Gamma_i$ introduced beyond Γ". Since each $\Gamma_i$ extends the same input Γ with a few new pattern binders, $\Gamma_i \setminus \Gamma$ is exactly the new-binding contribution of one sub-pattern; $\biguplus_i (\Gamma_i \setminus \Gamma)$ then asserts the new binders are mutually disjoint across sub-patterns.
- **$\otimes$-split is non-deterministic.** The table relates $(q_1, q_2)$ to $q$ pointwise; multiple satisfying choices exist when $q = 1$ (either $(1, \cdot)$ or $(\cdot, 1)$). The spec rule is satisfied if *any* choice makes both sub-derivations type-check. The implementation makes a single deterministic pick (`src/typecheck/infer.nx`'s left-then-right scan); soundness does not depend on which.

#### Linear consumption and the env residual $\Gamma \setminus\!\!\setminus e$

The expression judgment $\Gamma;\,\rho_q \vdash_e e : \tau \mathbin{!} \rho_0$ has no explicit output environment, but consumption of linear bindings *is* operational — it is realised by the $\otimes$-split mechanism at every multi-premise rule.

**Operational role of $\otimes$-split.** Every expression rule that has multiple expression premises ([T-App](#T-App), [T-Inject](#T-Inject)'s argument typing, etc.) opens with $\Gamma = \Gamma_1 \otimes \ldots \otimes \Gamma_k$ — a partition of Γ into $k$ sub-environments, one per sub-derivation. Each $\Gamma_i$ is then *fully* the responsibility of its sub-derivation: linear bindings in $\Gamma_i$ must be consumed by some leaf inside that sub-derivation, ω bindings may be referenced any number of times. At an expression *leaf*:

- [T-Var](#T-Var) consumes the binding it references: if $x :^1 S \in \Gamma$, the leaf's Γ is exactly the singleton (or the singleton plus ω entries the unifier may need); the linear $x$ disappears from the rest of the derivation because no other partition received it.
- [T-Const](#T-Const) and other no-variable leaves carry the side condition $\text{pure}(\Gamma)$ — the leaf's local Γ may not contain *any* live linear (every linear must have already been routed away by a $\otimes$-split, otherwise the leaf would consume nothing while a linear sits unconsumed).

We write

<div markdown="0">
$$\Gamma \setminus\!\!\setminus e \;=\; \lbrace x :^q S \in \Gamma \mid q = \omega \;\vee\; x \notin \text{linConsumed}(e\text{'s derivation}) \rbrace$$
</div>

for the **residual** of Γ after typing $e$, where $\text{linConsumed}(e\text{'s derivation})$ is the union of linear bindings drawn into [T-Var](#T-Var) leaves anywhere in the derivation tree of $e$. Equivalently: `linConsumed` is the set of linear $x \in \text{dom}(\Gamma)$ that the $\otimes$-splits of $e$'s derivation routed into a consuming leaf rather than the residual partition. The residual is well-defined *per derivation* (different $\otimes$-split choices yield different residuals; soundness holds for every choice that lets the derivation type-check).

**Syntactic computation of `linConsumed`.** Given Γ, we can also compute $\text{linConsumed}(e, \Gamma)$ structurally on the syntax of $e$ — this is the algorithm the implementation runs and is equivalent to the metatheoretic "T-Var leaves of the derivation" reading whenever a derivation exists. Sub-expression results combine by **disjoint union** $\uplus$, which is undefined when two sub-expressions consume the same linear binding (matching the $\otimes$-split's "$1 + 1 = -$" forbid clause):

<div markdown="0">
$$\begin{array}{rcl}
\text{linConsumed}(\mu\,x, \Gamma) & = & \begin{cases} \lbrace x \rbrace & \text{if}~\Gamma(x) = (1, S)~\text{and}~\mu \in \lbrace \varepsilon, \%, \mathord{\sim} \rbrace \\ \emptyset & \text{otherwise} \end{cases} \\[8pt]
\text{linConsumed}(\&x, \Gamma) & = & \emptyset \quad\text{(borrow does not consume)} \\[2pt]
\text{linConsumed}(c, \Gamma) = \text{linConsumed}(n, \Gamma) = \text{linConsumed}((), \Gamma) & = & \emptyset \\[2pt]
\text{linConsumed}(@e, \Gamma) = \text{linConsumed}(e.\ell, \Gamma) & = & \text{linConsumed}(e, \Gamma) \\[2pt]
\text{linConsumed}(e_1 \oplus e_2, \Gamma) & = & \text{linConsumed}(e_1, \Gamma) \uplus \text{linConsumed}(e_2, \Gamma) \\[2pt]
\text{linConsumed}(f(\overline{\ell : e}), \Gamma) & = & \text{linConsumed}(f, \Gamma) \;\uplus\; \biguplus_i \text{linConsumed}(e_i, \Gamma) \\[2pt]
\text{linConsumed}(\lbrace \overline{\ell : e} \rbrace, \Gamma) & = & \biguplus_i \text{linConsumed}(e_i, \Gamma) \\[2pt]
\text{linConsumed}(\textbf{throw}~e, \Gamma) & = & \text{linConsumed}(e, \Gamma) \\[6pt]
\text{linConsumed}(\textbf{fn}~(\ldots)~\textbf{do}~\overline{s}~\textbf{end}, \Gamma) & = & \lbrace x \in \text{fv}(\overline{s}) \cap \text{dom}(\Gamma) \mid \Gamma(x) = (1, S) \rbrace \\
& & \text{(captured linears are consumed by the closure)} \\[2pt]
\text{linConsumed}(\textbf{handler}~x~[\textbf{require}~\rho]~\textbf{do}~\overline{\ell_j = e_j}~\textbf{end}, \Gamma) & = & \lbrace y \in \textstyle\bigcup_j \text{fv}(e_j) \cap \text{dom}(\Gamma) \mid \Gamma(y) = (1, S) \rbrace \\
& & \text{(captured linears across all arms are consumed by the handler value)} \\[6pt]
\text{linConsumed}(\textbf{if}~e_c~\textbf{then}~\overline{s_1}~\textbf{else}~\overline{s_2}, \Gamma) & = & \text{linConsumed}(e_c, \Gamma) \;\uplus\; L_\text{if} \\
& & \text{where}~\Gamma' = \Gamma \setminus\!\!\setminus e_c,~\text{and}~L_\text{if}~\text{is selected by divergence:} \\
& & L_\text{if} = \begin{cases} \emptyset & \text{if}~\text{tail}(\overline{s_1}) = \bot \wedge \text{tail}(\overline{s_2}) = \bot \\ \text{linConsumed}(\overline{s_2}, \Gamma') & \text{if}~\text{tail}(\overline{s_1}) = \bot \wedge \text{tail}(\overline{s_2}) \neq \bot \\ \text{linConsumed}(\overline{s_1}, \Gamma') & \text{if}~\text{tail}(\overline{s_2}) = \bot \wedge \text{tail}(\overline{s_1}) \neq \bot \\ \text{linConsumed}(\overline{s_1}, \Gamma') & \text{otherwise (both non-}\bot\text{)} \end{cases} \\
& & \text{requires (both non-}\bot\text{):}~\text{linConsumed}(\overline{s_1}, \Gamma') = \text{linConsumed}(\overline{s_2}, \Gamma') \\
\text{linConsumed}(\textbf{match}~e~\lbrace \overline{p_i \to s_i} \rbrace, \Gamma) & = & \text{linConsumed}(e, \Gamma) \;\uplus\; L_\text{match} \\
& & \text{where}~L_\text{match} = \begin{cases} \emptyset & \text{if}~\forall i.\;\text{tail}(\overline{s_i}) = \bot \\ \text{linConsumed}(\overline{s_k}, \Gamma_k) \setminus \text{bv}(p_k) & \text{otherwise, where}~k~\text{is any}~i~\text{with}~\text{tail}(\overline{s_i}) \neq \bot \end{cases} \\
& & \text{requires (non-}\bot\text{arms only):} \\
& & \quad \forall i, j~\text{with}~\text{tail}(\overline{s_i}) \neq \bot \wedge \text{tail}(\overline{s_j}) \neq \bot.\; (\text{linConsumed}(\overline{s_i}, \Gamma_i) \setminus \text{bv}(p_i)) = (\text{linConsumed}(\overline{s_j}, \Gamma_j) \setminus \text{bv}(p_j)) \\
& & \text{requires}~\forall i.\;\forall y :^1 S \in \Gamma_i \setminus \Gamma.\;y \in \text{linConsumed}(\overline{s_i}, \Gamma_i) \\
& & \text{(pattern-introduced linear binders consumed within their arm — every arm, divergent or not)}
\end{array}$$
</div>

Branch constructs require **arm equality** of the linear-consumption sets *among non-divergent arms only*, projected onto the outer environment. Divergent arms (those with $\text{tail} = \bot$) are excluded from the equality requirement because their control flow never reaches the branch's joinpoint — whichever consumption they made is observably irrelevant to the residual computation. Concretely, an `if cond then consume(%a); return () else throw X end` is well-typed under this rule: the `else` arm diverges, so the equality `linConsumed(then) = linConsumed(else)` does not have to hold; $L_\text{if}$ takes the surviving non-divergent arm's consumption (`{a}` from the `then` arm). This carve-out mirrors the corresponding divergent-arm exclusion already present in T-If's / T-Match's $\text{tail}(\overline{s_i}) \neq \bot \implies \ldots$ premise, and matches `src/typecheck/linearity.nx`'s `if then_diverges then return st_else end` fall-through. Pattern-introduced linear binders are required to be consumed within their arm regardless of divergence — a divergent arm's pattern still binds names that must be observably consumed before the arm's control-flow exit (the same way a divergent arm's body still type-checks its statements).

For **match**, the projection step is explicit: each arm's $\Gamma_i$ extends Γ with pattern binders (e.g.\ the $x$ in `Some(%x) ->`), and a linear pattern binder is required to be consumed *within its arm* rather than crossing into the outer-Γ equality check. Equivalently, $\text{linConsumed}(\overline{s_i}, \Gamma_i) \setminus \text{bv}(p_i)$ is the arm's consumption restricted to outer-Γ linears, and the second `requires` clause discharges the per-arm obligation on $\Gamma_i \setminus \Gamma$ (the new bindings introduced by $p_i$). **if** has no pattern binders, so the projection collapses to the plain set equality already shown above.

For statement sequences, $\text{linConsumed}(\overline{s}, \Gamma)$ folds left-to-right, threading Γ through each statement's residual:

<div markdown="0">
$$\text{linConsumed}(\cdot, \Gamma) = \emptyset \qquad \text{linConsumed}(s; \overline{s'}, \Gamma) = \text{linConsumed}(s, \Gamma) \cup \text{linConsumed}(\overline{s'}, \Gamma \setminus\!\!\setminus s)$$
</div>

where $\Gamma \setminus\!\!\setminus s$ removes the linears consumed by $s$ before typing the tail. The per-statement base cases are:

<div markdown="0">
$$\begin{array}{rcl}
\text{linConsumed}(\textbf{let}~\mu\,x = e, \Gamma) & = & \text{linConsumed}(e, \Gamma) \\[2pt]
\text{linConsumed}(\textbf{let}~p = e, \Gamma) & = & \text{linConsumed}(e, \Gamma) \\[2pt]
\text{linConsumed}(\textbf{return}~e, \Gamma) & = & \text{linConsumed}(e, \Gamma) \\[2pt]
\text{linConsumed}(\mathord{\sim}x \leftarrow e, \Gamma) & = & \text{linConsumed}(e, \Gamma) \\[2pt]
\text{linConsumed}(e~\text{(bare expression stmt)}, \Gamma) & = & \text{linConsumed}(e, \Gamma) \\[6pt]
\text{linConsumed}(\textbf{inject}~\overline{h}~\textbf{do}~\overline{s}~\textbf{end}, \Gamma) & = & \lbrace h_i \in \overline{h} \mid \Gamma(h_i) = (1, S) \rbrace \;\uplus\; \text{linConsumed}(\overline{s}, \Gamma_\text{body}) \\
& & \text{where}~\Gamma = \Gamma_h \otimes \Gamma_\text{body},~\Gamma_h~\text{supplies the consumed handlers} \\
& & \text{(handler bindings whose scheme is linear are consumed by the inject;} \\
& & \text{the body is typed under its }\otimes\text{-split partition} \\
& & \text{— matching [T-Inject](#T-Inject) §inject linearity)} \\[6pt]
\text{linConsumed}(\textbf{while}~e~\textbf{do}~\overline{s}~\textbf{end}, \Gamma) & = & \text{linConsumed}(e, \Gamma) \\
& & \text{([T-While]'s P-Loop requires the body's linear set to round-trip,} \\
& & \text{so the body adds nothing to the loop's outer consumption)} \\[6pt]
\text{linConsumed}(\textbf{try}~\overline{s_t}~\overline{\textbf{catch}~p_i \to \overline{s_i}}~\textbf{end}, \Gamma) & = & \text{linConsumed}(\overline{s_t}, \Gamma) \;\uplus\; L_\text{try} \\
& & \text{where}~L_\text{try}~\text{is selected by arm equality / divergence,} \\
& & \text{symmetric with the }L_\text{match}~\text{clause above}
\end{array}$$
</div>

The two readings — "T-Var leaves of any derivation" and the syntactic recursion above — coincide on every well-typed program: the recursion eagerly commits to the unique consumption set the $\otimes$-splits would have produced, and undefined-$\uplus$ at any node signals exactly the "$1 + 1 = -$" reject case.

**Statement-judgment outputs read modulo the residual.** Where a rule's conclusion writes $\Gamma' = \Gamma,\, x :^q S$ for a fresh binder $x$, the operational reading is

<div markdown="0">
$$\Gamma' \;=\; (\Gamma \setminus\!\!\setminus e),\, x :^q S$$
</div>

with the residual computed against the rule's expression premise(s). Every statement-level conclusion in §2 should be read this way; T-Let and T-LetPat write the residual explicitly as the anchoring examples, and T-Seq-Cons threads it transitively through `Γ_1` from the head into the tail. The closeBlock narrative's claim — *"a linear outer binding consumed inside the block is removed from $\Gamma_\text{inner}$"* — discharges by induction over the body's statements: each statement's output is its input minus what its expressions consumed, so $\Gamma_\text{inner}$ at the body's end equals $\Gamma_\text{body} \setminus\!\!\setminus \overline{s}$ (treating $\setminus\!\!\setminus$ as iterated over the sequence).

**P-Block soundness.** With the residual reading, P-Block's $\forall x :^1 S \in \Gamma_\text{inner}.\;x \in \text{dom}(\Gamma_\text{outer}) \wedge x :^1 S \in \Gamma_\text{outer}$ scans only the linears that *survived* every consumption inside the block. A correctly-consumed inner $\%h$ is absent from $\Gamma_\text{inner}$ and therefore vacuously satisfies the premise; only genuinely-leaked or shadowed-divergent linears trigger the rejection. The same reading rescues P-FnEnd and P-Loop from the same false-positive trap.

**Implementation correspondence.** `src/typecheck/linearity.nx` carries a *live-linear set* (`LinState(vars, frame_stack)`) separate from the Γ map: the set shrinks on every linear use and grows on every linear-introducing **let**. The spec's $\Gamma \setminus\!\!\setminus e$ is the metatheoretic projection of that live-set onto Γ's linear restriction; the impl's bookkeeping is the operational embodiment of the $\otimes$-split's residual.

### Auxiliary Functions

<div markdown="0">
$$\begin{array}{rcl}
\text{typeof}(v) & = & \begin{cases}
\texttt{intlit} & \text{if } v \text{ is an integer literal} \\
\texttt{floatlit} & \text{if } v \text{ is a float literal} \\
\texttt{bool} & \text{if } v \in \lbrace \texttt{true}, \texttt{false} \rbrace \\
\texttt{string} & \text{if } v \text{ is a string literal} \\
\texttt{char} & \text{if } v \text{ is a character literal} \\
\texttt{unit} & \text{if } v = ()
\end{cases} \\[4pt]
\text{occurs}(\alpha, \tau) & & \text{holds iff } {?}\alpha \in \text{fv}(\tau) \\[4pt]
\text{fields}(\tau) & = & \begin{cases}
\overline{\ell : \sigma} & \text{if } \tau = \lbrace \overline{\ell : \sigma} \rbrace \\
\overline{\ell : \sigma[\overline{\alpha := \tau'}]} & \text{if } \tau = x\langle\overline{\tau'}\rangle,\;\text{typedef}(x) = \forall\overline{\alpha}.\,\lbrace\overline{\ell : \sigma}\rbrace \\
\text{error} & \text{otherwise}
\end{cases} \\[4pt]
\text{variants}(\tau) & = & \text{constructors of } \tau \\[4pt]
\text{exhaustive}(\tau, \overline{p}) & & \text{holds iff } \text{check}(M, [\tau]) = \text{ok},\; M = [[p_1], \ldots, [p_n]]
\end{array}$$
</div>

$\text{typedef}(x)$ denotes the definition of named type $x$ in the global type-definition environment.

Other functions are introduced where first used: `linear`, `autoDrop` (Linearity), `strip` (Pattern Matching), `open`, `stripCall`, `selectInt`/`selectFloat` and `comparable` (Expressions), `default`, `wrapSigil` (Statements), `merge` (Statements), `tail`, `branchType` (Expressions), `methods` (Expressions), `caughtVariants`, `hasCatchAll`, `members`, `diverges` (Statements), `closeBlock` (Statements).

### Free Variables

`fv` is overloaded — on a *type*, it returns the free unification variables (used by `occurs` in the unification rules); on a *term*, it returns the free term variables (used by [T-Lambda](#T-Lambda) and [T-Handler](#T-Handler) to compute the captured-binding partition $\Gamma_\text{cap}$). Disambiguation is by the argument's syntactic category.

The companion $\text{bv}(p)$ returns the binder names introduced by a pattern; it cooperates with `fv` when stripping shadowed names from a statement-sequence's free set.

Free variables of expressions (selected cases — clauses for forms with no binders trivially recurse into subterms):

<div markdown="0">
$$\begin{array}{rcl}
\text{fv}(\mu\,x) & = & \lbrace x \rbrace \\
\text{fv}(c) & = & \emptyset \\
\text{fv}(n) = \text{fv}(f) = \text{fv}(b) = \text{fv}(s) = \text{fv}(ch) = \text{fv}(()) & = & \emptyset \\
\text{fv}(e_1 \oplus e_2) & = & \text{fv}(e_1) \cup \text{fv}(e_2) \\
\text{fv}(f(\overline{\ell : e})) & = & \text{fv}(f) \cup \textstyle\bigcup_i \text{fv}(e_i) \\
\text{fv}(\textbf{fn}~(\overline{\ell : \tau}) \to \ldots~\textbf{do}~\overline{s}~\textbf{end}) & = & \text{fv}(\overline{s}) \setminus \lbrace \overline{\ell} \rbrace \\
\text{fv}(\textbf{if}~e~\textbf{then}~\overline{s_1}~\textbf{else}~\overline{s_2}) & = & \text{fv}(e) \cup \text{fv}(\overline{s_1}) \cup \text{fv}(\overline{s_2}) \\
\text{fv}(\textbf{match}~e~\lbrace \overline{p_i \to s_i} \rbrace) & = & \text{fv}(e) \cup \textstyle\bigcup_i (\text{fv}(\overline{s_i}) \setminus \text{bv}(p_i)) \\
\text{fv}(\lbrace \overline{\ell : e} \rbrace) & = & \textstyle\bigcup_i \text{fv}(e_i) \\
\text{fv}(e.\ell) & = & \text{fv}(e) \\
\text{fv}(@e) = \text{fv}(\&x) & = & \text{fv}(e),\;\lbrace x \rbrace~\text{respectively} \\
\text{fv}(\textbf{throw}~e) & = & \text{fv}(e) \\
\text{fv}(\textbf{handler}~x~[\textbf{require}~\rho]~\textbf{do}~\overline{\ell = e}~\textbf{end}) & = & \textstyle\bigcup_j \text{fv}(e_j)
\end{array}$$
</div>

Free variables of statement sequences are defined cumulatively from the right, with $\text{bv}(p)$ stripping shadowed names introduced earlier in the sequence:

<div markdown="0">
$$\begin{array}{rcl}
\text{fv}(\cdot) & = & \emptyset \\
\text{fv}(\textbf{let}~\mu\,x = e;\;\overline{s'}) & = & \text{fv}(e) \cup (\text{fv}(\overline{s'}) \setminus \lbrace x \rbrace) \\
\text{fv}(\textbf{let}~p = e;\;\overline{s'}) & = & \text{fv}(e) \cup (\text{fv}(\overline{s'}) \setminus \text{bv}(p)) \\
\text{fv}(\textbf{return}~e;\;\overline{s'}) & = & \text{fv}(e) \cup \text{fv}(\overline{s'}) \\
\text{fv}(\mathord{\sim}x \leftarrow e;\;\overline{s'}) & = & \lbrace x \rbrace \cup \text{fv}(e) \cup \text{fv}(\overline{s'}) \\
\text{fv}(\textbf{inject}~\overline{h}~\textbf{do}~\overline{s_b}~\textbf{end};\;\overline{s'}) & = & \lbrace \overline{h} \rbrace \cup \text{fv}(\overline{s_b}) \cup \text{fv}(\overline{s'}) \\
\text{fv}(\textbf{try}~\overline{s_t}~\textbf{catch}~\overline{p_i \to s_i}~\textbf{end};\;\overline{s'}) & = & \text{fv}(\overline{s_t}) \cup \textstyle\bigcup_i (\text{fv}(\overline{s_i}) \setminus \text{bv}(p_i)) \cup \text{fv}(\overline{s'}) \\
\text{fv}(e;\;\overline{s'}) & = & \text{fv}(e) \cup \text{fv}(\overline{s'})
\end{array}$$
</div>

Bound variables of patterns:

<div markdown="0">
$$\begin{array}{rcl}
\text{bv}(x) & = & \lbrace x \rbrace \\
\text{bv}(\_) = \text{bv}(n) & = & \emptyset \\
\text{bv}(c(\overline{\ell : p})) & = & \textstyle\bigcup_i \text{bv}(p_i) \\
\text{bv}(\lbrace \overline{\ell : p} \rbrace) & = & \textstyle\bigcup_i \text{bv}(p_i) \\
\text{bv}(p_1 \mathbin{\vert} p_2) & = & \text{bv}(p_1) = \text{bv}(p_2)~\text{(both alternatives must bind the same set; see [P-Or](#pattern-matching))}
\end{array}$$
</div>

The sequence-level `fv` accounts for shadowing: a $\textbf{let}~x = \ldots$ removes $x$ from the tail's free set, so a later capture site sees through the binding to whatever $x$ refers to in *its* enclosing scope. Without the subtraction, $\textbf{fn}\;()~\textbf{do}\;\textbf{let}~x = 1;\;\textbf{return}~x~\textbf{end}$ would compute $\text{fv} = \lbrace x \rbrace$ and try to capture an outer $x$ that does not exist.

Free unification variables of a *type* (used by `occurs` in unification) include both type-kinded `${?}\alpha$` and row-kinded `${?}r$`. Rigid quantifiers (α, $r$) are not free unification variables — they're parameters of the surrounding scheme, not refinement targets:

<div markdown="0">
$$\begin{array}{rcl}
\text{fv}(b) = \text{fv}(\texttt{intlit}) = \text{fv}(\texttt{floatlit}) & = & \emptyset \\
\text{fv}(\alpha) & = & \emptyset \quad\text{(rigid type variable)} \\
\text{fv}({?}\alpha) & = & \lbrace {?}\alpha \rbrace \\
\text{fv}((\overline{\ell : \tau}) \to \tau_r;\,\rho_q;\,\rho_e) & = & \textstyle\bigcup_i \text{fv}(\tau_i) \cup \text{fv}(\tau_r) \cup \text{fv}(\rho_q) \cup \text{fv}(\rho_e) \\
\text{fv}(\lbrace \overline{\ell : \tau} \rbrace) & = & \textstyle\bigcup_i \text{fv}(\tau_i) \\
\text{fv}(x\langle \overline{\tau} \rangle) & = & \textstyle\bigcup_i \text{fv}(\tau_i) \\
\text{fv}([\tau]) = \text{fv}([\lvert\,\tau\,\rvert]) & = & \text{fv}(\tau) \\
\text{fv}(\%\tau) = \text{fv}(@\tau) = \text{fv}(\&\tau) = \text{fv}(\mathord{\sim}\tau) & = & \text{fv}(\tau) \\
\text{fv}(\textbf{handler}\;x\;\rho) & = & \text{fv}(\rho) \\
\text{fv}(\lbrace \overline{\tau} \rbrace) & = & \textstyle\bigcup_i \text{fv}(\tau_i) \quad\text{(closed row)} \\
\text{fv}(\lbrace \overline{\tau} \mid r \rbrace) & = & \textstyle\bigcup_i \text{fv}(\tau_i) \quad\text{(open row with rigid tail)} \\
\text{fv}(\lbrace \overline{\tau} \mid {?}r \rbrace) & = & \textstyle\bigcup_i \text{fv}(\tau_i) \cup \lbrace {?}r \rbrace \quad\text{(open row with unification tail)}
\end{array}$$
</div>

The last clause is load-bearing for unification termination: when [U-Var](#U-Var) attempts $\text{unify}({?}\alpha, \tau)$ with τ containing an open row $\lbrace \overline{\tau} \mid {?}\alpha \rbrace$, the $\text{occurs}({?}\alpha, \tau)$ check inspects $\text{fv}(\tau) \ni {?}\alpha$ and rejects, preventing the cycle $({?}\alpha \mathrel{:=} \lbrace \overline{\tau} \mid {?}\alpha \rbrace)$ that would diverge under substitution. Symmetrically for ${?}r$: a row unification variable participates in `occurs` exactly when its enclosing type's `fv` includes it.

### Linearity

$\text{linear}(\tau)$ is a structural (recursive) predicate: holds if τ is $\%\sigma$, $@\sigma$, or $[\lvert\,\sigma\,\rvert]$ at the outermost level, or if any transitive component of τ satisfies the predicate. Components inspected by the recursion: fields of records, type arguments of named types, element types of lists, and elements of rows. Borrows $\&\sigma$ and mutable refs $\mathord{\sim}\sigma$ are skipped: a borrow is reusable ($q = \omega$), and the underlying owner's status is tracked at the owner's binding. Mutable refs receive an upstream guarantee from [§Mutable Reference Well-Formedness](#mutable-reference-well-formedness), which rejects $\mathord{\sim}\sigma$ at every introduction site whenever $\text{linear}(\sigma)$ — so by the time the predicate is consulted on a $\mathord{\sim}\sigma$ value the payload is already known non-linear.

Function arrows $(\overline{\ell:\tau}) \to \tau_r$ and handlers $\textbf{handler}\;x\;\rho$ are governed by capture-linearisation in [T-Lambda](#T-Lambda) / [T-Handler](#T-Handler); the predicate skips their interior. Example: $\text{linear}(\text{Pair}\langle\%\texttt{i64}, \texttt{i64}\rangle)$ holds because the first type argument carries a $\%$ wrapper; $\text{linear}(\mathord{\sim}\texttt{i64})$ does not — the $\mathord{\sim}$ wrapper is structurally non-linear.

$\text{autoDrop}(\tau)$ holds if the innermost non-modality type of τ (recursively stripping $\%$, $\&$, $\mathord{\sim}$ — but **not** $@$) is in $\lbrace b, \texttt{intlit}, \texttt{floatlit} \rbrace$. Types whose linear wrapper can be silently discarded. Thunks $@\sigma$ are explicitly **not** auto-droppable: an unforced thunk holds a suspended computation (with potentially-captured linear state, caps, or other resources) that the runtime never runs if the binding is silently dropped — exactly the *one-shot lazy continuation* hazard called out in [drop.md](../drop). Likewise arrays $[\lvert\,\sigma\,\rvert]$ are not auto-droppable: their linear contents (allocated cells, captured handles) must be released explicitly. The narrow auto-drop set is intentional — only structurally trivial values (scalars, intlit/floatlit, base types) qualify; anything else must reach an explicit consumption channel.

**Variable cases.** Both predicates take the *conservative* answer on unresolved unification variables and on rigid type/row quantifiers:

<div markdown="0">
$$\text{linear}({?}\alpha) = \text{linear}(\alpha) = \text{false}\qquad \text{autoDrop}({?}\alpha) = \text{autoDrop}(\alpha) = \text{false}$$
</div>

A $\%$- or $@$-wrapper around a variable, e.g.\ $\%{?}\alpha$ or $\%\alpha$, is still linear by the outermost-wrapper clause — only a bare variable defaults to non-linear. The convention is conservative in two opposite ways:

- $\text{linear} = \text{false}$ on a bare variable means [P-Var](#P-Var) assigns $q = \omega$ to a pattern bound at type $?\alpha$ (e.g.\ the divergent-RHS case where $\textbf{throw}~e$ returns $?\alpha$). The binding never carries a linear obligation; the unifier may later refine $?\alpha$ to a non-linear concrete type without re-evaluation. If a later occurrence demands linear ($\%\sigma$), unification refines $?\alpha$ at the wrapped position and the $\%$-clause makes linearity locally visible.
- $\text{autoDrop} = \text{false}$ on a bare variable means [P-Wild](#P-Wild) rejects discarding any binding whose type is still $?\alpha$ until it's resolved — the lambda body's $\textbf{let}~\_ = e$ for $e : ?\alpha$ is statically rejected as a possible silent leak. This is conservative *the other direction*: we prefer false-positive errors over silent linear discard.

The two conventions together preserve soundness: any program that type-checks under the variable cases also type-checks at every later refinement of those variables (provided the refinement is consistent with the rest of the derivation). Mechanically, `src/typecheck/linearity.nx`'s `is_linear_binding_type` and `is_auto_droppable` implement these defaults — both fall through to `false` on `TyVar`.

**Recursive named types: cycle-guarded fixpoint.** When $\text{linear}(\tau)$ recurses into a named type $x\langle \overline{\tau} \rangle$, it must unfold $x$'s declaration to inspect field/variant types — but a self-referential or mutually-recursive declaration (e.g.\ $\textbf{type}~\texttt{Tree}\langle T \rangle = \texttt{Leaf} \mathbin{\vert} \texttt{Node}(\textit{left}: \texttt{Tree}\langle T \rangle, \ldots)$) makes naive structural recursion non-terminating. The evaluation is therefore parameterised by a **visited set** $V$ and computed as a least fixpoint:

<div markdown="0">
$$\text{linear}(\tau) \;=\; \text{linear}'(\tau, \emptyset) \qquad \text{autoDrop}(\tau) \;=\; \text{autoDrop}'(\tau, \emptyset)$$
</div>

with the cycle guard

<div markdown="0">
$$\text{linear}'(x\langle \overline{\tau} \rangle, V) = \begin{cases}
\text{false} & \text{if}~x \in V \quad (\text{cycle: minimum fixpoint}) \\
\bigvee_{F~\text{a field-or-variant-arg type of}~\text{unfold}(x\langle \overline{\tau} \rangle)} \text{linear}'(F, V \cup \lbrace x \rbrace) & \text{otherwise}
\end{cases}$$
</div>

and analogously for $\text{autoDrop}'$. All other clauses (the $\%\sigma$, $@\sigma$, $[\lvert\sigma\rvert]$ outermost wrappers, base types, records, lists, type-arg recursion) thread $V$ unchanged. The cycle case returns *false* — the conservative answer that makes the predicate the minimum fixpoint and keeps a recursive type non-linear unless one of its non-recursive components forces linearity. Concretely:

- $\text{linear}(\texttt{Tree}\langle T \rangle)$ where $\texttt{Tree}\langle T \rangle = \texttt{Leaf} \mathbin{\vert} \texttt{Node}(\textit{left}: \texttt{Tree}\langle T \rangle, \textit{val}: T, \textit{right}: \texttt{Tree}\langle T \rangle)$ unfolds to fields $\lbrace \texttt{Tree}\langle T \rangle, T, \texttt{Tree}\langle T \rangle \rbrace$. The two recursive references hit the cycle guard and return `false`; $T$ is a rigid quantifier (also `false`). Result: `false` — Tree is non-linear unless $T$ is later instantiated to a linear type.
- $\text{linear}(\texttt{LList}\langle T \rangle)$ where $\texttt{LList}\langle T \rangle = \texttt{Empty} \mathbin{\vert} \texttt{Cons}(\textit{head}: T, \textit{tail}: \%\texttt{LList}\langle T \rangle)$ unfolds to fields $\lbrace T, \%\texttt{LList}\langle T \rangle \rbrace$. The second field's outermost $\%$ wrapper trips the linear clause *before* the cycle guard fires, returning `true`. Result: `true` — the explicit $\%$ on the recursive tail makes the list itself linear.

The implementation memoises by $x \mapsto (\text{linear}, \text{autoDrop})$ to avoid re-walking the body; the spec's $V$ parameter is the metatheoretic counterpart of that memo table.

Linearity is entirely structural: the split $\otimes$ ensures each linear binding ($q = 1$) goes to exactly one sub-derivation, and branching constructs give both arms the same portion of Γ.

<a id="mutable-reference-well-formedness"></a>

**Mutable-reference well-formedness (`wfRef`).** A mutable reference cell $\mathord{\sim}\sigma$ permits unrestricted reads (each $\mathord{\sim}x$ via [T-Deref](#T-Deref) yields a fresh σ) and assignments (via [T-Assign](#T-Assign)). If σ were linear, each read would produce a fresh copy of the linear payload, duplicating the resource — incompatible with linearity's single-use discipline. The type system therefore rejects $\mathord{\sim}\sigma$ as malformed when σ is linear:

<div markdown="0">
$$\text{wfRef}(\mathord{\sim}\sigma) \;\Longleftrightarrow\; \neg\text{linear}(\sigma)$$
</div>

**Checked at (introduction sites).**  `wfRef` is enforced at every type-formation site that can introduce a $\mathord{\sim}\sigma$ into the typing context:

| Site | Rule |
|------|------|
| Parameter and return slots of a **fn** literal | [T-Lambda](#T-Lambda), [T-Let-PolyFn](#T-Let-PolyFn) |
| Method signature in a cap declaration | [D-Cap](#D-Cap) |
| Type annotation of an external binding | [D-External](#D-External) |
| Field types of a record type declaration | [D-Type-Record](#D-Type-Record) |
| Field types of a sum-type variant | [D-Type-Sum](#D-Type-Sum), [D-Type-Sum-Opaque](#D-Type-Sum-Opaque) |
| Explicit type annotation on a let-binding | [T-Let](#T-Let) |

`wfRef` is checked at every **type-formation site** that can introduce a $\mathord{\sim}\sigma$: parameter and return slots of **fn** literals ([T-Lambda](#T-Lambda) / [T-Let-PolyFn](#T-Let-PolyFn)), the signature of a method declared by [D-Cap](#D-Cap), the type annotation of [D-External](#D-External), the field types of [D-Type-Record](#D-Type-Record) / [D-Type-Sum](#D-Type-Sum) / [D-Type-Sum-Opaque](#D-Type-Sum-Opaque), and any explicit type annotation on [T-Let](#T-Let). The check fails fast at declaration time rather than letting a $\mathord{\sim}\%T$-shaped value smuggle in through e.g.\ an externally-declared signature, then duplicate the inner linear via successive $\mathord{\sim}x$ reads. T-Let itself also carries the rule-local guard $\mu = \mathord{\sim} \implies \neg\text{linear}(\tau')$ (see [T-Let](#T-Let)); `wfRef` is the global counterpart that catches the same hazard when the type sneaks in through a non-sigil channel.

Two additional behaviors are embedded in specific rules rather than stated as standalone inference rules:

- **Weakening** (in [T-App](#T-App)): when a parameter has type $\%\tau$ and the argument has type σ with $\neg\text{linear}(\sigma)$, $\text{unify}(\sigma, \tau)$ is used instead of $\text{unify}(\sigma, \%\tau)$. This applies only to the linear modality $\%$, not to $@$ or other linear-producing forms.
- **Closure linearization** (in [T-Lambda](#T-Lambda)): when a lambda captures any linear binding from Γ, its closure type is wrapped with $\%$ (making the closure itself linear).

<a id="gravity-rule-occurrence-position"></a>

**Gravity rule — occurrence-position constraint ($\neg\text{escapesRef}$).** `wfRef` above only checks that the *inner* type of a reference cell is non-linear. It does not prevent the reference cell type $\mathord{\sim}\sigma$ itself from appearing in positions that would let the cell outlive its defining function. The *gravity rule* (documented in [types.md §Gravity Rule](../types)) additionally prohibits $\mathord{\sim}\sigma$ from appearing in **escape positions**: the return type of a function, the field type of a heap-allocated record or sum-type variant, and — via closure linearization plus the no-ref-capture premise in [T-Lambda](#T-Lambda) — closure captures. The formal predicate is:

<div markdown="0">
$$\text{escapesRef}(\tau) \;\Longleftrightarrow\; \tau~\text{contains}~\mathord{\sim}\sigma~\text{at any structurally reachable position (record fields, ADT fields, list element type, or as the type itself)}$$
</div>

The occurrence-position constraint is enforced at the following sites:

| Site | Premise added | Rule |
|------|---------------|------|
| Return type of a **fn** declaration | $\neg\text{escapesRef}(\tau_r)$ | [T-Lambda](#T-Lambda), [T-Let-PolyFn](#T-Let-PolyFn) |
| Method return type in a cap declaration | $\neg\text{escapesRef}(\kappa_j)$ | [D-Cap](#D-Cap) |
| Return type of an external binding | $\neg\text{escapesRef}(\tau_r)$ | [D-External](#D-External) |
| Field types of a record type declaration | $\forall \ell.\;\neg\text{escapesRef}(\tau_\ell)$ | [D-Type-Record](#D-Type-Record) |
| Field types of a sum-type variant | $\forall i.\;\neg\text{escapesRef}(\tau_i)$ | [D-Type-Sum](#D-Type-Sum), [D-Type-Sum-Opaque](#D-Type-Sum-Opaque) |
| Explicit **return** statement | $\neg\text{escapesRef}(\tau)$ | [T-Return](#T-Return) |

The T-Return premise is the last-resort catch for any reference type that reaches a return statement without being screened at a declaration site. The declaration-site premises (T-Lambda/T-Let-PolyFn return-type annotation, D-Type-Record/D-Type-Sum fields) provide early rejection at the type-formation point and are the primary enforcement layer; T-Return is a secondary guard for annotated-return-type mismatches. Closure capture of $\mathord{\sim}\sigma$ is already ruled out by T-Lambda's `no ref capture` premise ($\forall x \in \text{fv}(\overline{s}) \cap \text{dom}(\Gamma).\;\Gamma(x) \neq \mathord{\sim}\sigma$) and does not require a separate $\neg\text{escapesRef}$ premise there.

### Unification

Unification is symmetric: $\text{unify}(\tau_1, \tau_2) = \text{unify}(\tau_2, \tau_1)$ unless otherwise noted. The rules below are written with the "interesting" argument on the left; the symmetric case is implied. U-Borrow is intentionally asymmetric (no symmetric counterpart); U-Expand is asymmetric in form but applies in both argument orders by the symmetry convention.

**Argument-order convention.** Where the rules below are asymmetric, the **left** argument is the *actual* (the type produced by an expression or read out of a binding) and the **right** argument is the *expected* (the type a context demands — a parameter slot, an annotation, a return type). All call sites in the typing rules follow this convention:

- [T-App](#T-App): $\text{unify}(\tau_i, P_i)$ with the argument's actual type on the left
- [T-Let](#T-Let): $\text{unify}(\tau', \sigma)$ with the inferred type on the left and the annotation on the right
- [T-Return](#T-Return): $\text{unify}(\tau, \tau_r)$ with the expression's type on the left
- [T-Assign](#T-Assign): $\text{unify}(\sigma, \tau)$ with the assigned expression on the left

This convention is what makes U-Borrow's asymmetry well-defined: $\&\sigma$ on the left (an actual borrow value being supplied) auto-derefs to σ; $\&\sigma$ on the right (a context demanding a borrow) does not. That choice means borrows can be passed where the underlying type is expected, but plain values are never auto-borrowed — call sites must use $\&x$ explicitly.

<a id="U-Refl"></a>

<div markdown="0">
$$\dfrac{}{\text{unify}(\tau, \tau) = \emptyset} \;\textsc{U-Refl}$$
</div>

<div markdown="0">
$$\dfrac{\neg\text{occurs}(\alpha, \tau)}{\text{unify}({?}\alpha, \tau) = \lbrace {?}\alpha := \tau \rbrace} \;\textsc{U-Var}
\qquad
\dfrac{\text{occurs}(\alpha, \tau)}{\text{unify}({?}\alpha, \tau) = \text{error}} \;\textsc{U-Occurs}$$
</div>

<a id="U-RowVar"></a>

<div markdown="0">
$$\dfrac{\neg\text{occurs}(r, \rho)}{\text{unify}({?}r, \rho) = \lbrace {?}r := \rho \rbrace} \;\textsc{U-RowVar}
\qquad
\dfrac{\text{occurs}(r, \rho)}{\text{unify}({?}r, \rho) = \text{error}} \;\textsc{U-RowOccurs}$$
</div>

U-RowVar mirrors U-Var for the **row** sort: a bare row unification variable ${?}r$ refines to any row ρ that does not mention $r$. The occurs check uses $\text{fv}(\rho)$ extended to rows by the open-tail clause $\text{fv}(\lbrace \overline{\tau} \mid {?}r \rbrace) = \text{fv}(\overline{\tau}) \cup \lbrace {?}r \rbrace$ from §Free Variables. U-RowVar applies in both argument orders by the symmetry convention (so $\text{unify}(\rho, {?}r)$ is handled too), and covers in particular the $\text{unify}({?}r_1, {?}r_2)$ case where two fresh row variables are aliased. Row variables arise from [inst](#inst) at every use site whose scheme has a kind-$\texttt{Row}$ quantifier, and from $\text{open}(\rho)$ in [T-App](#T-App)'s capability-row premise. The three [U-Row-*](#U-Row-Open-Open) rules below handle the case where *both* operands have entries (i.e. the rows have the shape $\lbrace \overline{\tau} \mid \cdot \rbrace$ with $\overline{\tau} \neq \emptyset$); U-RowVar covers the residual case where one side is a bare row variable. As with U-Var, refining ${?}r$ produces a non-empty substitution that propagates through the derivation.

<div markdown="0">
$$\dfrac{}{\text{unify}(\texttt{intlit}, \texttt{i32}) = \lbrace\rbrace} \quad
\dfrac{}{\text{unify}(\texttt{intlit}, \texttt{i64}) = \lbrace\rbrace} \;\textsc{U-IntLit}$$
</div>

<div markdown="0">
$$\dfrac{}{\text{unify}(\texttt{floatlit}, \texttt{f32}) = \lbrace\rbrace} \quad
\dfrac{}{\text{unify}(\texttt{floatlit}, \texttt{f64}) = \lbrace\rbrace} \;\textsc{U-FloatLit}$$
</div>

Two `intlit` (or two `floatlit`) occurrences unify by [U-Refl](#U-Refl) — both sides are the same singleton symbol, so syntactic identity holds trivially and the empty substitution suffices. **U-IntLit / U-FloatLit also return the empty substitution**: the per-occurrence resolution is *local* to the unification site, not broadcast through the typing context. This matches the impl in `src/typecheck/unify.nx` (line 42–46) and preserves compositionality — a `let x: i32 = 1; let y: i64 = 2` sequence is well-typed because resolving the first literal at `i32` does not rewrite the second occurrence's `intlit` to `i32` before it meets `i64`. The narrative in §1.2 calling `intlit`/`floatlit` a "shared symbol" refers to their *grammar* (they're the same metavariable across occurrences), not to a typing-time shared identity. Resolution proceeds two ways:

- **At a use site** — unifying `intlit` with a concrete $\tau \in \lbrace \texttt{i32}, \texttt{i64} \rbrace$ succeeds at that use's local typing, returning $\lbrace\rbrace$; the literal at *that* occurrence is treated as τ for the rest of the derivation through ordinary Γ-flow, but other occurrences of `intlit` in the same program remain at `intlit` until they too unify.
- **At a let-binding site** — if a literal still types at `intlit` when it reaches [T-Let](#T-Let), the `default` auxiliary pins it to `i64` (resp.\ `f64` for `floatlit`). This is the only fallback; literals that flow into other contexts (function arguments, return values) must have been pinned by unification before reaching the let.

U-Var produces a non-empty substitution because $?\alpha$ stands for a *named* unification variable shared across the derivation — refining $?\alpha$ to a concrete type must propagate. U-IntLit and U-FloatLit's empty substitution is the operational counterpart of "`intlit` is a grammar symbol, not a per-derivation variable". U-Var, U-IntLit, and U-FloatLit apply in both argument orders via the symmetry convention above.

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \lvert\overline{p_1}\rvert = \lvert\overline{p_2}\rvert \qquad
  \forall i.\;\text{unify}(\tau_i^1, \tau_i^2) \\[2pt]
  \text{unify}(\tau_{r1}, \tau_{r2}) \qquad
  \text{unify}(\rho_{q1}, \rho_{q2}) \qquad
  \text{unify}(\rho_{e1}, \rho_{e2})
  \end{array}
}{
  \text{unify}((\overline{p_1}) \to \tau_{r1};\, \rho_{q1};\, \rho_{e1},\;
  (\overline{p_2}) \to \tau_{r2};\, \rho_{q2};\, \rho_{e2})
} \;\textsc{U-Arrow}$$
</div>

Arrow parameters unify **positionally**, by index — labels are not part of the arrow type's structural identity. A parameter label is metadata used at the *call site* (see [T-App](#T-App)): the caller writes $f(\ell_i\colon e_i)$ using the labels declared on the *type the caller sees*, and call-site label matching is what resolves which positional slot each argument fills. Two arrow types $(x\colon \tau) \to \tau'$ and $(y\colon \tau) \to \tau'$ therefore unify (and the call site uses whichever label its surface type carries), but $(x\colon \tau_1, y\colon \tau_2)$ and $(y\colon \tau_2, x\colon \tau_1)$ do **not** — order is significant.

This contrasts with [U-Record](#U-Record) below, where field names *are* part of the type's identity: a record value carries its labels into every use site, so two records with the same labels but in different declaration order are the same type, while two records with different labels are distinct types.

<div markdown="0">
$$\dfrac{
  \lvert\overline{f_1}\rvert = \lvert\overline{f_2}\rvert \qquad
  \text{sorted by label} \qquad
  \forall i.\;\ell_i^1 = \ell_i^2 \qquad
  \forall i.\;\text{unify}(\tau_i^1, \tau_i^2)
}{
  \text{unify}(\lbrace \overline{f_1} \rbrace, \lbrace \overline{f_2} \rbrace)
} \;\textsc{U-Record}$$
</div>

<div markdown="0">
$$\dfrac{
  \forall i.\;\text{unify}(\tau_i, \sigma_i)
}{
  \text{unify}(x\langle\overline{\tau}\rangle, x\langle\overline{\sigma}\rangle)
} \;\textsc{U-Named}$$
</div>

U-Named handles the *symmetric* case where both operands are named types and the names match. The two *asymmetric* cross-shape cases — a named record-typedef appearing opposite a structural record, and the prelude $\texttt{List}\langle\tau\rangle$ enum appearing opposite the surface syntax $[\tau]$ — are covered by [U-Expand](#U-Expand) and [U-ListSugar](#U-ListSugar) below respectively. There is **no** mixed-name case ($\text{unify}(x\langle\overline{\tau}\rangle, y\langle\overline{\sigma}\rangle)$ with $x \neq y$): the symmetry convention plus the absence of such a rule means name mismatch is a unification error, with one exception — when one side is a record-typedef and the other is a structural record, U-Expand unfolds the typedef before comparing.

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \overline{c} = \overline{\tau_1} \cap \overline{\tau_2} \qquad
  \overline{r_1} = \overline{\tau_1} \setminus \overline{c} \qquad
  \overline{r_2} = \overline{\tau_2} \setminus \overline{c} \\[4pt]
  {?}\gamma ~\text{fresh} \qquad
  \text{unify}({?}t_1, \lbrace \overline{r_2} \mid {?}\gamma \rbrace) \qquad
  \text{unify}({?}t_2, \lbrace \overline{r_1} \mid {?}\gamma \rbrace)
  \end{array}
}{
  \text{unify}(\lbrace \overline{\tau_1} \mid {?}t_1 \rbrace, \lbrace \overline{\tau_2} \mid {?}t_2 \rbrace)
} \;\textsc{U-Row-Open-Open}$$
</div>

<div markdown="0">
$$\dfrac{
  \overline{\tau_1} = \overline{\tau_2}~\text{as multisets (order-irrelevant)}
}{
  \text{unify}(\lbrace \overline{\tau_1} \rbrace, \lbrace \overline{\tau_2} \rbrace)
} \;\textsc{U-Row-Closed-Closed}$$
</div>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \overline{c} = \overline{\tau_1} \cap \overline{\tau_2} \qquad
  \overline{r_1} = \overline{\tau_1} \setminus \overline{c} \qquad
  \overline{r_2} = \overline{\tau_2} \setminus \overline{c} \\[4pt]
  \overline{r_2} = \emptyset \qquad
  \text{unify}({?}t_2, \lbrace \overline{r_1} \rbrace)
  \end{array}
}{
  \text{unify}(\lbrace \overline{\tau_1} \rbrace, \lbrace \overline{\tau_2} \mid {?}t_2 \rbrace)
} \;\textsc{U-Row-Closed-Open}$$
</div>

The three U-Row rules cover every combination of closed/open arguments. Closed-closed succeeds only when the multisets are equal — neither side has a tail to absorb the difference. Closed-open is the asymmetric mixed case: the right-hand tail must absorb whatever the left has beyond the common prefix, but the left being closed means the right cannot have entries the left lacks ($\overline{r_2} = \emptyset$). The open-closed case follows by the symmetry convention stated at the start of §Unification.

<a id="U-Row-Exn"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \texttt{Exn} \in \overline{\tau_2} \qquad
  \overline{c} = \overline{\tau_2} \setminus \lbrace \texttt{Exn} \rbrace \\[2pt]
  \forall C \in \overline{\tau_1}.\;\;C = \texttt{Exn} \;\vee\; C \in \overline{c} \;\vee\; C \in \text{variants}(\texttt{Exn})
  \end{array}
}{
  \text{unify}(\lbrace \overline{\tau_1} \rbrace,\; \lbrace \overline{\tau_2} \rbrace)
} \;\textsc{U-Row-Exn}$$
</div>

U-Row-Exn handles the variant-lattice subsumption of `Exn` described in §1.3: when one side carries the catch-all sentinel `Exn`, any constructors of `Exn` on the other side are absorbed by it. This is the *only* place the type system admits a row-inclusion relationship — every other row rule requires entry-by-entry equality. U-Row-Exn applies in both argument orders by the symmetry convention. It is intentionally restricted to closed-closed shapes; a shape where one side is an open row $\lbrace \overline{\tau} \mid {?}r \rbrace$ carrying (or paired with) `Exn` does **not** reduce to U-Row-Closed-Open before re-applying U-Row-Exn: U-Row-Closed-Open's premise $\overline{r_2} = \emptyset$ fails whenever the open side carries `Exn` (since $\overline{r_2} = \overline{\tau_2} \setminus \overline{c} \ni \texttt{Exn}$). In practice, by the time effect rows are unified against a closed call-site row all tail variables have been solved to closed rows, so the closed-closed form of U-Row-Exn always applies. The Exn-absorption check for throw sites that have not yet resolved an open tail is handled separately in the throw-site well-formedness pass (`row_admits_exception` in `src/typecheck/infer.nx`) rather than through row unification.

**Throws-position restriction.** U-Row-Exn is sound *only* for throws-position rows $\rho_e$. The premise $\texttt{Exn} \in \overline{\tau_2}$ guards activation: per §Row Types, `Exn` and `variants(Exn)` enter rows exclusively through [T-Throw-Ctor](#T-Throw-Ctor) / [T-Throw-CtorNullary](#T-Throw-Val) / [T-Throw-Val](#T-Throw-Val), all of which target the throws row. A require row $\rho_q$ contains user-declared cap names and `SysCaps` only — neither `Exn` nor a `variants(Exn)` constructor name can land there by any introduction rule, so the activation premise of U-Row-Exn is unreachable for $\rho_q$. The rule therefore does not need an explicit kind annotation in the formal premise — its activation set is by-construction throws-only. This matches the impl: `src/typecheck/unify.nx::unify_rows_kind_i` threads a `kind` argument (`"throws"` / `"requires"`) and only the throws path consults the Exn-absorption logic. The kind discrimination is operational rather than formal, mirroring the §Row Types convention that row position is maintained by the introduction rules and not by a kind system.

<div markdown="0">
$$\dfrac{
  \neg\text{linear}(\tau_2) \qquad
  \text{unify}(\tau_1, \tau_2)
}{
  \text{unify}(\&\tau_1, \tau_2)
} \;\textsc{U-Borrow}$$
</div>

The $\neg\text{linear}(\tau_2)$ premise blocks borrow-to-ownership smuggling: a value of type $\&\sigma$ supplied where the context demands a linear $\tau_2$ would let the callee consume the underlying resource while the caller (still holding the borrow's source) believes the resource is alive. With the premise, $\textit{consume}(\&\%r)$ is rejected at unification — the borrow must be explicitly cloned or the caller must move ownership.

<a id="U-Expand"></a>

<div markdown="0">
$$\dfrac{
  \text{fields}(x\langle\overline{\tau}\rangle) = \lbrace \overline{\ell : \sigma} \rbrace \qquad
  \text{unify}(\lbrace \overline{\ell : \sigma} \rbrace, R)
}{
  \text{unify}(x\langle\overline{\tau}\rangle, R)
} \;\textsc{U-Expand}$$
</div>

U-Expand is what makes a value constructed via a record literal (whose inferred type is the structural $\lbrace \overline{\ell : \tau} \rbrace$) unify with a slot annotated using the named-record alias $x\langle\overline{\sigma}\rangle$ — e.g.\ `let p = Pair(fst: 1, snd: 2)` (structural) flowing into `let q: Pair<i64, i64> = p` (named). The premise $\text{fields}(x\langle\overline{\tau}\rangle) = \lbrace \overline{\ell : \sigma} \rbrace$ looks up the record-typedef body $\forall\overline{\alpha}.\,\lbrace \overline{\ell : F} \rbrace$ and substitutes the type arguments to obtain $\sigma_i = F_i[\overline{\alpha := \tau}]$. U-Expand applies **only** to record typedefs; sum typedefs ($\text{type}~x\langle\overline{\alpha}\rangle = c_1 \mid \ldots \mid c_n$) have no structural counterpart and therefore no analogous rule — sum values reach unification already wearing their $x\langle\overline{\tau}\rangle$ skin via the constructor's typing rule [T-Ctor](#T-Ctor). This is also the only place in unification where typedef-unfolding occurs; the related `comparable` predicate (§T-Cmp) has its own `unfold` helper that does the same job for equality-checking but extends to sums.

<a id="U-ListSugar"></a>

<div markdown="0">
$$\dfrac{
  \text{unify}(\tau_1, \tau_2)
}{
  \text{unify}([\tau_1],\, \texttt{List}\langle\tau_2\rangle)
} \;\textsc{U-ListSugar}$$
</div>

U-ListSugar bridges the type-level alias: $[\tau]$ in source is identical to the prelude $\texttt{List}\langle\tau\rangle$ enum (see §1, "List literals and the :: cons operator"). Both directions are reachable by the symmetry convention. Note that U-ListSugar is a *separate* rule from U-Expand because `List` is a sum typedef (not a record), so the structural-record machinery of U-Expand does not apply; the bridge is hard-coded to the list pair specifically.

U-Borrow auto-derefs $\&\sigma$ only when it appears on the left (the *actual* position — see the argument-order convention at the start of this section). U-Expand applies in both argument orders via the symmetry convention — the implementation handles both $\text{unify}(x\langle\overline{\tau}\rangle, R)$ and $\text{unify}(R, x\langle\overline{\tau}\rangle)$.

<div markdown="0">
$$\textbf{P7}~\text{(Unification).}\quad \text{unify}(\tau_1, \tau_2)~\text{terminates and returns a most general unifier or fails}$$
</div>

### Polymorphism Introduction

Polymorphic schemes are introduced **only** by explicit type-parameter lists on top-level function declarations. The quantifier list is **kind-aware** — each user-named quantifier $X$ ranges over either type variables ($\kappa = \texttt{Type}$) or row variables ($\kappa = \texttt{Row}$):

<div markdown="0">
$$\kappa ::= \texttt{Type} \mid \texttt{Row}$$
</div>

<div markdown="0">
$$\textbf{fn}~\textit{foo}\langle X_1, \ldots, X_n\rangle(\overline{\ell:\tau}) \to \tau_r;\,\rho_q;\,\rho_e \quad\rightsquigarrow\quad \forall X_1{:}\kappa_1 \ldots X_n{:}\kappa_n.\,(\overline{\ell:\tau}) \to \tau_r;\,\rho_q;\,\rho_e$$
</div>

The kind $\kappa_i$ of each $X_i$ is **inferred from $X_i$'s occurrence position** in the function signature. We formalise the inference as the auxiliary $\text{kindOf}(X, \sigma)$, a partial function from a quantifier name and a signature to $\lbrace \texttt{Type}, \texttt{Row} \rbrace$:

<div markdown="0">
$$\text{kindOf}(X, \sigma) = \begin{cases}
\texttt{Type} & \text{if}~\text{occurs}_\tau(X, \sigma)~\text{and not}~\text{occurs}_\rho(X, \sigma) \\
\texttt{Row} & \text{if}~\text{occurs}_\rho(X, \sigma)~\text{and not}~\text{occurs}_\tau(X, \sigma) \\
\text{undefined} & \text{otherwise (unused or kind clash)}
\end{cases}$$
</div>

with the position predicates defined recursively over the signature's structure:

<div markdown="0">
$$\begin{array}{rcl}
\text{occurs}_\tau(X, X) & = & \text{true} \\
\text{occurs}_\tau(X, b) = \text{occurs}_\tau(X, \texttt{intlit}) = \text{occurs}_\tau(X, \texttt{floatlit}) & = & \text{false} \\
\text{occurs}_\tau(X, Y) & = & \text{false} \quad (Y \neq X) \\
\text{occurs}_\tau(X, (\overline{\ell:\tau}) \to \tau_r;\,\rho_q;\,\rho_e) & = & \exists i.\;\text{occurs}_\tau(X, \tau_i) \;\vee\; \text{occurs}_\tau(X, \tau_r) \;\vee \\
& & \text{occurs}_\tau^\rho(X, \rho_q) \;\vee\; \text{occurs}_\tau^\rho(X, \rho_e) \\
\text{occurs}_\tau(X, \%\tau) = \text{occurs}_\tau(X, @\tau) = \text{occurs}_\tau(X, \&\tau) & = & \text{occurs}_\tau(X, \tau) \\
\text{occurs}_\tau(X, [\tau]) = \text{occurs}_\tau(X, [\lvert\tau\rvert]) & = & \text{occurs}_\tau(X, \tau) \\
\text{occurs}_\tau(X, \lbrace \overline{\ell:\tau} \rbrace) = \text{occurs}_\tau(X, x\langle \overline{\tau} \rangle) & = & \exists i.\;\text{occurs}_\tau(X, \tau_i) \\[6pt]
\text{occurs}_\tau^\rho(X, \lbrace \overline{\tau} \rbrace) & = & \exists i.\;\text{occurs}_\tau(X, \tau_i) \\
\text{occurs}_\tau^\rho(X, \lbrace \overline{\tau} \mid Y \rbrace) & = & \exists i.\;\text{occurs}_\tau(X, \tau_i) \\[6pt]
\text{occurs}_\rho(X, \lbrace \overline{\tau} \mid X \rbrace) & = & \text{true} \\
\text{occurs}_\rho(X, \rho)~\text{(other cases)} & = & \text{recurse structurally, surfacing only row-tail occurrences of}~X
\end{array}$$
</div>

In words: $\text{occurs}_\tau$ asks "does $X$ appear at any *type* position (anywhere a τ is expected, including row entries)?" and $\text{occurs}_\rho$ asks "does $X$ appear specifically as a *row tail*?". Their disjoint truth values pin $\kappa$. The clash case (both true) and the unused case (both false) are static errors at [T-Let-PolyFn](#T-Let-PolyFn) — both surface as a malformed quantifier list at the binding site, not at a use site.

The surface syntax `fn <R>(...)` carries no kind annotation; kind inference recovers $\kappa_i$ from the body. This is faithful to the implementation (`convert_ud_to_var` in `src/typecheck/check.nx`), which represents both kinds with the same $\texttt{TyVar}(n)$ constructor; the unifier then learns the kind from the first row/non-row context the variable meets, achieving the same fixpoint as the metatheoretic `kindOf` above.

The $X_i$ are user-named quantifiers (predicative System-F extended with row kind). There is **no implicit generalization**: every let-binding produces a monomorphic scheme via `mono`. The two carve-outs are [T-Let-PolyFn](#T-Let-PolyFn) (the introduction site — fires when the RHS is a **fn** literal with an explicit type-parameter list, generalizing the inferred arrow over $\overline{X_i}$) and [T-Let-Alias](#T-Let-Alias) (the forwarding site — copies an existing polymorphic scheme verbatim when the RHS is a bare polymorphic variable).

<div markdown="0">
$$\text{mono}(\tau) = \forall\emptyset.\,\tau \qquad\text{(monomorphic scheme; empty quantifier list)}$$
</div>

The pattern rules ([P-Var](#P-Var)) and assignment rule ([T-Assign](#T-Assign)) write the equivalent 2-tuple form $(\emptyset,\,\tau)$ for the same monomorphic scheme — both denote $\forall\emptyset.\,\tau$.

`inst` produces a fresh unification variable of the appropriate kind for each quantifier:

<div markdown="0">
$$\text{inst}(\forall X_1{:}\kappa_1 \ldots X_n{:}\kappa_n.\, \tau) = \tau[X_1 := \nu_1, \ldots, X_n := \nu_n]$$
</div>

<div markdown="0">
$$\nu_i = \begin{cases} {?}\beta_i & \text{if}~\kappa_i = \texttt{Type},~{?}\beta_i~\text{fresh type unification variable} \\ {?}r_i & \text{if}~\kappa_i = \texttt{Row},~{?}r_i~\text{fresh row tail variable} \end{cases}$$
</div>

`inst` is used at every variable use site ([T-Var](#T-Var)). When the scheme is monomorphic ($n = 0$), `inst` is the identity and $\tau' = \tau$.

<div markdown="0">
$$\textbf{P8}~\text{(No implicit generalization).}\quad\text{For any binding}~x :^{q} S~\text{introduced by [T-Let](#T-Let) or [T-LetPat](#T-LetPat)},~S = \text{mono}(\tau)~\text{for some}~\tau.$$
</div>

Polymorphic schemes ($\forall\overline{X{:}\kappa}.\,\tau$ with $\overline{X} \neq \emptyset$) enter Γ only via [T-Let-PolyFn](#T-Let-PolyFn) (top-level **fn** declarations) or [T-Let-Alias](#T-Let-Alias) (bare-variable forwarding).

**Worked example (row polymorphism).** The library function

```nexus
fn <R>(f: () -> unit require { Logger | R }) -> unit require { Logger | R } do ...
```

has surface quantifier list $\langle R \rangle$. $R$ appears only in row-tail position ($\lbrace \texttt{Logger} \mid R \rbrace$), so kind inference sets $\kappa_R = \texttt{Row}$, yielding the scheme

<div markdown="0">
$$\forall R{:}\texttt{Row}.\;(f: () \to \texttt{unit};\,\lbrace \texttt{Logger} \mid R \rbrace;\,\lbrace\rbrace) \to \texttt{unit};\,\lbrace \texttt{Logger} \mid R \rbrace;\,\lbrace\rbrace$$
</div>

At a call site, `inst` replaces $R$ with a fresh row unification variable ${?}r$, which then unifies with the caller's residual capability tail by ordinary row unification.

### Pattern Matching

<div markdown="0">
$$\Gamma \vdash p : \tau \Rightarrow \Gamma'$$
</div>

`strip` removes the outermost modality before pattern matching. It peels $\%$ (linear) and $\&$ (borrow) only — it deliberately does **not** peel $@$ (thunk) or $\mathord{\sim}$ (mutable ref). Thunks must be forced explicitly via [T-Force](#T-Force) before destructuring; refs cannot be match scrutinees at all.

<div markdown="0">
$$\text{strip}(\tau) = \begin{cases}
\sigma & \text{if } \tau \in \lbrace \%\sigma,\, \&\sigma \rbrace \\
\tau & \text{otherwise}
\end{cases}$$
</div>

The match expression ([T-Match](#T-Match)) consumes the linear scrutinee via $\otimes$; the pattern rules operate on the stripped type. A scrutinee of type $@\sigma$ therefore fails to match any structural pattern, surfacing a type error that directs the user to write $\textbf{match}\;@x\;\lbrace\ldots\rbrace$ — making the force explicit and ensuring T-Force's linear-consumption obligation is discharged.

<a id="P-Var"></a>

<div markdown="0">
$$\dfrac{
  \mu \in \lbrace \varepsilon,\, \%,\, \mathord{\sim},\, \& \rbrace \qquad
  \tau_b = \text{wrapSigil}(\mu, \text{strip}(\tau)) \qquad
  q = \begin{cases} 1 & \text{if } \text{linear}(\tau_b) \\ \omega & \text{otherwise} \end{cases}
}{
  \Gamma \vdash \mu\,x : \tau \Rightarrow \Gamma,\, x :^{q} (\emptyset, \tau_b)
} \;\textsc{P-Var}$$
</div>

P-Var binds $x$ at $\tau_b = \text{wrapSigil}(\mu, \text{strip}(\tau))$: the pattern's sigil decides the modality of the binding regardless of what the scrutinee's sigil was. The combined effect — `strip` peels the scrutinee's outer modality, `wrapSigil` re-applies the pattern's modality — means $\textbf{let}~\%x = (\%v : \%T)$ binds $x$ at $\%T$, $\textbf{let}~\&y = (v : T)$ binds $y$ at $\&T$ (a borrow-let-pattern, mirroring the let-statement form), and $\textbf{let}~x = (\%v : \%T)$ binds at $\%T$ via wrapSigil's $\mu = \varepsilon$ identity clause. The idempotency of `wrapSigil` (§Statements) ensures a single layer is always present, never two. P-Wild / P-Lit / P-Or / P-Record have no sigil prefix at the pattern root (the surface grammar admits sigils only on variable and constructor patterns); their sub-patterns recurse through P-Var or P-Ctor where sigils may again appear.

<div markdown="0">
$$\dfrac{
  \text{linear}(\tau) \wedge \neg\text{autoDrop}(\tau) \implies \text{error}
}{
  \Gamma \vdash \_ : \tau \Rightarrow \Gamma
} \;\textsc{P-Wild}$$
</div>

<div markdown="0">
$$\dfrac{
  \text{unify}(\tau, \text{typeof}(n))
}{
  \Gamma \vdash n : \tau \Rightarrow \Gamma
} \;\textsc{P-Lit}$$
</div>

<a id="P-Ctor"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \mu \in \lbrace \varepsilon,\, \%,\, \& \rbrace \qquad
  \Gamma(c) = \forall\overline{\alpha}.\,(\overline{\ell : F}) \to \tau' \\[2pt]
  \text{unify}(\text{strip}(\tau),\, \tau'[\overline{\alpha := {?}\beta}]) \qquad
  \lvert\overline{p}\rvert = \lvert\overline{F}\rvert \\[2pt]
  \forall i.\;\Gamma \vdash p_i : F_i[\overline{\alpha := {?}\beta}] \Rightarrow \Gamma_i \\[2pt]
  \biguplus_i (\Gamma_i \setminus \Gamma)~\text{is defined}
  \end{array}
}{
  \Gamma \vdash \mu\,c(\overline{\ell : p}) : \tau \Rightarrow \Gamma \uplus \textstyle\biguplus_i (\Gamma_i \setminus \Gamma)
} \;\textsc{P-Ctor}$$
</div>

Field patterns bind in parallel: each $p_i$ is checked against the same input Γ, and the new bindings $\Gamma_i \setminus \Gamma$ are combined by disjoint union $\uplus$. Disjoint union fails if any two field patterns introduce the same variable name (e.g. $c(a: x, b: x)$), so a single use of $x$ across fields is rejected at the rule level instead of silently shadowing. The pattern's sigil $\mu$ is informational: `strip` already peels the scrutinee's outer modality before the inner-type unify, so $\textbf{let}~\%\texttt{Some}(\textit{val}: x) = e$ types $e$ at $\%\texttt{Option}\langle T \rangle$ and recurses into $\texttt{Option}\langle T \rangle$ for the constructor fields — the recursive sub-patterns then re-attach their own sigils via P-Var.

<a id="P-CtorNullary"></a>

<div markdown="0">
$$\dfrac{
  \mu \in \lbrace \varepsilon,\, \%,\, \& \rbrace \qquad
  \Gamma(c) = \forall\overline{\alpha}.\,\tau' \qquad
  \tau'~\text{is not an arrow type} \qquad
  \text{unify}(\text{strip}(\tau),\, \tau'[\overline{\alpha := {?}\beta}])
}{
  \Gamma \vdash \mu\,c : \tau \Rightarrow \Gamma
} \;\textsc{P-CtorNullary}$$
</div>

P-CtorNullary handles the bare-identifier form of a zero-field constructor, e.g.\ catching $\textbf{exception}~\texttt{MissingMain}$ (declared without a parameter list) via $\textbf{catch}~\texttt{MissingMain} \to \ldots$. The premise $\Gamma(c) = \forall\overline{\alpha}.\,\tau'$ with $\tau'$ a value type (not an arrow) distinguishes the nullary case from the variable pattern [P-Var](#P-Var): P-Var fires only when the identifier is *not* a constructor (the grammar's variable-pattern side-condition). For a sum-type variant `None` with declaration $\textbf{type}~\texttt{Option}\langle T \rangle = \texttt{None} \mathbin{\vert} \texttt{Some}(\textit{val}: T)$, [D-Type-Sum](#D-Type-Sum) installs $\texttt{None} :^{\omega} \forall T.\, \texttt{Option}\langle T \rangle$ in Γ (the zero-field constructor has the named type itself as its scheme, not an arrow), so P-CtorNullary applies. The output Γ is unchanged — nullary constructors bind no field variables.

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \text{distinct}(\overline{\ell}) \qquad
  \forall i.\;\tau_i = \text{fields}(\text{strip}(\tau)).\ell_i \\[2pt]
  \forall i.\;\Gamma \vdash p_i : \tau_i \Rightarrow \Gamma_i \\[2pt]
  \biguplus_i (\Gamma_i \setminus \Gamma)~\text{is defined}
  \end{array}
}{
  \Gamma \vdash \lbrace \overline{\ell : p} \rbrace : \tau \Rightarrow \Gamma \uplus \textstyle\biguplus_i (\Gamma_i \setminus \Gamma)
} \;\textsc{P-Record}$$
</div>

<a id="P-Or"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \Gamma \vdash p_1 : \tau \Rightarrow \Gamma_1 \qquad
  \Gamma \vdash p_2 : \tau \Rightarrow \Gamma_2 \\[2pt]
  \Gamma_1 \setminus \Gamma = \Gamma_2 \setminus \Gamma \quad\text{(both alternatives bind the same names at the same types and usages)}
  \end{array}
}{
  \Gamma \vdash p_1 \mathbin{\vert} p_2 : \tau \Rightarrow \Gamma_1
} \;\textsc{P-Or}$$
</div>

P-Or constrains both alternatives to introduce **identical** binding sets — same names, same types, same usage annotations — so the body that follows the pattern can refer to those bindings unambiguously regardless of which alternative matched. The output environment can be taken from either side ($\Gamma_1$, by convention). For exhaustiveness, an or-pattern $p_1 \mathbin{\vert} p_2$ in matrix row $(p_1 \mathbin{\vert} p_2 :: \overline{r})$ expands to two rows $(p_1 :: \overline{r})$ and $(p_2 :: \overline{r})$ before the standard `spec`/$D$ algorithm runs.

Exhaustiveness is checked via Maranget's pattern matrix algorithm:

<div markdown="0">
$$\dfrac{M = \emptyset}{\text{check}(M, \overline{\tau}) = \text{error}} \;\textsc{Exh-Empty}
\qquad
\dfrac{M \neq \emptyset \qquad \lvert\overline{\tau}\rvert = 0}{\text{check}(M, \overline{\tau}) = \text{ok}} \;\textsc{Exh-Done}$$
</div>

<div markdown="0">
$$\dfrac{
  \text{check}(\text{spec}(M, \texttt{true}), \overline{\tau}') \qquad
  \text{check}(\text{spec}(M, \texttt{false}), \overline{\tau}')
}{
  \text{check}(M, \texttt{bool} :: \overline{\tau}')
} \;\textsc{Exh-Bool}$$
</div>

<a id="Exh-Sum"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \text{variants}(\tau_1) = \overline{c_j(\overline{F_j})} \\[2pt]
  \forall j.\;\text{check}(\text{spec}(M, c_j), \overline{F_j} \mathbin{+\!\!+} \overline{\tau}')
  \end{array}
}{
  \text{check}(M, \tau_1 :: \overline{\tau}')
} \;\textsc{Exh-Sum}$$
</div>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \text{fields}(\tau_1) = \overline{\ell : \sigma} \\[2pt]
  \text{check}(\text{spec}_R(M, \overline{\ell}), \overline{\sigma} \mathbin{+\!\!+} \overline{\tau}')
  \end{array}
}{
  \text{check}(M, \tau_1 :: \overline{\tau}')
} \;\textsc{Exh-Record}$$
</div>

$\text{spec}_R(M, \overline{\ell})$ specializes the matrix for a record scrutinee: rows whose first pattern is $\lbrace \overline{\ell' : p} \rbrace$ contribute $\text{canonicalize}_R(\lbrace \overline{\ell' : p} \rbrace, \overline{\ell})$ prepended to the rest; wildcard-like rows (matching `wild`, defined below) are replicated with $\lvert\overline{\ell}\rvert$ fresh wildcards. The input parameter $\overline{\ell}$ is the declared field-order sequence from $\text{fields}(\tau_1)$ and serves as the canonical position-ordered representation that the matrix algorithm operates over. $\text{canonicalize}_R$ permutes each row's sub-patterns into that declared order so that two rows written with different label orderings (e.g.\ $\lbrace a : x, b : y \rbrace$ vs.\ $\lbrace b : y, a : x \rbrace$) produce identical position-indexed sub-pattern lists; without it, the matrix would treat the two rows as distinct shape templates and the per-column recursive [check](#Exh-Record) calls would receive misaligned types vs.\ patterns. Formally:

<div markdown="0">
$$\text{canonicalize}_R(\lbrace \overline{\ell' : p} \rbrace,\; [\ell_1, \ldots, \ell_k]) = [p_{\pi(1)}, \ldots, p_{\pi(k)}] \quad\text{where}~\pi~\text{is the unique permutation with}~\ell'_{\pi(i)} = \ell_i$$
</div>

Uniqueness of $\pi$ is guaranteed by $\text{distinct}(\overline{\ell'})$ (from [T-Record](#T-Record), applied at pattern parse) and by $\lbrace \overline{\ell'} \rbrace = \lbrace \overline{\ell} \rbrace$ (the pattern's label set must match the declared field set; pattern-typing at [P-Record](#pattern-matching) rejects mismatches).

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \tau_1 \notin \lbrace \texttt{bool} \rbrace \cup \lbrace x\langle \overline{\tau} \rangle \mid \text{variants}(x) \neq \emptyset \rbrace \cup \lbrace \lbrace \overline{\ell : \sigma} \rbrace \rbrace \\[2pt]
  \quad\text{(}\tau_1~\text{has no finite enumerable surface — not}~\texttt{bool}\text{, not a sum, not a record)} \\[2pt]
  D = \lbrace\, \overline{r} \mid (p :: \overline{r}) \in M,\; \text{wild}(p) \,\rbrace \qquad
  \text{check}(D, \overline{\tau}')
  \end{array}
}{
  \text{check}(M, \tau_1 :: \overline{\tau}')
} \;\textsc{Exh-Default}$$
</div>

Exh-Default applies to head types that lack a complete-constructor surface — e.g.\ `i64`, `string`, `char`, `f64`, an array $[\lvert\sigma\rvert]$, or any other type whose value space is not exhaustible by a finite case split. The premise's first clause syntactically forbids the rule from applying when $\tau_1$ would have been handled by [Exh-Bool](#Exh-Bool) ($\tau_1 = \texttt{bool}$), [Exh-Sum](#Exh-Sum) ($\tau_1 = x\langle \overline{\tau} \rangle$ with a non-empty $\text{variants}(x)$, including `Exn`), or [Exh-Record](#Exh-Record) ($\tau_1$ is a record type). Without this restriction Exh-Sum and Exh-Default would share the conclusion $\text{check}(M, \tau_1 :: \overline{\tau}')$ for sum-typed scrutinees, and a derivation that chose Exh-Default first against a matrix $M$ of only constructor patterns (no wildcards) would compute $D = \emptyset$ and falsely conclude inexhaustive via [Exh-Empty](#Exh-Empty). The premise canonicalises rule choice: any finite-enumerable head type must go through its dedicated rule. For an opaque sum visible only outside its defining module, $\text{variants}(x) = \emptyset$ (see [D-Type-Sum-Opaque](#D-Type-Sum-Opaque)) and Exh-Default does apply — matching the impl's behaviour where an opaque sum is treated as wildcard-only outside its module.

<div markdown="0">
$$\text{wild}(p) = (p = \_) \;\vee\; (p~\text{is a variable pattern}~x)$$
</div>

A variable pattern $x$ binds the scrutinee under name $x$; from an exhaustiveness standpoint it succeeds against every value, exactly like $\_$. Treating $x$ as wildcard-like in the matrix algorithm restores Maranget's invariant that $\textbf{match}~e~\lbrace x \to \ldots \rbrace$ is exhaustive — which is also required for [T-LetPat](#T-LetPat) to admit single-variable patterns.

<div markdown="0">
$$\text{spec}(M, c) = \lbrace\, \text{canonicalize}_c(c(\overline{\ell' : p'})) \mathbin{+\!\!+} \overline{r} \mid (c(\overline{\ell' : p'}) :: \overline{r}) \in M \,\rbrace \;\cup\; \lbrace\, \underbrace{\_,\ldots,\_}_{a(c)} \mathbin{+\!\!+} \overline{r} \mid (p :: \overline{r}) \in M,\; \text{wild}(p) \,\rbrace$$
</div>

where $a(c)$ is the arity of constructor $c$. Rows whose first pattern is the labelled constructor application $c(\overline{\ell' : p'})$ contribute the *canonicalized* sub-pattern list prepended to the rest; wildcard-like rows (including variable patterns) are replicated with $a(c)$ fresh wildcards.

Constructor sub-patterns carry labels in Nexus (e.g.\ $\texttt{Some}(\textit{val} : x)$, $\texttt{Pair}(\textit{left} : l,\, \textit{right} : r)$). The label-order in the surface pattern need not match the order declared at [D-Type-Sum](#D-Type-Sum) — the surface allows the same constructor to be written with any permutation of its labels. $\text{canonicalize}_c$ permutes each row's sub-pattern list into the constructor's declared field order so that the matrix algorithm operates over a fixed position-ordered representation:

<div markdown="0">
$$\text{canonicalize}_c(c(\overline{\ell' : p'})) = [p'_{\pi(1)}, \ldots, p'_{\pi(a(c))}] \quad\text{where the declared field order of}~c~\text{is}~[\ell_1, \ldots, \ell_{a(c)}]~\text{and}~\pi~\text{is the unique permutation with}~\ell'_{\pi(i)} = \ell_i$$
</div>

Uniqueness of $\pi$ follows from the constructor declaration providing a label-set without duplicates and from [P-Ctor](#P-Ctor)'s pattern-typing requiring $\lbrace \overline{\ell'} \rbrace = \lbrace \overline{\ell} \rbrace$ on every constructor pattern. Without this canonicalization step, two semantically equivalent constructor patterns written in different label orders would produce distinct rows in $\text{spec}(M, c)$ — the per-position recursive [check](#Exh-Sum) calls would then see type-position $i$ unified against sub-pattern $\ell'_i$ in one row but $\ell_i$ in the next, breaking Maranget's positional invariant. The same ideology backs [T-App](#T-App)'s label-permutation premise — labels, not positions, are the user-facing identity, and canonicalization happens at the rule boundary.

<div markdown="0">
$$\textbf{P6}~\text{(Exhaustiveness).}\quad \text{check}(M, [\tau]) = \text{ok} \implies \forall v : \tau.\;\exists i.\; v \in \text{match}(p_i)$$
</div>

<a id="redundancy"></a>

**Redundancy (per-arm usefulness).** Beyond exhaustiveness, the type system rejects programs containing an *unreachable* match arm — a row that no run-time value can reach because earlier rows already cover its shape. Maranget's $\text{useful}(M, \overline{p})$ predicate decides "row $\overline{p}$ matches at least one value not already matched by $M$"; the impl invokes it row-by-row against the prefix matrix and reports the first row for which $\text{useful}(M_{<i}, [p_i]) = \text{false}$.

<div markdown="0">
$$\textbf{P6'}~\text{(No redundant arms).}\quad \forall i.\;\text{useful}(\{[p_1], \ldots, [p_{i-1}]\},\, [p_i]) = \text{true}$$
</div>

The redundancy scan operates on the same `spec`/$D$ machinery as exhaustiveness, but switches the constructor-signature classification at one point: for a head type $\tau_1$, the signature is $\text{SigFinite}(\overline{c_j})$ when $\text{variants}(\tau_1)$ is a *closed* set (records, ordinary user-defined sums, `bool`) and `SigInfinite` otherwise (infinite-domain primitives like `i64`, `string`; and crucially the open-extensible `Exn`). The `Exn` classification matters because [D-Exception](#D-Exception) makes $\text{variants}(\texttt{Exn})$ *grow* across modules — a fresh **exception** declaration in any reachable module extends the set. Treating it as `SigFinite` at any single use site would let `useful`'s "all constructors present in $M$" branch trivially succeed against an empty closed-variant list at the catch-all carve-out site (since the catch-all + main-wrap pass guarantees coverage), classifying every wildcard or variable arm following a concrete-constructor arm as redundant. Instead, `Exn` is surfaced as `SigInfinite`: the wildcard-head usefulness check falls through to $\text{default}(M)$, which preserves wildcard rows, and only genuine duplicates (a second arm whose $\text{spec}(M_{<i}, c)$ specialisation is already covered) are flagged. See `src/typecheck/exhaustive.nx::column_signature` (nexus-t9cl.19). P6' applies symmetrically to [T-Match](#T-Match) and [T-TryCatch](#T-TryCatch).

### Expressions

<div markdown="0">
$$\Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_e$$
</div>

All linear bindings in Γ must be consumed by the derivation; $\otimes$ distributes them among sub-expressions. $\rho_e$ ($\mathbin{!}$) is the effect produced. Literal rules carry the side-condition $\text{pure}(\Gamma)$, defined below, to make "no unspent linears at a leaf" a checkable premise rather than a narrative obligation:

<div markdown="0">
$$\text{pure}(\Gamma) = \forall x :^{q} S \in \Gamma.\;q = \omega$$
</div>

<a id="T-IntLit"></a>
<a id="T-FloatLit"></a>

<div markdown="0">
$$\dfrac{\text{pure}(\Gamma)}{\Gamma;\, \rho_q \vdash_e n : \texttt{intlit} \mathbin{!} \lbrace\rbrace} \;\textsc{T-IntLit}
\qquad
\dfrac{\text{pure}(\Gamma)}{\Gamma;\, \rho_q \vdash_e f : \texttt{floatlit} \mathbin{!} \lbrace\rbrace} \;\textsc{T-FloatLit}$$
</div>

<div markdown="0">
$$\dfrac{\text{pure}(\Gamma)}{\Gamma;\, \rho_q \vdash_e b : \texttt{bool} \mathbin{!} \lbrace\rbrace} \;\textsc{T-Bool}
\qquad
\dfrac{\text{pure}(\Gamma)}{\Gamma;\, \rho_q \vdash_e ch : \texttt{char} \mathbin{!} \lbrace\rbrace} \;\textsc{T-Char}$$
</div>

<div markdown="0">
$$\dfrac{\text{pure}(\Gamma)}{\Gamma;\, \rho_q \vdash_e s : \texttt{string} \mathbin{!} \lbrace\rbrace} \;\textsc{T-Str}
\qquad
\dfrac{\text{pure}(\Gamma)}{\Gamma;\, \rho_q \vdash_e () : \texttt{unit} \mathbin{!} \lbrace\rbrace} \;\textsc{T-Unit}$$
</div>

<a id="T-Var"></a>

<div markdown="0">
$$\dfrac{
  \mu \in \lbrace \varepsilon,\, \% \rbrace \qquad
  x :^{q} \forall\overline{\alpha}.\,\tau \in \Gamma \qquad
  \tau' = \text{inst}(\forall\overline{\alpha}.\,\tau) \qquad
  \text{pure}(\Gamma \setminus \lbrace x \rbrace)
}{
  \Gamma;\, \rho_q \vdash_e \mu\,x : \tau' \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Var}$$
</div>

If $q = 1$, the binding $x$ is consumed by this use. T-Var covers both bare $x$ ($\mu = \varepsilon$) and the linear-decorated $\%x$ ($\mu = \%$): the $\%$ sigil at the binding site already asserts linearity on the scheme, and the use site reads that off the binding rather than re-wrapping. The resulting $\tau'$ is whatever scheme $\Gamma(x)$ carries — a $\%\sigma$ binding yields $\tau' = \%\sigma$; dropping the use-site sigil avoids the redundant $\%\%\sigma$ shape. §Modalities (line 89) admits $\mu \in \lbrace \varepsilon, \%, \mathord{\sim} \rbrace$ for expression-position variable references; the $\mathord{\sim}$ case routes through [T-Deref](#T-Deref) (with its deref-read semantics), while $\varepsilon$ and $\%$ both fold into T-Var. Remaining sigil forms each have a dedicated rule: [T-Borrow](#T-Borrow) for $\&x$, [T-Force](#T-Force) for $@x$ (subsuming $@e$ for any expression), and [T-Deref](#T-Deref) for $\mathord{\sim}x$.

<a id="T-Deref"></a>

<div markdown="0">
$$\dfrac{
  x :^{\omega} \forall\overline{\alpha}.\,\tau \in \Gamma \qquad
  \tau' = \text{inst}(\forall\overline{\alpha}.\,\tau) \qquad
  \tau' = \mathord{\sim}\sigma \qquad
  \text{pure}(\Gamma \setminus \lbrace x \rbrace)
}{
  \Gamma;\, \rho_q \vdash_e \mathord{\sim}x : \sigma \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Deref}$$
</div>

T-Deref reads through a mutable reference cell. The binding is not consumed (refs are $q = \omega$ — matching [T-Assign](#T-Assign)'s precondition $x :^\omega (\emptyset, \mathord{\sim}\tau)$). Mirrors [T-Borrow](#T-Borrow)'s structure: variable-only, no row effect, instantiation against the looked-up scheme.

To allow functions with fewer capabilities/effects to be called in a context with more (row subsumption in [T-App](#T-App)), we introduce `open`:

<div markdown="0">
$$\text{open}(\rho) = \begin{cases}
\lbrace \overline{\tau} \mid {?}r \rbrace & \text{if } \rho = \lbrace \overline{\tau} \rbrace,\; {?}r~\text{fresh} \\
\rho & \text{if } \rho = \lbrace \overline{\tau} \mid {?}r \rbrace
\end{cases}$$
</div>

<a id="T-App"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{c}
  B = \lbrace x \in \text{dom}(\Gamma) \mid \Gamma(x) = (1, \_) \wedge \exists i.\; e_i = \&x \wedge \forall j.\; x \in \text{fv}(e_j) \implies e_j = \&x \rbrace \\[2pt]
  \Gamma \mid_B~\text{is shared as}~\omega~\text{across}~\Gamma_f, \Gamma_1, \ldots, \Gamma_k \quad\text{(borrow-only linears coexist; see below)} \\[2pt]
  (\Gamma \setminus B) = \Gamma_f \otimes \Gamma_1 \otimes \ldots \otimes \Gamma_k \\[2pt]
  \Gamma_f;\, \rho_q \vdash_e f : \tau_f \mathbin{!} \rho_f \\[2pt]
  \text{stripCall}(\tau_f) = (\overline{\ell' : P}) \to \tau_r;\, \rho_q';\, \rho_e' \\[2pt]
  \lbrace \overline{\ell} \rbrace = \lbrace \overline{\ell'} \rbrace \quad\text{(label sets match; no duplicates; full coverage)} \\[2pt]
  \pi: \lbrace 1,\ldots,k \rbrace \to \lbrace 1,\ldots,k \rbrace,\; \ell_i = \ell'_{\pi(i)} \quad\text{(unique permutation by label name)} \\[2pt]
  \forall i.\;(\Gamma_i \cup \Gamma\mid_B);\, \rho_q \vdash_e^{\text{arg}} e_i \mathrel{\Updownarrow} P_{\pi(i)} : \tau_i \mathbin{!} \rho_i \\[2pt]
  \forall i.\;\begin{cases} \text{unify}(\tau_i, \text{strip}(P_{\pi(i)})) & \text{if } P_{\pi(i)} = \%\sigma \wedge \neg\text{linear}(\tau_i) \wedge \tau_i \neq \&\sigma' \\ \text{unify}(\tau_i, P_{\pi(i)}) & \text{otherwise} \end{cases} \\[2pt]
  \text{unify}(\rho_q, \text{open}(\rho_q'))
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e f(\overline{\ell : e}) : \tau_r \mathbin{!} \rho_e' \cup \rho_f \cup \textstyle\bigcup_i \rho_i
} \;\textsc{T-App}$$
</div>

<div markdown="0">
$$\text{stripCall}(\tau) = \begin{cases}
\sigma & \text{if } \tau \in \lbrace \%\sigma,\, @\sigma \rbrace \\
\tau & \text{otherwise}
\end{cases}$$
</div>

`stripCall` peels the outermost closure modality before extracting the arrow shape. It handles two cases:

- $\tau_f = \%\tau_\to$: a lambda that captured linear bindings is given a $\%$ wrapper by T-Lambda's closure-linearization premise ($\tau_\to^\star = \%\tau_\to$ when $\Gamma_\text{cap} \neq \emptyset$). The wrapper records that the closure is one-shot — its linear captures may be consumed at most once. Calling such a closure consumes the $\%\tau_\to$ value (via T-Var with $q = 1$) and delegates to the inner arrow.
- $\tau_f = @\tau_\to$: a thunk whose payload is itself a function. The call implicitly forces the thunk — the $@$ wrapper is discarded and the inner arrow is used directly. This is equivalent to writing $(@f)(\overline{\ell:e})$ with an explicit [T-Force](#T-Force) step, but the surface syntax allows the parentheses to be omitted. The thunk is consumed by the implicit force ($q = 1$ on the $@\tau_\to$ binding), so a second call to the same $f$ would violate linearity.

`stripCall` deliberately does **not** peel $\&$ or $\mathord{\sim}$: a borrow $\&\tau_\to$ or mutable-ref $\mathord{\sim}\tau_\to$ in the callee position is a type error — the caller does not own the closure and cannot invoke it. Contrast with the pattern-matching `strip`, which peels $\%$ and $\&$ (borrows are valid scrutinees) but not $@$.

The caller's argument labels $\overline{\ell}$ are matched against the callee's parameter labels $\overline{\ell'}$ **by name**, not by position. The permutation $\pi$ aligns the caller's $i$-th argument to the callee's $\pi(i)$-th parameter so that $\ell_i = \ell'_{\pi(i)}$; both directions of the label-set equality must hold (every callee parameter is supplied, no extra caller labels). The permutation is unique because labels are required to be distinct on each side (the surface parser rejects duplicate-label calls and parameter lists). This formalises the *order-independent labeled arguments* guarantee from [semantics.md](../semantics) §Label Order Independence — `f(b: 2, a: 1)` and `f(a: 1, b: 2)` produce the same derivation up to $\pi$.

The weakening condition is explicit: when $P_{\pi(i)} = \%\sigma$ and $\tau_i$ is not linear, unification targets the inner type σ (stripping the $\%$ wrapper). This does not apply to other linear forms like $@\sigma$. The extra side condition $\tau_i \neq \&\sigma'$ rejects **borrow-to-ownership smuggling**: $\text{linear}(\&\sigma')$ is `false` by §Linearity (borrows are not recursed into), so without the carve-out a $\&\texttt{ByteBuffer}$ argument would satisfy a $\%\texttt{ByteBuffer}$ parameter via weakening — handing the callee linear-owner privileges over a value the caller still holds. The weakening's intent is "a non-linear *value* can substitute for a linear parameter slot the callee never consumes"; a borrow is a non-consuming *view* of a still-linear owner, not a non-linear value. Argument-position borrows of linear targets must go through the dedicated [T-App-BorrowLin](#T-App) path (which only fires for $P = \&\sigma$, never for $P = \%\sigma$).

**Argument-position typing $\vdash_e^{\text{arg}}\,e \mathrel{\Updownarrow} P$.** Most arguments are typed by ordinary expression typing $\vdash_e$, which then unifies $\tau_i$ against $P_{\pi(i)}$. The carve-out exists for **linear borrows**: when the argument is syntactically $\&x$ and the parameter is shaped $\&\sigma$, the argument is admitted even if $x$ is a linear binding ($x :^1 \in \Gamma_i$). The expression $\&x$ alone is rejected by [T-Borrow](#T-Borrow)'s $x :^{\omega}$ premise — outside an argument position, a borrow of a linear binding would create a long-lived $\&\sigma$ value whose target persists past the use-once obligation. In argument position, the borrow is *discharged on call return*: the callee uses $\&\sigma$ during its body, the call's result is the callee's return type (no borrow leakage), and the linear target $x$ survives the call unconsumed. Formally:

<div markdown="0">
$$\dfrac{
  e = \&x \quad x :^1 \forall\overline{\alpha}.\,\tau \in \Gamma \quad \tau' = \text{inst}(\forall\overline{\alpha}.\,\tau) \quad P = \&\sigma \quad \text{unify}(\text{stripBorrow}(\tau'), \sigma)
}{
  \Gamma;\, \rho_q \vdash_e^{\text{arg}} \&x \mathrel{\Updownarrow} \&\sigma : \&\sigma \mathbin{!} \lbrace\rbrace
} \;\textsc{T-App-BorrowLin}$$
</div>

<div markdown="0">
$$\dfrac{
  e~\text{not in T-App-BorrowLin shape, or}~P~\text{not}~\&\sigma \quad \Gamma;\,\rho_q \vdash_e e : \tau \mathbin{!} \rho
}{
  \Gamma;\, \rho_q \vdash_e^{\text{arg}} e \mathrel{\Updownarrow} P : \tau \mathbin{!} \rho
} \;\textsc{T-App-ArgDefault}$$
</div>

T-App-BorrowLin does not consume the linear target ($x$ remains in $\Gamma_i$ after the borrow); T-App-ArgDefault falls through to the ordinary expression-typing path. The carve-out is **call-site syntactic**: only when the argument literally has the form $\&x$ does it apply — `f(p: g(x: &y))` does *not* benefit because the inner $g(\ldots)$ would type the borrow through ordinary T-Borrow first. This mirrors the impl in `src/typecheck/infer.nx::infer_call`'s argument-shape special-case.

**Borrow-set $B$ and same-linear multi-borrow.** The T-App premise pre-extracts the set $B$ of linear bindings $x$ that appear in at least one argument as $\&x$ **and** appear in **no** argument under any other shape (no consuming use of $x$ anywhere in $\overline{e}$), and shares those bindings across **all** sub-environments as if they were ω (rather than fragmenting them via $\otimes$). This is what makes `f(p: &x, q: &x)` type-check when $x$ is linear: a naive $\otimes$-split would assign $x$ to exactly one $\Gamma_i$ (say $\Gamma_1$), and the second $\&x$ argument's T-App-BorrowLin premise $x :^1 {\ldots} \in \Gamma_2$ would fail. Sharing $\Gamma\mid_B$ as ω is sound because **borrows do not consume**: every leaf reference to $x$ in argument position routes through T-App-BorrowLin (or its `&x.\ell` projection variants), each of which leaves $x$ in its sub-environment unconsumed. The linearity invariant for $x$ is preserved overall — $x$ still has exactly one ultimate consumer (after the call), namely whatever later statement consumes it; the call itself contributes zero consumptions for any $x \in B$. The element-of premise of T-App-BorrowLin then succeeds in every $\Gamma_i$ that holds an argument $\&x$, since $\Gamma\mid_B$ is unioned into each. Outside argument position, $x$ remains linear and the ordinary $\otimes$-split still applies (e.g. `let y = x in f(&x)` is still rejected if $x$ has been consumed by the `let`). The impl correlate is `src/typecheck/linearity.nx`'s `Borrow` case returning the input state unchanged: borrows leave the live set intact, so repeated borrows of the same linear inside one call do not interfere.

**Capability-row enforcement is deferred** (nexus-mqin.14): the T-App premise $\text{unify}(\rho_q, \text{open}(\rho_q'))$ and the corresponding $\rho_q$ slot on T-Lambda's arrow type are part of the formal rule, but the self-host typechecker constructs lambda arrows with empty $\rho_q'$ and discards the callee's $\rho_q'$ at call sites. Capability admission is currently enforced by a downstream pass on MIR rather than by typecheck. The spec rule remains the reference target; closing the gap is tracked by mqin.14 (impl) — symmetric to how throws-row enforcement was tightened in mqin.1.1.

`selectInt` and `selectFloat` resolve operand types. Integer and float operators are separate ($+$ vs $+.$); they cannot mix. "$—$" = type error (no implicit coercion).

<div markdown="0">
$$\text{selectInt}: \quad
\begin{array}{c|ccc}
 & \texttt{intlit} & \texttt{i32} & \texttt{i64} \\
\hline
\texttt{intlit} & \texttt{i64} & \texttt{i32} & \texttt{i64} \\
\texttt{i32} & \texttt{i32} & \texttt{i32} & — \\
\texttt{i64} & \texttt{i64} & — & \texttt{i64}
\end{array}
$$
</div>

<div markdown="0">
$$\text{selectFloat}: \quad
\begin{array}{c|ccc}
 & \texttt{floatlit} & \texttt{f32} & \texttt{f64} \\
\hline
\texttt{floatlit} & \texttt{f64} & \texttt{f32} & \texttt{f64} \\
\texttt{f32} & \texttt{f32} & \texttt{f32} & — \\
\texttt{f64} & \texttt{f64} & — & \texttt{f64}
\end{array}$$
</div>

<a id="T-ArithInt"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \Gamma = \Gamma_1 \otimes \Gamma_2 \\[2pt]
  \Gamma_1;\, \rho_q \vdash_e e_1 : \tau_1 \mathbin{!} \rho_1 \qquad
  \Gamma_2;\, \rho_q \vdash_e e_2 : \tau_2 \mathbin{!} \rho_2 \\[2pt]
  \tau = \text{selectInt}(\tau_1, \tau_2) \qquad
  \text{unify}(\tau_1, \tau) \qquad
  \text{unify}(\tau_2, \tau)
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e e_1 \oplus e_2 : \tau \mathbin{!} \rho_1 \cup \rho_2
} \;\textsc{T-ArithInt}$$
</div>

<a id="T-ArithFloat"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \Gamma = \Gamma_1 \otimes \Gamma_2 \\[2pt]
  \Gamma_1;\, \rho_q \vdash_e e_1 : \tau_1 \mathbin{!} \rho_1 \qquad
  \Gamma_2;\, \rho_q \vdash_e e_2 : \tau_2 \mathbin{!} \rho_2 \\[2pt]
  \tau = \text{selectFloat}(\tau_1, \tau_2) \qquad
  \text{unify}(\tau_1, \tau) \qquad
  \text{unify}(\tau_2, \tau)
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e e_1 \oplus_f e_2 : \tau \mathbin{!} \rho_1 \cup \rho_2
} \;\textsc{T-ArithFloat}$$
</div>

Unresolved type variables (${?}\alpha$) are treated as `intlit` in `selectInt` and as `floatlit` in `selectFloat`.

The $\oplus$ in [T-ArithInt](#T-ArithInt) ranges over the integer arithmetic, bitwise, and shift operators: $\oplus \in \lbrace +,\, -,\, *,\, /,\, \%,\, \mathbin{\\&},\, \mathbin{\vert},\, \mathbin{\hat{}},\, \ll,\, \gg \rbrace$. Float operators $\oplus_f \in \lbrace +.,\, -.,\, *.,\, /. \rbrace$ use `selectFloat` in [T-ArithFloat](#T-ArithFloat). Integer and float operators are syntactically distinct (`+` vs `+.`) and cannot mix.

<a id="T-Cmp"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \Gamma = \Gamma_1 \otimes \Gamma_2 \\[2pt]
  \Gamma_1;\, \rho_q \vdash_e e_1 : \tau_1 \mathbin{!} \rho_1 \qquad
  \Gamma_2;\, \rho_q \vdash_e e_2 : \tau_2 \mathbin{!} \rho_2 \\[2pt]
  \text{unify}(\tau_1, \tau_2) \qquad
  \text{comparable}(\tau_1)
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e e_1 \odot e_2 : \texttt{bool} \mathbin{!} \rho_1 \cup \rho_2
} \;\textsc{T-Cmp}$$
</div>

$\odot$ ranges over comparison operators $\lbrace ==,\, !=,\, <,\, \leq,\, >,\, \geq \rbrace$. Both operands must unify (e.g. both numeric, both strings, both chars); the result is always `bool`. Equality on records and ADTs reduces structurally, requiring the operand types to match. The `comparable` predicate excludes types whose runtime equality is undefined:

<div markdown="0">
$$\text{comparable}(\tau) \;=\; \text{comparable}'(\tau, \emptyset)$$
</div>

<div markdown="0">
$$\text{comparable}'(\tau, V) = \begin{cases}
\text{true} & \text{if}~\tau \in \lbrace b,\, \texttt{intlit},\, \texttt{floatlit} \rbrace \\
\text{true} & \text{if}~\tau = \lbrace \overline{\ell : \sigma} \rbrace \wedge \forall i.\;\text{comparable}'(\sigma_i, V) \\
\text{true} & \text{if}~\tau = [\sigma] \wedge \text{comparable}'(\sigma, V) \\
\text{false} & \text{if}~\tau = \%\sigma \;\text{(linear)} \\
\text{false} & \text{if}~\tau~\text{is an arrow type, handler value,}~\mathord{\sim}\sigma,~\&\sigma,~@\sigma,~\text{or}~[\lvert\sigma\rvert] \\
\text{false} & \text{if}~\tau = x\langle\overline{\sigma}\rangle \wedge x \in V \quad (\text{cycle: minimum fixpoint}) \\
\text{comparable}'(\text{unfold}(x\langle\overline{\sigma}\rangle), V \cup \lbrace x \rbrace) & \text{if}~\tau = x\langle\overline{\sigma}\rangle \wedge x \notin V \\
\text{false} & \text{if}~\tau = \alpha~\text{or}~?\alpha \quad (\text{rigid quantifier / unification var})
\end{cases}$$
</div>

where the named-type recursion unfolds the typedef body and substitutes type arguments:

<div markdown="0">
$$\text{unfold}(x\langle\overline{\sigma}\rangle) = \begin{cases}
\lbrace \overline{\ell : F[\overline{\alpha := \sigma}]} \rbrace & \text{if}~\text{typedef}(x) = \forall \overline{\alpha}.\,\lbrace \overline{\ell : F} \rbrace~\text{(record)} \\
c_1 \mathbin{\vert} \ldots \mathbin{\vert} c_n~\text{with payload types}~\overline{F_i[\overline{\alpha := \sigma}]} & \text{if}~\text{typedef}(x)~\text{is a sum, and}~x~\text{is not opaque (or we are in its defining module)} \\
\text{opaque} & \text{if}~x~\text{is opaque and we are outside its defining module}
\end{cases}$$
</div>

A **sum type** is comparable iff every variant's payload-field types are comparable (a sum's value-equality reduces to constructor-tag equality plus payload equality). An **opaque type** outside its defining module unfolds to `opaque`, which makes $\text{comparable}'$ return `false` — value-equality cannot be defined externally because the constructors aren't visible. Inside the defining module, opaque types are treated like ordinary sum types.

Linear types ($\%\sigma$), functions, handlers, mutable refs ($\mathord{\sim}\sigma$), borrows ($\&\sigma$), thunks ($@\sigma$), and arrays ($[\lvert\,\sigma\,\rvert]$) have no defined value-equality at runtime; comparing them is a type error. (Identity comparison on these would be an explicit operator, not $==$.) The cycle-guarded fixpoint mirrors `linear` / `autoDrop`: a self-referential type whose recursion path has no inherently-incomparable field (e.g.\ a $\textbf{type}~\texttt{Tree}\langle T \rangle = \texttt{Leaf} \mathbin{\vert} \texttt{Node}(\ldots, \textit{left}: \texttt{Tree}\langle T \rangle, \ldots)$) is comparable iff $T$ is.

**Generic equality is not expressible.** Rigid-quantifier rejection — $\text{comparable}'(\alpha) = \text{false}$ — rules out polymorphic equality functions: a body that wants to compare two values of type $T$ inside $\textbf{fn}~\langle T\rangle\,(a: T, b: T) \to \texttt{bool}$ has no derivation, because T-Cmp's $\text{comparable}(T)$ premise fails at the definition site even when every actual instantiation would be comparable. Conservative rejection is intentional here — there is no constraint-polymorphism mechanism (no `where comparable T` clause), so admitting the body would let a caller specialise $T$ to a linear / function / handler / array type and then ask for value-equality on values that have none. As a standard-library consequence, generic equality functions over user-defined containers (e.g.\ `eq<T>(a: List<T>, b: List<T>) -> bool`, `Set<T>.member<T>(s: Set<T>, x: T) -> bool`) cannot be written in Nexus. Common workarounds:

- Move the equality op into a stdlib **external** that compiles to a runtime-side per-monomorphisation specialisation (the route stdlib's `==` uses for concrete types).
- Take a comparator parameter `eq: fn (a: T, b: T) -> bool` and let the caller supply equality.
- Specialise the container at concrete types (`type IntSet = Set(repr: [i64])`, `eq_int_set: (a: IntSet, b: IntSet) -> bool`).

A future constraint-polymorphism extension (where-clauses, type-class style) would relax this — see the `comparable` predicate's role in §T-Cmp as the natural attachment point.

<a id="T-Logic"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \Gamma = \Gamma_1 \otimes \Gamma_2 \\[2pt]
  \Gamma_1;\, \rho_q \vdash_e e_1 : \tau_1 \mathbin{!} \rho_1 \qquad
  \Gamma_2;\, \rho_q \vdash_e e_2 : \tau_2 \mathbin{!} \rho_2 \\[2pt]
  \text{unify}(\tau_1, \texttt{bool}) \qquad
  \text{unify}(\tau_2, \texttt{bool})
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e e_1 \boxdot e_2 : \texttt{bool} \mathbin{!} \rho_1 \cup \rho_2
} \;\textsc{T-Logic}$$
</div>

$\boxdot \in \lbrace \mathbin{\\&\\&},\, \mathbin{\vert\vert} \rbrace$. Note that the right-hand row $\rho_2$ joins unconditionally — this is **not** short-circuit-aware effect tracking; if you need pure short-circuit semantics, write the equivalent **if**.

<a id="T-Concat"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \Gamma = \Gamma_1 \otimes \Gamma_2 \\[2pt]
  \Gamma_1;\, \rho_q \vdash_e e_1 : \tau_1 \mathbin{!} \rho_1 \qquad
  \Gamma_2;\, \rho_q \vdash_e e_2 : \tau_2 \mathbin{!} \rho_2 \\[2pt]
  \text{unify}(\tau_1, \texttt{string}) \qquad
  \text{unify}(\tau_2, \texttt{string})
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e e_1 \mathbin{+\\!+} e_2 : \texttt{string} \mathbin{!} \rho_1 \cup \rho_2
} \;\textsc{T-Concat}$$
</div>

To unify the result types of multi-branch expressions ([T-If](#T-If), [T-Match](#T-Match)), we introduce `tail`, which extracts the type produced by the last statement in a sequence, and `branchType`, which folds the per-branch tails into the conclusion type σ.

<div markdown="0">
$$\text{tail}(\overline{s}) = \begin{cases} \bot & \text{if last statement is one of:} \\
& \quad \textbf{return},\; \textbf{throw}~e\;(\text{as expression statement}),\; \textbf{let}~\mu\,x = \textbf{throw}~e',\; \textbf{let}~p = e~\text{with}~\text{diverges}(e), \\
& \quad \textbf{if}~e_c~\textbf{then}~\overline{s_1}~\textbf{else}~\overline{s_2}~\text{(as expression statement) with}~\text{tail}(\overline{s_1}) = \bot \wedge \text{tail}(\overline{s_2}) = \bot, \\
& \quad \textbf{match}~e~\lbrace \overline{p_i \to s_i} \rbrace~\text{(as expression statement) with}~\forall i.\;\text{tail}(\overline{s_i}) = \bot \\
\tau & \text{if last statement is an expression of type } \tau~\text{(non-divergent)} \\
\texttt{unit} & \text{otherwise (} \textbf{let},\; \mathord{\sim}x \leftarrow e,\; \textbf{inject},\; \textbf{try}\text{-}\textbf{catch},\; \textbf{while}\text{)} \end{cases}$$
</div>

<div markdown="0">
$$\text{branchType}(\overline{s_1}, \ldots, \overline{s_n}) = \begin{cases}
{?}\alpha~(\text{fresh}) & \text{if } \forall i.\;\text{tail}(\overline{s_i}) = \bot \\
\tau & \text{otherwise, where } \tau~\text{is any non-}\bot~\text{tail and } \forall i.\;\text{tail}(\overline{s_i}) \in \lbrace \bot, \tau \rbrace
\end{cases}$$
</div>

The "otherwise" case is well-defined because the per-branch unification premises in [T-If](#T-If) and [T-Match](#T-Match) require all non-$\bot$ tails to be pairwise-unified before `branchType` is applied: every non-$\bot$ tail collapses to the same τ, so picking "any" is canonical. Divergence propagates through a binding whose RHS is a **throw**: the binding never produces a value, so the arm should not be forced to unify against a concrete type. Without this case, $\textbf{match}~e~\lbrace A \to \textbf{throw}~X;\; B \to \textbf{let}~\_ = \textbf{throw}~Y \rbrace$ would have $\sigma = \texttt{unit}$ (only the B arm survives the $\bot$ filter), pinning the whole match's type spuriously.

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \Gamma = \Gamma_c \otimes \Gamma_b \\[2pt]
  \Gamma_c;\, \rho_q \vdash_e e_c : \tau_c \mathbin{!} \rho_c \qquad
  \text{unify}(\tau_c, \texttt{bool}) \\[2pt]
  \Gamma_b;\, \rho_q;\, \tau_r \vdash_s \overline{s_1} : \Gamma_1' \mathbin{!} \rho_1 \\[2pt]
  \Gamma_b;\, \rho_q;\, \tau_r \vdash_s \overline{s_2} : \Gamma_2' \mathbin{!} \rho_2 \\[2pt]
  \text{tail}(\overline{s_1}) \neq \bot \wedge \text{tail}(\overline{s_2}) \neq \bot \implies \\[2pt]
  \quad \text{unify}(\text{tail}(\overline{s_1}), \text{tail}(\overline{s_2})) \;\wedge\; \text{linConsumed}(\overline{s_1}, \Gamma_b) = \text{linConsumed}(\overline{s_2}, \Gamma_b) \\[2pt]
  \sigma = \text{branchType}(\overline{s_1}, \overline{s_2})
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e \textbf{if}~e_c~\textbf{then}~\overline{s_1}~\textbf{else}~\overline{s_2} : \sigma \mathbin{!} \rho_c \cup \rho_1 \cup \rho_2
} \;\textsc{T-If}$$
</div>

σ is fixed by the premise $\sigma = \text{branchType}(\overline{s_1}, \overline{s_2})$: when both branches yield a value, σ is their (pairwise-unified) common tail; when one diverges, σ is the survivor's tail; when both diverge, σ is a fresh ${?}\alpha$. Both branches receive the **same** $\Gamma_b$ (since only one executes at runtime). The if-without-else form (surface only) desugars to $\textbf{if}~e_c~\textbf{then}~\overline{s_1}~\textbf{else}~()$ and therefore has type `unit`. Mirrors [T-Match](#T-Match)'s divergent-arm carve-out for symmetry.

<a id="T-Match"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \Gamma = \Gamma_e \otimes \Gamma_b \\[2pt]
  \Gamma_e;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \qquad
  \text{exhaustive}(\text{strip}(\tau), \overline{p}) \\[2pt]
  \text{strip}(\tau) = \texttt{Exn} \implies \text{hasCatchAll}(\overline{p}) \quad\text{(cross-module-extensible: syntactic catch-all required)} \\[4pt]
  \forall i.\;\Gamma_b \vdash p_i : \text{strip}(\tau) \Rightarrow \Gamma_i \\[2pt]
  \forall i.\;\Gamma_i;\, \rho_q;\, \tau_r \vdash_s \overline{s_i} : \Gamma_i' \mathbin{!} \rho_i \\[4pt]
  \forall i, j.\;\text{tail}(\overline{s_i}) \neq \bot \wedge \text{tail}(\overline{s_j}) \neq \bot \implies \\[2pt]
  \quad \text{unify}(\text{tail}(\overline{s_i}), \text{tail}(\overline{s_j})) \;\wedge\; (\text{linConsumed}(\overline{s_i}, \Gamma_i) \setminus \text{bv}(p_i)) = (\text{linConsumed}(\overline{s_j}, \Gamma_j) \setminus \text{bv}(p_j)) \\[2pt]
  \forall i.\;\forall y :^1 S \in (\Gamma_i \setminus \Gamma_b).\;y \in \text{linConsumed}(\overline{s_i}, \Gamma_i) \quad\text{(pattern-introduced linears consumed within arm)} \\[2pt]
  \sigma = \text{branchType}(\overline{s_1}, \ldots, \overline{s_n})
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e \textbf{match}~e~\lbrace \overline{p_i \to s_i} \rbrace : \sigma \mathbin{!} \rho_0 \cup \textstyle\bigcup_i \rho_i
} \;\textsc{T-Match}$$
</div>

σ is fixed by the premise $\sigma = \text{branchType}(\overline{s_1}, \ldots, \overline{s_n})$: the common type of non-diverging ($\text{tail} \neq \bot$) arms, or a fresh ${?}\alpha$ if all arms diverge. All arms receive the same $\Gamma_b$. Because `strip` does not peel $@$, a thunk scrutinee $\tau = @\sigma$ leaves the pattern facing $@\sigma$ rather than σ — pattern rules ([P-Ctor](#P-Ctor), [P-Record](#pattern-matching)) then fail to unify against the constructor/record shape. The user must force the thunk explicitly: $\textbf{match}\;@x\;\lbrace\ldots\rbrace$ routes the linear consumption through [T-Force](#T-Force).

<a id="T-Lambda"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \Gamma_\text{cap} = \lbrace x :^{1} S \in \Gamma \mid x \in \text{fv}(\overline{s}) \rbrace \\[2pt]
  \Gamma_\omega = \lbrace x :^{\omega} S \in \Gamma \mid x \in \text{fv}(\overline{s}) \rbrace \\[2pt]
  \forall x \in \text{fv}(\overline{s}) \cap \text{dom}(\Gamma).\;\Gamma(x) \neq \mathord{\sim}\sigma \quad\text{(no ref capture)} \\[2pt]
  \text{distinct}(\overline{\ell}) \quad\text{(parameter labels are distinct — mirrors [D-Cap](#D-Cap) / [T-Record](#T-Record))} \\[2pt]
  q_i = \begin{cases} 1 & \text{if } \text{linear}(\tau_i) \\ \omega & \text{otherwise} \end{cases} \\[2pt]
  \overline{s}^\dagger = \begin{cases} \overline{s};\,\textbf{return}~() & \text{if}~\tau_r = \texttt{unit}~\wedge~\text{tail}(\overline{s}) \neq \bot \\ \overline{s} & \text{otherwise} \end{cases} \\[2pt]
  \Gamma_\omega,\, \Gamma_\text{cap},\, \overline{x_i :^{q_i} \tau_i};\, \rho_q;\, \tau_r \vdash_s \overline{s}^\dagger : \Gamma' \mathbin{!} \rho_e^\text{body} \\[2pt]
  \text{unify}(\rho_e^\text{body},\, \rho_e) \quad\text{(declared throw row absorbs body's inferred row; uses [U-Row-Exn](#U-Row-Exn) for variant subsumption)} \\[2pt]
  \tau_r \neq \texttt{unit} \implies \text{tail}(\overline{s}^\dagger) = \bot \quad\text{(non-unit returns require explicit termination)} \\[2pt]
  \forall y :^1 S \in \Gamma'.\;y \in \lbrace\overline{x_i}\rbrace \wedge \text{autoDrop}(S) \quad\text{(P-FnEnd: no leaked linear at body end)} \\[2pt]
  \forall i.\;\text{wfRef}(\tau_i) \qquad \text{wfRef}(\tau_r) \qquad \neg\text{escapesRef}(\tau_r) \quad\text{(gravity rule at param + return slots)} \\[2pt]
  \text{wfCap}(\rho_q) \quad \text{wfThrow}(\rho_e) \quad\text{(declared rows reference known caps / variants)} \\[2pt]
  \tau_\to = (\overline{\ell : \tau}) \to \tau_r;\, \rho_q;\, \rho_e \\[2pt]
  \tau_\to^\star = \begin{cases} \%\tau_\to & \text{if } \Gamma_\text{cap} \neq \emptyset \\ \tau_\to & \text{otherwise} \end{cases}
  \end{array}
}{
  \Gamma;\, \rho_q' \vdash_e \textbf{fn}~(\overline{\ell : \tau}) \to \tau_r;\, \rho_q;\, \rho_e~\textbf{do}~\overline{s}~\textbf{end} : \tau_\to^\star \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Lambda}$$
</div>

The lambda is pure ($\mathbin{!} \lbrace\rbrace$). The conclusion's input environment Γ is the caller's $\otimes$-split partition that flows into the lambda's construction site — it contains every ω binding the caller shares (per $\otimes$-split's ω rule) plus exactly the linear bindings the caller has routed to the lambda partition. The premise then derives the captures $\Gamma_\text{cap}$ (the linear restriction of Γ on $\text{fv}(\overline{s})$) and the body's ω context $\Gamma_\omega$ (the ω restriction on $\text{fv}(\overline{s})$) from the input. The lambda **consumes** $\Gamma_\text{cap}$ (captured linears flow into the body and must be discharged by [P-FnEnd](#T-Lambda) before the body returns). The body environment includes $\Gamma_\omega$, $\Gamma_\text{cap}$, and the parameters $\overline{x_i :^{q_i} \tau_i}$ — each parameter's usage $q_i$ matches its type's linearity (mirroring [T-Let](#T-Let)). The closure-linearization premise $\tau_\to^\star$ promotes the lambda's type to $\%\tau_\to$ whenever any linear binding is captured: a closure that owns a linear resource is itself one-shot, so two uses of the same closure value would imply two consumptions of the resource. The same shape is reused in [T-Handler](#T-Handler) to linearize handler values that capture linears.

The conclusion's ambient row $\rho_q'$ is **not bound by any premise** — it is the caller's ambient at the lambda's construction site. The rule reads as "for any $\rho_q'$, …": the caller may construct a lambda under any ambient because lambda construction itself produces no effect ($\mathbin{!} \lbrace\rbrace$) and reads no capabilities. The lambda's own body is typed under the **declared** $\rho_q$ (the require row written into the arrow type), not under $\rho_q'$; the connection between $\rho_q'$ and $\rho_q$ is enforced later, at the call site, by [T-App](#T-App)'s $\text{unify}(\rho_q, \text{open}(\rho_q'))$ premise. Treating $\rho_q'$ as universally quantified is the intentional formalisation of "lambda construction is ambient-independent".

**P-FnEnd (function-end no-leak).** The body's output environment $\Gamma'$ must contain no linear binding except parameters whose declared type is auto-droppable. This formalises [drop.md](../drop)'s function-end check (`require_empty_or_droppable` in `src/typecheck/linearity.nx`) as a premise of T-Lambda rather than leaving it as an out-of-band obligation. Concretely:

- **Captured linears** ($\Gamma_\text{cap}$) flow into the body and must be consumed before body end; otherwise they would be silently dropped when the closure value returns, but the caller still believes the resource is alive via the closure's captured-state contract.
- **Locally introduced linears** (let-bindings inside $\overline{s}$ with linear RHS) likewise must be consumed; they have no consumer in any caller.
- **Linear parameters** ($q_i = 1$) must either be consumed by the body (transferred via a return / throw / argument-passing channel, per [drop.md](../drop) §Linear Consumption) or have $\text{autoDrop}(\tau_i)$ — the carve-out admits e.g. an array-typed parameter whose linear wrapper is structural rather than semantically resource-bearing.

P-FnEnd is the analogue at function-body scope of P-Block at block scope: both reject linear-leak at a scope boundary. T-Lambda is the only construct that crosses a function-body boundary, so the function-end check lives uniquely here; [T-Inject](#T-Inject) and [T-TryCatch](#T-TryCatch) discharge P-Block instead. The two together cover every closing scope in the language.

**Implicit-return desugaring.** The auxiliary $\overline{s}^\dagger$ in T-Lambda's premise formalises the surface convention from [semantics.md](../semantics) §Implicit Unit Return: a **unit**-returning lambda whose body does not already end in a divergent statement (i.e.\ $\text{tail}(\overline{s}) \neq \bot$) is desugared to $\overline{s};\,\textbf{return}~()$ before body typing. Non-unit returns get no desugaring — the rule's $\tau_r \neq \texttt{unit} \implies \text{tail}(\overline{s}^\dagger) = \bot$ premise then statically rejects an `i64`-returning lambda whose body is a let-statement or a bare expression statement that produces a value but never **return**s it. Together, the desugar and the premise pin the surface convention at rule level: unit returners may omit `return ()`; non-unit returners must explicitly `return` (or **throw** / loop forever) on every control-flow path.

<a id="T-Throw-Ctor"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  e = c(\overline{\ell : e_a}) \qquad
  c \in \text{variants}(\texttt{Exn}) \\[2pt]
  \Gamma;\, \rho_q \vdash_e c(\overline{\ell : e_a}) : \texttt{Exn} \mathbin{!} \rho_0
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e \textbf{throw}~e : {?}\alpha \mathbin{!} \lbrace c \rbrace \cup \rho_0
} \;\textsc{T-Throw-Ctor}$$
</div>

<a id="T-Throw-CtorNullary"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  e = c \qquad c \in \text{variants}(\texttt{Exn}) \qquad
  \Gamma(c) = (\omega,\,\forall \overline{\alpha}.\,\texttt{Exn}) \\[2pt]
  \Gamma;\, \rho_q \vdash_e c : \texttt{Exn} \mathbin{!} \rho_0
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e \textbf{throw}~e : {?}\alpha \mathbin{!} \lbrace c \rbrace \cup \rho_0
} \;\textsc{T-Throw-CtorNullary}$$
</div>

<a id="T-Throw-Val"></a>

<div markdown="0">
$$\dfrac{
  e~\text{is neither a constructor application nor a bare exception-constructor identifier} \qquad
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \qquad
  \text{unify}(\tau, \texttt{Exn})
}{
  \Gamma;\, \rho_q \vdash_e \textbf{throw}~e : {?}\alpha \mathbin{!} \lbrace \texttt{Exn} \rbrace \cup \rho_0
} \;\textsc{T-Throw-Val}$$
</div>

The split records variant identity in the effect row. **T-Throw-Ctor** fires when the throw expression is syntactically a constructor application (e.g.\ $\textbf{throw}~\texttt{NotFound}(\textit{path}: p)$) — the row gets the precise constructor name $\lbrace \texttt{NotFound} \rbrace$. **T-Throw-CtorNullary** fires for the bare-identifier form of a zero-field exception (e.g.\ $\textbf{throw}~\texttt{MissingMain}$, where `MissingMain` is bound at value scheme $\forall \overline{\alpha}.\,\texttt{Exn}$ by the nullary clause of [D-Exception](#D-Exception)) — the row again gets the precise variant name $\lbrace \texttt{MissingMain} \rbrace$, not the catch-all sentinel. **T-Throw-Val** fires for the residual case — a variable, projection, or other expression yielding `Exn` (typically a catch-bound binding being re-thrown: $\textbf{catch}~e \to \textbf{throw}~e$); the row gets the catch-all sentinel $\lbrace \texttt{Exn} \rbrace$, which subsumes any variant via [U-Row-Exn](#U-Row-Exn). All three rules produce the universal type $?\alpha$ since **throw** never returns to its caller. The companion [T-TryCatch](#T-TryCatch) consumes these row entries — specific-variant arms subtract specific entries, catch-all arms subtract `Exn` and any constructors covered by U-Row-Exn.

The disambiguation between T-Throw-CtorNullary and T-Throw-Val on a bare identifier follows [P-CtorNullary](#P-CtorNullary)'s convention: Γ-lookup decides. If $\Gamma(c)$ is a value scheme rooted at `Exn` (i.e.\ $c$ was declared by the nullary clause of D-Exception), T-Throw-CtorNullary fires and preserves variant precision; otherwise (a catch-bound $e : \texttt{Exn}$, a record-field projection, etc.), T-Throw-Val fires and assigns the catch-all sentinel.

[T-Handler](#T-Handler) types $\textbf{handler}~x~[\textbf{require}~\rho]~\textbf{do}~\overline{\ell = e}~\textbf{end}$ — a record-of-lambdas implementing the methods of cap $x$. We assume a global lookup $\text{methods}(x)$ returning the method signatures declared for cap $x$ (populated by cap declarations, see §1):

<div markdown="0">
$$\text{methods}(x) = \lbrace\; \ell_j : (\overline{\pi_j}) \to \kappa_j;\, \alpha_j;\, \beta_j \;\mid\; j \in J \;\rbrace$$
</div>

where $\alpha_j$ and $\beta_j$ are the require row and throw row declared for method $\ell_j$ on cap $x$. The handler's arms must be in 1-1 correspondence with $\text{methods}(x)$.

<a id="T-Handler"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \text{methods}(x) = \lbrace\; \ell_j : (\overline{\pi_j}) \to \kappa_j;\, \alpha_j;\, \beta_j \;\mid\; j \in J \;\rbrace \\[2pt]
  \text{handler literal arms} = \lbrace\; \ell'_k = e'_k \;\mid\; k \in K \;\rbrace \\[2pt]
  \lbrace \ell_j \mid j \in J \rbrace = \lbrace \ell'_k \mid k \in K \rbrace \quad\text{(1-1 arm/method correspondence: name-set equality, no missing arm, no extra arm)} \\[2pt]
  \forall j \in J.\;\exists!\;k \in K.\;\ell_j = \ell'_k \qquad e_j \mathrel{\stackrel{\Delta}{=}} e'_{k(j)} \quad\text{where}~k(j)~\text{is the unique}~k~\text{with}~\ell_j = \ell'_k \\[2pt]
  \Gamma_\text{cap} = \lbrace y :^{1} S \in \Gamma \mid y \in \textstyle\bigcup_j \text{fv}(e_j) \rbrace \\[2pt]
  \Gamma_\omega = \lbrace y :^{\omega} S \in \Gamma \mid y \in \textstyle\bigcup_j \text{fv}(e_j) \rbrace \\[2pt]
  \forall y \in \text{dom}(\Gamma_\text{cap}).\;\lvert \lbrace j \in J \mid y \in \text{fv}(e_j) \rbrace \rvert = 1 \quad\text{(each captured linear is referenced by at most one arm — no cross-arm duplication)} \\[2pt]
  \forall y \in \textstyle\bigcup_j \text{fv}(e_j) \cap \text{dom}(\Gamma).\;\Gamma(y) \neq \mathord{\sim}\sigma \\[2pt]
  \forall j \in J.\;\Gamma_\omega,\, \Gamma_\text{cap};\, \rho_q \vdash_e e_j : \tau_j \mathbin{!} \lbrace\rbrace \\[2pt]
  \forall j \in J.\;\text{unify}(\tau_j,\;(\overline{\pi_j}) \to \kappa_j;\, \alpha_j;\, \beta_j) \quad\text{(arm signature absorbs declared method type; row premises invoke [U-Row-Exn](#U-Row-Exn) as needed)} \\[2pt]
  \text{wfCap}(\rho_\text{annot}) \quad\text{(handler's optional require annotation references known caps)} \\[2pt]
  \rho_\text{req} = \textstyle\bigcup_j \alpha_j \cup \rho_\text{annot} \\[2pt]
  \tau_h = \textbf{handler}\;x\;\rho_\text{req}
  \end{array}
}{
  \Gamma;\, \rho_q' \vdash_e \textbf{handler}~x~[\textbf{require}~\rho_\text{annot}]~\textbf{do}~\overline{\ell'_k = e'_k}~\textbf{end} : \tau_h^\star \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Handler}$$
</div>

<div markdown="0">
$$\tau_h^\star = \begin{cases} \%\tau_h & \text{if } \Gamma_\text{cap} \neq \emptyset \\ \tau_h & \text{otherwise} \end{cases}$$
</div>

The handler is pure ($\mathbin{!} \lbrace\rbrace$) — its construction has no effect; effects are deferred until the handler is injected and a method is invoked. Each arm $e_j$ must be a lambda whose function type matches the cap's declared signature for method $\ell_j$. The handler's require row $\rho_\text{req}$ aggregates each arm's declared require row $\alpha_j$ (carried on the lambda's arrow type and validated against the lambda body in [T-Lambda](#T-Lambda)/[T-App](#T-App)) and the optional surface annotation $\rho_\text{annot}$ (defaulting to $\lbrace\rbrace$ if absent). [T-Inject](#T-Inject) checks that $\rho_\text{req}$ is satisfied by the surrounding ambient row at the inject site. Closure linearization mirrors [T-Lambda](#T-Lambda): if any arm captures a linear binding, the entire handler value becomes $\%\tau_h$ — only one **inject** may consume it.

As with [T-Lambda](#T-Lambda), the conclusion's ambient $\rho_q'$ is universally quantified — handler construction is ambient-independent (the per-arm $\alpha_j$ are validated against the arms' own bodies, not the surrounding ambient). The connection between $\rho_q'$ and $\rho_\text{req}$ is enforced at the [T-Inject](#T-Inject) site.

**Arm/method 1-1 correspondence.** Match the cap's declared methods $\lbrace \ell_j \mid j \in J \rbrace$ against the handler literal's arm labels $\lbrace \ell'_k \mid k \in K \rbrace$ **by name** — surface arms may appear in any order, and the impl's `validate_handler_arm_sets` runs the set-equality check before any per-arm work. Set-equality $\lbrace \ell_j \mid j \in J \rbrace = \lbrace \ell'_k \mid k \in K \rbrace$ pins the handler literal to exactly the methods declared on cap $x$, rejecting both omissions (which would leave a cap-method invocation through [T-CapCall](#T-CapCall) with no runtime implementation) and surplus arms (which would silently introduce a name unreachable by any method-dispatch path). The accompanying $\exists!\,k\in K.\;\ell_j = \ell'_k$ premise plus the abbreviation $e_j \mathrel{\stackrel{\Delta}{=}} e'_{k(j)}$ map each method index $j$ to the unique literal arm carrying the same label, so subsequent $e_j$ premises stay unambiguous regardless of the literal's syntactic ordering.

Earlier formulations indexed the per-arm typing premise by $j \in J$ alone, which (a) silently demanded literal-order = methods-order matching, (b) left an extra user arm $\ell_\text{extra} = e_\text{extra}$ untyped, and (c) made the missing-arm case vacuously satisfied. Today's premise discharges all three. Record-construction and call sites get the same treatment elsewhere: [T-Record](#T-Record)'s $\text{distinct}(\overline{\ell})$ and [T-App](#T-App)'s label-permutation premise both pin label sets to their declared shapes.

**No cross-arm linear capture.** Each arm $e_j$ is itself a lambda, so [T-Lambda](#T-Lambda) recomputes its own $\Gamma_\text{cap}$ from the shared $\Gamma_\omega, \Gamma_\text{cap}$ input. Without the $\lvert\lbrace j \mid y \in \text{fv}(e_j)\rbrace\rvert = 1$ premise, a linear $y \in \text{fv}(e_1) \cap \text{fv}(e_2)$ would be routed into *both* arms' per-arm $\Gamma_\text{cap}$ — each arm's T-Lambda derivation consumes the same $y$, double-counting a resource the operational reading admits only once. The premise pins the captured-linear partition to a single arm, matching `linConsumed`'s set-semantics handler clause (which counts each captured linear once across $\bigcup_j \text{fv}(e_j)$) and the impl's runtime layout (one closure-environment slot per binding, shared by all arms).

**With-continuation arms (`with @k`).** A handler arm may optionally carry a *continuation binder* — a thunk whose body is the rest of the arm's own statement list after the `with @k` point. The surface syntax is:

```
fn ell_j(...) -> kappa_j with @k do ... end
```

The binder `k` has type $@\kappa_j$ inside the arm body: forcing it ($@k$) delivers the arm's declared return value of type $\kappa_j$. The binder is linear — it may be forced at most once (a second force would constitute a second return from the arm, which is ill-typed). The formal rule for arm bodies that carry a continuation binder is:

<a id="T-Continuation"></a>

<div markdown="0">
$$\dfrac{
  \text{methods}(x) \ni \ell_j : (\overline{\pi_j}) \to \kappa_j;\, \alpha_j;\, \beta_j \\[2pt]
  k \text{ fresh} \qquad k :^{1} @\kappa_j \notin \Gamma_\text{body} \\[2pt]
  \Gamma_\text{body},\, k :^{1} @\kappa_j;\, \rho_q;\, \kappa_j \vdash_s \overline{s} : \Gamma' \mathbin{!} \beta_j \\[2pt]
  \text{tail}(\overline{s}) = \bot \quad\text{(arm body must terminate divergently — every path \textbf{return}s, throws, or loops)}
}{
  \Gamma_\text{body};\, \rho_q \vdash_\text{arm} \textbf{fn}~\ell_j(\overline{\pi_j}) \to \kappa_j~\textbf{with}~@k~\textbf{do}~\overline{s}~\textbf{end} \mathbin{!} \beta_j
} \;\textsc{T-Continuation}$$
</div>

Here $\Gamma_\text{body}$ is the arm's body environment (parameters $\overline{\pi_j}$ plus any captured bindings from [T-Handler](#T-Handler)'s $\Gamma_\omega, \Gamma_\text{cap}$ partition). The body-typing premise uses the standard statement-sequence judgment $\Gamma; \rho_q; \tau_r \vdash_s \overline{s} : \Gamma' \mathbin{!} \rho_e$ (see §Statements), with the enclosing return slot $\tau_r$ instantiated to $\kappa_j$ — the cap method's declared return type — so a $\textbf{return}~v$ inside the arm body checks $v : \kappa_j$ via [T-Return](#T-Return). The companion $\text{tail}(\overline{s}) = \bot$ premise mirrors [T-Lambda](#T-Lambda)'s non-unit termination guard: every control path through the arm must $\textbf{return}$ a $\kappa_j$ value, $\textbf{throw}$, or otherwise diverge — the arm has no implicit-unit return because $\kappa_j$ may be non-unit and the arm's effect-handler role demands an explicit producer.

T-Continuation is the arm-level refinement of T-Handler's per-arm typing premise $\Gamma_\omega,\, \Gamma_\text{cap};\, \rho_q \vdash_e e_j : (\overline{\pi_j}) \to \kappa_j;\, \alpha_j;\, \beta_j$: when the arm carries `with @k`, the arm lambda's body sees an extra linear binding $k :^{1} @\kappa_j$ in scope, and the arm's function type is the same $(\overline{\pi_j}) \to \kappa_j$ as declared on the cap — the presence of `with @k` does not change the visible method signature. The linearity of $k$ means the body may force the continuation at most once; any control path that forces $k$ more than once is rejected by the standard linear-usage check ([P-FnEnd](#T-Lambda)). Implementation: `src/typecheck/check.nx::check_arm_body` and `check_function` insert $k \mapsto \text{mono}(@\kappa_j)$ into the arm's body environment before running the standard statement-sequence check.

<div markdown="0">
$$\dfrac{
  x :^{\omega} \forall\overline{\alpha}.\,\tau \in \Gamma \qquad
  \tau' = \text{inst}(\forall\overline{\alpha}.\,\tau) \qquad
  \sigma = \text{stripBorrow}(\tau')
}{
  \Gamma;\, \rho_q \vdash_e \&x : \&\sigma \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Borrow}$$
</div>

<div markdown="0">
$$\text{stripBorrow}(\tau) = \begin{cases}
\sigma & \text{if } \tau \in \lbrace \%\sigma,\, @\sigma,\, \&\sigma,\, \mathord{\sim}\sigma \rbrace \\
\tau & \text{otherwise}
\end{cases}$$
</div>

Borrowing does not consume the binding. Only unrestricted bindings can be borrowed. T-Borrow uses `stripBorrow` rather than `strip` because borrowing a $\mathord{\sim}\tau$ binding should yield a $\&\tau$ borrow of the cell's contents, not a nonsensical $\&(\mathord{\sim}\tau)$ borrow-of-cell. The pattern-side `strip` deliberately keeps $\mathord{\sim}$ in place — refs cannot be match scrutinees — so the two operators diverge precisely at the $\mathord{\sim}$ case.

<a id="T-Force"></a>

<div markdown="0">
$$\dfrac{
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \qquad
  \sigma~\text{fresh} \qquad
  \text{unify}(\tau, @\sigma)
}{
  \Gamma;\, \rho_q \vdash_e @e : \sigma \mathbin{!} \rho_0
} \;\textsc{T-Force}$$
</div>

The thunk is consumed by $e$'s sub-derivation: if $e$ is a variable reference $\mu y$, the consumption happens via [T-Var](#T-Var) with $q = 1$ on $y$; if $e$ is a composite expression (e.g. $@x.\textit{thunk\_field}$, $@(\textit{get\_thunk}())$, $@(\textbf{if}~c~\textbf{then}~t_a~\textbf{else}~t_b)$), the consumption occurs at whichever T-Var leaf inside $e$'s derivation tree references the linear thunk-typed binding. This matches `linConsumed`'s recursive clause $\text{linConsumed}(@e,\Gamma) = \text{linConsumed}(e,\Gamma)$: forcing a composite expression inherits its sub-expression's consumption set verbatim. The premise $\text{unify}(\tau, @\sigma)$ uses a fresh σ rather than a structural pattern $\tau = @\sigma$ on the premise's right-hand side, so that an unresolved inference variable $\tau = {?}\alpha$ — common when $e$ is a generic-typed parameter inside a $\forall$-quantified body — is pinned to $@\sigma$ by the unifier instead of leaving the rule inapplicable. The two forms agree on already-concrete $\tau = @\sigma'$ shapes (`unify` succeeds with $\sigma = \sigma'$); they diverge on unresolved τ, where only the unification form makes the derivation tree mechanically constructible.

<div markdown="0">
$$\dfrac{
  \Gamma = \Gamma_1 \otimes \ldots \otimes \Gamma_k \qquad
  \text{distinct}(\overline{\ell}) \qquad
  \forall i.\;\Gamma_i;\, \rho_q \vdash_e e_i : \tau_i \mathbin{!} \rho_i
}{
  \Gamma;\, \rho_q \vdash_e \lbrace \overline{\ell : e} \rbrace : \lbrace \overline{\ell : \tau_i} \rbrace \mathbin{!} \textstyle\bigcup_i \rho_i
} \;\textsc{T-Record}$$
</div>

$\text{distinct}(\overline{\ell})$ holds iff $\lvert\overline{\ell}\rvert = \lvert\lbrace \ell_1, \ldots, \ell_k \rbrace\rvert$ — the label sequence has no duplicates. This makes record types label-sets, not multisets: $\lbrace a:1, a:2\rbrace$ is rejected at construction time, so [T-Proj](#T-Proj) and `fields` never face an ambiguous lookup.

<a id="T-Proj"></a>

<div markdown="0">
$$\dfrac{
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \qquad
  \neg\text{linear}(\tau) \qquad
  (\ell : \sigma) \in \text{fields}(\tau)
}{
  \Gamma;\, \rho_q \vdash_e e.\ell : \sigma \mathbin{!} \rho_0
} \;\textsc{T-Proj}$$
</div>

The $\neg\text{linear}(\tau)$ premise rejects projection on linear records. Since `linear` is structural (§Linearity), it holds whenever τ is itself $\%\sigma$/$@\sigma$/$[\lvert\,\sigma\,\rvert]$ *or* any field's type is linear. Allowing $e.\ell$ on such a record would consume $e$ via the sub-derivation while exposing only one field — silently dropping the other linear obligations. Linear-record destructuring is funneled exclusively through pattern matching ([P-Record](#pattern-matching)), where $\biguplus$ requires every linear field's binding to be picked up. This matches the consumption-channel list in [types.md](../types) (function call, pattern match, return, assignment).

### Statements

<div markdown="0">
$$\Gamma;\, \rho_q;\, \tau_r \vdash_s s : \Gamma' \mathbin{!} \rho_e$$
</div>

$\Gamma'$ is the updated environment (new bindings from [T-Let](#T-Let)). $\tau_r$ is the expected return type of the enclosing function.

[T-Let](#T-Let) resolves numeric literals and applies sigil modalities via two auxiliaries. `default` defaults `intlit`/`floatlit` at binding sites where no concrete type was inferred:

<div markdown="0">
$$\text{default}(\tau) = \begin{cases}
\texttt{i64} & \text{if } \tau = \texttt{intlit} \\
\texttt{f64} & \text{if } \tau = \texttt{floatlit} \\
\tau & \text{otherwise (applied recursively to all subterms)}
\end{cases}$$
</div>

`wrapSigil` wraps the inferred type with the modality corresponding to the binding's sigil. It is **idempotent**: wrapping with a modality the type already carries at the outermost level returns the type unchanged, avoiding ill-formed double-wraps like $\%\%\sigma$ or $@@\sigma$ that no surface syntax can describe.

<div markdown="0">
$$\text{wrapSigil}(\mu, \tau) = \begin{cases}
\tau & \text{if } \mu = \% \wedge \tau = \%\sigma \\
\%\tau & \text{if } \mu = \% \\
\tau & \text{if } \mu = \mathord{\sim} \wedge \tau = \mathord{\sim}\sigma \\
\mathord{\sim}\tau & \text{if } \mu = \mathord{\sim} \\
\tau & \text{if } \mu = @ \wedge \tau = @\sigma \\
@\tau & \text{if } \mu = @ \\
\tau & \text{if } \mu = \& \wedge \tau = \&\sigma \\
\&\tau & \text{if } \mu = \& \\
\tau & \text{if } \mu = \varepsilon
\end{cases}$$
</div>

Idempotency makes $\textbf{let}~\%x = \textit{make\_linear}()$ produce $\%T$ regardless of whether $\textit{make\_linear}$ returns $T$ (weakened) or $\%T$ — the binding's stated modality is the truth. Pattern `strip` removes one layer; idempotent `wrapSigil` ensures that one layer is always present, never two.

<a id="T-Let"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \\[2pt]
  \tau' = \begin{cases} \sigma & \text{if annotation } \sigma \text{ present and } \text{unify}(\tau, \sigma) \\ \text{default}(\tau) & \text{otherwise} \end{cases} \\[2pt]
  \mu = \mathord{\sim} \implies \neg\text{linear}(\tau') \\[2pt]
  \text{annotation } \sigma \text{ present} \implies \text{wfRef}(\sigma) \\[2pt]
  \tau_f = \text{wrapSigil}(\mu, \tau') \qquad
  S = \text{mono}(\tau_f) \\[2pt]
  q = \begin{cases} 1 & \text{if } \text{linear}(\tau_f) \\ \omega & \text{otherwise} \end{cases}
  \end{array}
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{let}~\mu\,x = e : (\Gamma \setminus\!\!\setminus e),\, x :^{q} S \mathbin{!} \rho_0
} \;\textsc{T-Let}$$
</div>

The annotation case **pins** $\tau'$ to σ before any defaulting could fire: $\text{unify}(\tau, \sigma)$ resolves the inferred type (which may be `intlit`/`floatlit`) against the user-written annotation, and $\tau'$ takes σ verbatim. This matters because — per [U-IntLit / U-FloatLit](#U-IntLit) (nexus-q52x.1) — those unifications return the **empty substitution** and do *not* mutate τ in place; running $\text{default}(\tau)$ first would commit to `i64`/`f64` and then mis-unify against any narrower annotation like `i32`. The reproducer is $\textbf{let}~x : \texttt{i32} = 1$: $\tau = \texttt{intlit}$, $\text{unify}(\texttt{intlit}, \texttt{i32})$ succeeds, $\tau' = \texttt{i32}$, accept. Without the case-split — i.e. if `default` fired unconditionally — $\tau' = \texttt{i64}$ and the subsequent unify against `i32` would fail spuriously. This mirrors `src/typecheck/infer.nx::infer_let`: annotation-present skips the literal-defaulter, annotation-absent runs it.

The side-condition $\mu = \mathord{\sim} \implies \neg\text{linear}(\tau')$ enforces the [types.md](../types#mutable-references-) invariant that mutable-ref cells cannot hold linear values. Without it, $\textbf{let}~\mathord{\sim}r = \textit{make\_linear}()$ would produce a $\mathord{\sim}\%T$ binding; subsequent $\mathord{\sim}r$ deref-reads would each yield a fresh $\%T$ value, duplicating the linear resource. The check applies uniformly to inferred types and to explicit annotations ($\textbf{let}~\mathord{\sim}x : \%T = e$). Linearity is structural, so the check also rejects $\mathord{\sim}$ cells holding records or ADTs with any linear component.

T-Let always produces a monomorphic scheme (see P8). The single exception is the variable-aliasing form below, which fires only when the surface form is exactly $\textbf{let}~x = y$ with no sigil, no annotation, and $y$ bound to a polymorphic scheme. All other shapes — annotated, sigil-prefixed, or with a non-variable RHS — fall through to T-Let.

<a id="T-Let-Alias"></a>

<div markdown="0">
$$\dfrac{
  y :^{\omega} \forall\overline{\alpha}.\,\sigma \in \Gamma \qquad
  \overline{\alpha} \neq \emptyset \qquad
  \text{pure}(\Gamma \setminus \lbrace y \rbrace)
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{let}~x = y : \Gamma,\, x :^{\omega} (\forall\overline{\alpha}.\,\sigma) \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Let-Alias}$$
</div>

T-Let-Alias preserves polymorphism across plain rebinding: subsequent uses of $x$ re-instantiate $\forall\overline{\alpha}.\,\sigma$ via [T-Var](#T-Var) just as uses of $y$ would. Without this rule, $\textbf{let}~f = \textit{id}$ would instantiate *id* once at the binding site (collapsing $f$ to a monotyped arrow), defeating the polymorphism of *id* at every use of $f$. The carve-out is intentionally narrow — RHS must be a bare variable — so that `mono`-by-default remains the rule, not the exception. Implementation: see `infer.nx::alias_poly_scheme`.

<a id="T-Let-PolyFn"></a>

The second carve-out fires when the RHS is a **fn** literal carrying an explicit type-parameter list. This is the **only** way a fresh polymorphic scheme enters Γ (per the narrative of §Polymorphism Introduction); T-Let-Alias only forwards an existing scheme.

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  e = \textbf{fn}~\langle X_1, \ldots, X_n\rangle\,(\overline{\ell : \tau}) \to \tau_r;\, \rho_q;\, \rho_e~\textbf{do}~\overline{s}~\textbf{end} \qquad n \geq 1 \\[2pt]
  \forall i.\;\kappa_i~\text{is the inferred kind of}~X_i~\text{(see §Polymorphism Introduction)} \\[2pt]
  \Gamma,\, \overline{X_i{:}\kappa_i};\, \rho_q' \vdash_e \textbf{fn}~(\overline{\ell : \tau}) \to \tau_r;\, \rho_q;\, \rho_e~\textbf{do}~\overline{s}~\textbf{end} : \tau_\to \mathbin{!} \lbrace\rbrace \\[2pt]
  \quad\text{(typed as in [T-Lambda](#T-Lambda) with}~\overline{X_i}~\text{treated as rigid type/row symbols in}~\Gamma; \rho_q'~\text{universally quantified per T-Lambda)} \\[2pt]
  \tau_\to~\text{is not}~\%\sigma \qquad
  S = \forall X_1{:}\kappa_1 \ldots X_n{:}\kappa_n.\,\tau_\to
  \end{array}
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{let}~x = e : \Gamma,\, x :^{\omega} S \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Let-PolyFn}$$
</div>

T-Let-PolyFn formalises the rewrite given in §Polymorphism Introduction. The body $\overline{s}$ is typed under Γ extended with the type-parameter symbols $\overline{X_i{:}\kappa_i}$: each $X_i$ behaves as a **rigid** variable — not a fresh unification variable. Parameter and return annotations that mention $X_i$ pass through unification unchanged (they unify only with themselves), so the body cannot specialise $X_i$ to a concrete type. Generalisation happens once, at the binding site, by quantifying the inferred $\tau_\to$ over $\overline{X_i}$.

Three restrictions are inherited from the surface notation:

- **Sigil-free, annotation-free LHS.** The carve-out fires only on $\textbf{let}~x = e$ without sigil or type annotation. Sigil-prefixed (`%x`, `~x`) or annotated forms fall through to [T-Let](#T-Let), which produces a monomorphic scheme; user code wanting a polymorphic scheme on a sigil binding does not exist in the surface.
- **No linear closure.** The premise $\tau_\to \neq \%\sigma$ rejects polymorphic generalisation over a closure that captured a linear binding — a $\%$-wrapped arrow is one-shot at every instantiation, which is incoherent with $\forall$. Capture-free lambdas (the common case for top-level **fn** declarations) and lambdas closing only over ω bindings satisfy this premise.
- **Quantifier list is non-empty.** When $n = 0$, the rule reduces to T-Let (with $S = \text{mono}(\tau_\to)$); there is no observable difference, so the spec presents the polymorphic case as the carve-out.

Together with T-Let-Alias, these two rules exhaust the entry-points for polymorphic schemes in Γ, justifying P8's "no implicit generalization" property mechanically rather than only by side-remark.

**Inner $\textbf{fn}\langle\overline{X}\rangle$ rejected at expression position.** The surface grammar admits $\textbf{fn}\langle X_1, \ldots, X_n\rangle\,(\overline{\ell{:}\tau}) \to \ldots~\textbf{end}$ at any expression site, but [T-Lambda](#T-Lambda) takes no type-parameter list — its conclusion is $\Gamma;\,\rho_q' \vdash_e \textbf{fn}\,(\overline{\ell{:}\tau}) \to \ldots~\textbf{end} : \tau_\to^\star \mathbin{!} \lbrace\rbrace$. T-Let-PolyFn is the *only* rule whose conclusion accepts the $\langle\overline{X}\rangle$ form, and its conclusion is a $\textbf{let}\,x = e$ statement, not an expression. Therefore an inner $\textbf{fn}\langle X\rangle\ldots$ — e.g. as the argument of a call, the RHS of an assignment, an arm of a **match**, or the body of another lambda — has no derivation. The impl makes this rejection a focused typecheck diagnostic ("polymorphic `fn` only allowed at top-level `let` RHS"; `src/typecheck/infer.nx`, nexus-t9cl.23) rather than letting the failure surface as a generic "no rule applies"-style error far from the cause. Wrap the polymorphic body in a top-level $\textbf{let}\,f = \textbf{fn}\langle X\rangle\ldots$ and reference $f$ instead.

<div markdown="0">
$$\dfrac{
  \tau_r \neq \bot \qquad
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \qquad
  \text{unify}(\tau, \tau_r) \qquad
  \neg\text{escapesRef}(\tau)
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{return}~e : \Gamma \mathbin{!} \rho_0
} \;\textsc{T-Return}$$
</div>

The premise $\tau_r \neq \bot$ rejects $\textbf{return}~e$ outside any enclosing function. The premise $\neg\text{escapesRef}(\tau)$ enforces the gravity rule (see [§Gravity Rule](#gravity-rule-occurrence-position)): a $\mathord{\sim}\sigma$-typed expression may not be returned from a function because that would let the reference cell outlive the stack frame that owns it. The check fires on τ (the inferred type of $e$) rather than on $\tau_r$ (the declared return type) so that it catches cases where $\tau_r$ is a unification variable that happened to unify with a reference type. $\bot$ is the **return-context sentinel** used to mark the absence of an enclosing function (see §1.2 below); a top-level **let** via [D-Let-Top](#D-Let-Top) types its body under $\tau_r = \bot$, so a **return** statement at module scope is statically rejected.

<a id="T-Assign"></a>

<div markdown="0">
$$\dfrac{
  x :^{\omega} (\emptyset,\, \mathord{\sim}\tau) \in \Gamma \qquad
  \Gamma;\, \rho_q \vdash_e e : \sigma \mathbin{!} \rho_0 \qquad
  \text{unify}(\sigma, \tau)
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \mathord{\sim}x \leftarrow e : \Gamma \mathbin{!} \rho_0
} \;\textsc{T-Assign}$$
</div>

[T-Inject](#T-Inject) extends the ambient capability row with the caps each injected handler provides, after checking that the ambient row already satisfies what each handler requires. `merge` unions two rows:

<div markdown="0">
$$\text{merge}(\rho_1, \rho_2) = \rho_1 \cup \rho_2 \quad\text{(row union, deduplicating by type identity)}$$
</div>

Block-scoped constructs (**inject**, **try**/**catch**, and any future bracketing form) close their inner environment back to the outer scope via `closeBlock`, which drops bindings introduced *inside* the block from the output environment. The lexical-scoping rule from [semantics.md](../semantics) — *"Bindings are visible in the block where they are defined and in nested blocks"* — is enforced statically here: an inner **let** may shadow an outer name within the block, but the shadow ceases to exist at block end and the outer binding becomes visible again. A companion premise rejects programs that leave a linear binding introduced *inside* the block unconsumed at block end — those resources have no consumer in the outer scope and would silently leak.

<div markdown="0">
$$\text{closeBlock}(\Gamma_\text{inner}, \Gamma_\text{outer}) = \lbrace x :^q S \mid x \in \text{dom}(\Gamma_\text{outer}) \cap \text{dom}(\Gamma_\text{inner}),\; x :^q S \in \Gamma_\text{outer} \rbrace$$
</div>

Two design properties of this definition:

- **Binding info comes from $\Gamma_\text{outer}$, not $\Gamma_\text{inner}$.** When an inner **let** shadows an outer name, the shadow lives only in $\Gamma_\text{inner}$ during the block; at block end, the outer value is restored. Filtering $\Gamma_\text{inner}$ by outer-dom alone would leak the shadowed scheme into the outer scope and break lexical scoping (e.g.\ outer `x : i64` shadowed by inner `let x = "s"` would surface as `x : string` after the block).
- **Membership in $\Gamma_\text{inner}$ still gates restoration.** A linear outer binding consumed inside the block is removed from $\Gamma_\text{inner}$, and the intersection therefore excludes it from the output. Consumption inside the block reaches the outer scope; only the shadowed-value channel is broken.

A corollary: shadowing a *linear* outer binding inside a closed block is operationally equivalent to consume-and-rebind while the block runs. The outer linear remains in $\Gamma_\text{outer}$ unchanged, but P-Block (below) requires the shadow itself to be consumed before block end, and the outer's quantity/scheme is then restored by the intersection. Programs relying on subtle re-resurrection of a shadowed outer linear should use distinct names.

<div markdown="0">
$$\textbf{P-Block}~\text{(linear no-leak).}\quad\forall x :^1 S \in \Gamma_\text{inner}.\;x \in \text{dom}(\Gamma_\text{outer}) \wedge x :^1 S \in \Gamma_\text{outer}$$
</div>

P-Block rejects two failure modes at the block boundary: (i) a linear binding introduced inside the block ($x \notin \text{dom}(\Gamma_\text{outer})$) that survives to block end has no outer consumer and silently leaks; (ii) a linear outer binding shadowed by an inner **let** to a *different* scheme — $x \in \text{dom}(\Gamma_\text{outer})$ but $x :^1 S \in \Gamma_\text{inner}$ with $S$ not matching $\Gamma_\text{outer}(x)$ — must have its shadow consumed before block end so the outer binding can be restored unambiguously.

P-Block is intentionally one-directional: a linear binding from $\Gamma_\text{outer}$ that survives unchanged through the body remains available for consumption after the block (the consumer runs in outer scope and still sees $x$). Only *newly introduced* linear bindings, and shadows that diverged from the outer scheme, must be consumed before block end. This mirrors the function-end check in [drop.md](../drop) but is strictly stronger: function-end catches leftover linears only at the outermost frame, while P-Block catches them at every nested block boundary.

<a id="T-Inject"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \Gamma = \Gamma_h \otimes \Gamma_\text{body} \\[2pt]
  \forall i.\;{?}P_i,\,{?}\rho_i~\text{fresh} \qquad
  \forall i.\;\text{unify}(\text{strip}(\text{inst}(\Gamma_h(h_i))),\, \textbf{handler}\;{?}P_i\;{?}\rho_i) \\[2pt]
  \forall i \neq j.\;P_i \neq P_j \quad\text{(injection uniqueness: no two handlers may target the same cap)} \\[2pt]
  \forall i.\;\rho_i \subseteq \rho_q \quad\text{(handler requires are satisfied by the ambient row)} \\[2pt]
  \rho_q' = \text{merge}(\rho_q,\, \lbrace \overline{P} \rbrace) \\[2pt]
  \Gamma_\text{body};\, \rho_q';\, \tau_r \vdash_s \overline{s} : \Gamma' \mathbin{!} \rho_0 \\[2pt]
  \forall x :^1 S \in \Gamma'.\;x \in \text{dom}(\Gamma_\text{body}) \wedge x :^1 S \in \Gamma_\text{body} \quad\text{(P-Block: no leaked linear, no diverged shadow)}
  \end{array}
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{inject}~\overline{h}~\textbf{do}~\overline{s}~\textbf{end} : \text{closeBlock}(\Gamma',\, \Gamma_\text{body}) \mathbin{!} \rho_0
} \;\textsc{T-Inject}$$
</div>

The handler's require row $\rho_i$ is a *precondition* on the inject site, not a grant to the body. The body sees only $\rho_q' = \rho_q \cup \lbrace \overline{P} \rbrace$ — the original ambient plus the caps each handler implements. The earlier formulation merged $\text{caps}(\overline{\rho_i})$ into $\rho_q'$ as well, which would let the body access capabilities the surrounding context never granted, breaking capability containment. With requires moved to a containment premise instead, the inject site fails to type-check unless the surrounding scope already provides every capability each handler needs.

**Injection uniqueness.** The premise $\forall i \neq j.\;P_i \neq P_j$ rejects an **inject** clause that lists two handlers targeting the same cap (e.g. $\textbf{inject}\;h_1, h_2\;\textbf{do}\;\ldots\;\textbf{end}$ with both $h_i : \textbf{handler}\;\texttt{Logger}\;\rho$). Without it, `merge` would collapse the row entry to a single `Logger` but $\Gamma_h$ would still bind both handlers — leaving runtime method dispatch under $x.\ell(\ldots)$ (via [T-CapCall](#T-CapCall)) ambiguous between the two arms. Disallowing the overlap statically removes the ambiguity at the rule level; programs that need to swap handlers should nest two single-handler **inject**s instead, where the inner one shadows the outer while its body runs. The impl in `src/typecheck/check.nx::check_inject` performs the same duplicate-cap rejection.

**Unification-based handler shape match.** The premise uses $\text{unify}(\cdots, \textbf{handler}\;{?}P_i\;{?}\rho_i)$ with fresh metavariables $({?}P_i, {?}\rho_i)$ rather than a structural pattern $\text{strip}(\cdots) = \textbf{handler}\;P_i\;\rho_i$ on the right-hand side. The two forms agree on already-concrete handler types (`unify` pins ${?}P_i, {?}\rho_i$ to the concrete components); they diverge on the unresolved-inference-variable case (e.g.\ a generic-typed handler parameter whose inst yields ${?}\alpha$) — only the unification form makes the derivation tree mechanically constructible. This mirrors [T-Force](#T-Force)'s pattern of $\text{unify}(\tau, @\sigma)$ over a literal structural match, keeping the rule applicable when the inferred handler type is still a meta-variable. Note: $P_i$ ranges over cap names — a row-entry symbol — so ${?}P_i$ stands for a cap-name unification variable, distinct from the type/row meta-variable categories used elsewhere; the current surface does not allow cap-polymorphic functions, so ${?}P_i$ remains resolvable to a concrete cap name in every well-typed program (any open ${?}P_i$ remaining after generalisation is a defect rather than a feature). The same shape applies to ${?}\rho_i$, which is a row meta-variable in the existing row-unification machinery.

Two linearity-related details:

- **Strip on handler-pattern match.** [T-Handler](#T-Handler) wraps the handler's type with $\%$ when any arm captures a linear binding, producing $\%(\textbf{handler}\;P\;\rho)$. Without `strip`, the structural pattern $\textbf{handler}\;P_i\;\rho_i$ in this premise would not match a $\%$-wrapped handler — every captured-linear handler would be unusable. `strip` peels the $\%$ wrapper before the structural match, mirroring its use on match scrutinees in [T-Match](#T-Match). Note that `strip` does **not** peel $@$: a handler of type $@(\textbf{handler}\;P\;\rho)$ fails this premise, requiring the user to force it explicitly (e.g. $\textbf{inject}\;@h\;\textbf{do}\;\ldots\;\textbf{end}$) so the thunk's linear consumption goes through [T-Force](#T-Force).
- **$\otimes$-split between handler lookup and body.** Γ is split into $\Gamma_h$ (used to look up the handler bindings $h_i$) and $\Gamma_\text{body}$ (which flows into $\overline{s}$). For unrestricted handlers ($q = \omega$), $\otimes$ assigns the binding to both partitions, so the body can still call methods on the same handler. For linear handlers ($q = 1$, e.g. $\%h$), $\otimes$ assigns the binding to exactly one partition: when used at the inject site it is *not* available in the body, preventing the documented "only one inject may consume it" promise from being silently violated by an in-body re-use.

[T-CapCall](#T-CapCall) types a cap-method invocation $x.\ell(\overline{\ell':e})$ inside a scope where a handler for cap $x$ has been injected. Method signatures are read from the global $\text{methods}(x)$ environment populated by cap declarations:

<a id="T-CapCall"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{c}
  B = \lbrace x \in \text{dom}(\Gamma) \mid \Gamma(x) = (1, \_) \wedge \exists i.\; e_i = \&x \wedge \forall j.\; x \in \text{fv}(e_j) \implies e_j = \&x \rbrace \\[2pt]
  \Gamma \mid_B~\text{is shared as}~\omega~\text{across}~\Gamma_1, \ldots, \Gamma_k \quad\text{(borrow-only linears coexist; see T-App)} \\[2pt]
  (\Gamma \setminus B) = \Gamma_1 \otimes \ldots \otimes \Gamma_k \\[2pt]
  \text{methods}(x).\ell = (\overline{\ell' : P}) \to \kappa;\, \alpha;\, \beta \\[2pt]
  \alpha \subseteq \rho_q \qquad
  x \in \rho_q \\[2pt]
  \forall i.\;(\Gamma_i \cup \Gamma\mid_B);\, \rho_q \vdash_e^{\text{arg}} e_i \mathrel{\Updownarrow} P_i : \tau_i \mathbin{!} \rho_i \\[2pt]
  \forall i.\;\begin{cases} \text{unify}(\tau_i, \text{strip}(P_i)) & \text{if } P_i = \%\sigma \wedge \neg\text{linear}(\tau_i) \wedge \tau_i \neq \&\sigma' \\ \text{unify}(\tau_i, P_i) & \text{otherwise} \end{cases}
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e x.\ell(\overline{\ell' : e}) : \kappa \mathbin{!} \beta \cup \textstyle\bigcup_i \rho_i
} \;\textsc{T-CapCall}$$
</div>

T-CapCall is the missing link between handler declarations and call sites. Three premises wire the rows:

- $\alpha \subseteq \rho_q$ — the method's declared **require** row must be a subset of the ambient capability row, so the caller already holds whatever capabilities this method invocation transitively needs (delegated to the handler's body).
- $x \in \rho_q$ — the cap $x$ itself must be in the ambient row, meaning a handler for $x$ has been brought into scope by an enclosing [T-Inject](#T-Inject) (or by the function's own require annotation).
- β joins the call's effect row — exceptions a method may throw propagate to the caller's $\rho_e$.

The argument premises mirror [T-App](#T-App) exactly — three fixes that landed in T-App are ported here for consistency (nexus-q52x.2 / nexus-2z0b.2 / nexus-t9cl.18):

1. **B set and shared-borrow split (nexus-q52x.2 / nexus-2z0b.2).** The set $B$ collects every linear binding that appears in argument position *only* as $\&x$ (never consumed directly). These bindings are withdrawn from the $\otimes$-split and instead *shared* across all partitions $\Gamma_1,\ldots,\Gamma_k$ as ω while arguments are typed — because a borrow is a non-consuming view, the same linear can legally appear in multiple argument borrows without violating the split. This covers the case $x.\text{method}(p: \&\%q,\; r: \&\%q)$ where the same linear $q$ is borrowed twice (nexus-2z0b.2): without the $B$-set, a naive $\otimes$-split would assign $q$ to exactly one partition and reject the second borrow.

2. **Argument-position typing $\vdash_e^{\text{arg}}\,e \mathrel{\Updownarrow} P$ (nexus-q52x.2).** Arguments are typed with the dedicated $\vdash_e^{\text{arg}}$ judgement that includes [T-App-BorrowLin](#T-App): when the argument is syntactically $\&x$ and the parameter shape is $\&\sigma$, the borrow is admitted even if $x$ is a linear binding. This allows $x.\ell(\text{arg}: \&\%q)$ where $\%q$ is a linear binding — the same permission T-App grants for ordinary function calls.

3. **Borrow-to-ownership smuggling rejection $\tau_i \neq \&\sigma'$ (nexus-t9cl.18).** The $\%$-weakening case additionally requires $\tau_i \neq \&\sigma'$ to exclude borrow types from the weakening path. Without this carve-out, $\text{linear}(\&\sigma') = \text{false}$ would make a $\&\texttt{T}$ argument appear non-linear and thus eligible to satisfy a $\%\texttt{T}$ parameter slot via weakening — silently converting a borrow into an ownership claim. The fix matches T-App's identical side condition.

The result type $\kappa$ is the method's declared return type; no instantiation step is needed because **cap declarations are monomorphic at every level** — cap names $X$ take no type parameters in the surface grammar (`cap X do ... end`, never `cap X<T> do ... end`), and method signatures inside a cap are not generalised by [D-Cap](#D-Cap). The parser rejects the polymorphic-cap form at the declaration site; the spec therefore needs no rule for "instantiating a cap's type parameters at the call site".

If polymorphic caps become a surface feature in the future (e.g.\ for a collection-style cap `Vec<T>`), D-Cap would have to store a scheme $\forall \overline{\alpha}.\,\text{methods}$ and T-CapCall would read the concrete instantiation $\overline{\sigma}$ off the injected handler's type (extending $\textbf{handler}\;X\;\rho$ to $\textbf{handler}\;X\langle \overline{\sigma}\rangle\;\rho$). This is recorded here as a forward-pointer, not a current rule.

<a id="T-TryCatch"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \overline{s_\text{try}} : \Gamma_1 \mathbin{!} \rho_\text{try} \\[2pt]
  \forall x :^1 S \in \Gamma_1.\;x \in \text{dom}(\Gamma) \wedge x :^1 S \in \Gamma \quad\text{(P-Block: try-body)} \\[4pt]
  \forall i.\;\Gamma_1 \vdash p_i : \texttt{Exn} \Rightarrow \Gamma_i \\[2pt]
  \forall i.\;\Gamma_i;\, \rho_q;\, \tau_r \vdash_s \overline{s_i} : \Gamma_i' \mathbin{!} \rho_i \\[2pt]
  \forall i.\;\forall x :^1 S \in \Gamma_i'.\;x \in \text{dom}(\Gamma) \wedge x :^1 S \in \Gamma \quad\text{(P-Block: catch-arm)} \\[4pt]
  \overline{C}_\text{caught} = \text{caughtVariants}(\overline{p}) \\[2pt]
  \rho_\text{residual} = \begin{cases} \rho_\text{try} \setminus (\lbrace\texttt{Exn}\rbrace \cup \overline{C}_\text{caught}) & \text{if } \text{hasCatchAll}(\overline{p}) \\ \rho_\text{try} \setminus \overline{C}_\text{caught} & \text{otherwise} \end{cases}
  \end{array}
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{try}~\overline{s_\text{try}}~\textbf{catch}~\overline{p_i \to s_i}~\textbf{end} : \text{closeBlock}(\Gamma_1,\, \Gamma) \mathbin{!} \rho_\text{residual} \cup \textstyle\bigcup_i \rho_i
} \;\textsc{T-TryCatch}$$
</div>

The output environment is $\text{closeBlock}(\Gamma_1, \Gamma)$ — $\Gamma_1$ (the try-block's evolved environment) restricted to the outer scope Γ. Bindings introduced *inside* the try-body — pattern bindings on **let**, locals scoped to the try — are dropped at the construct's end, matching the lexical-scoping rule. The catch-arm output environments $\Gamma_i'$ are not threaded into the construct's output: the conservative choice picks the try-success path's view of Γ, because a catch arm runs only when the try-body thrown before completing, leaving the precise consumption state of outer linears statically indeterminate. Both the try-body and every catch arm carry the P-Block premise, ensuring no linear binding introduced inside either branch leaks past the construct.

Variant-precise residual computation requires two auxiliaries:

<div markdown="0">
$$\text{caughtVariants}(\overline{p}) = \bigcup_i \begin{cases}
\lbrace c \rbrace & \text{if}~p_i = c~\text{or}~p_i = c(\overline{\ell : p'})~\text{and}~c \in \text{variants}(\texttt{Exn}) \\
\emptyset & \text{otherwise (wildcard, variable pattern)}
\end{cases}$$
</div>

A group-name pattern $G$ has no clause here — group patterns are flattened to their member set $\lbrace C_1, \ldots, C_n \rbrace$ at parse time (see §Row Types) and surface as a fan of constructor-pattern arms before reaching the typing rules. caughtVariants therefore sees only individual constructors $c$. The auxiliary $\text{members}(G)$ is the parse-time projection that gives that fan its contents; it is *not* read by any typing rule but is referenced by D-ExceptionGroup and the parse-time expansion narrative.

<div markdown="0">
$$\text{members}(G) = \lbrace C_1, C_2, \ldots, C_n \rbrace \quad\text{where}~G~\text{was declared}~\textbf{exception group}~G = C_1 \mathrel{\vert} \ldots \mathrel{\vert} C_n$$
</div>

Group members must be individual exception constructors, not other group names. Nesting is **rejected**: a declaration $\textbf{exception group}~G_2 = G_1 \mathrel{\vert} C_k$ where $G_1$ is itself a group name is ill-formed — [D-ExceptionGroup](#D-ExceptionGroup) requires each $C_i \in \text{variants}(\texttt{Exn})$, and group names are not exception constructors. To create a "super-group" spanning the members of $G_1$, list all individual constructors directly (see [Exception Groups](../exception-groups) §Group Composition). This matches the implementation, which does not perform transitive group expansion.

<div markdown="0">
$$\text{hasCatchAll}(\overline{p}) = \exists i.\;p_i = \_ \;\vee\; p_i~\text{is a variable pattern}~x$$
</div>

The catch-all condition `hasCatchAll` is *syntactic*: only an explicit wildcard arm $\_ \to \ldots$ or a single-variable arm $e \to \ldots$ (binding the exception value at type `Exn`) clears the catch-all sentinel and any remaining declared-variant entries. A *closed enumeration* of currently-declared `Exn` variants does **not** count — because `Exn` is extensible across modules, a closed enumeration that is exhaustive at the catch site can become inexhaustive when a downstream module declares a new variant, silently corrupting the throws-row of any function whose body contains the now-stale catch. Requiring a syntactic catch-all closes that cross-module hole.

Variant subtraction enables partial catches: catching only `NotFound` from a try-row of $\lbrace \texttt{NotFound}, \texttt{PermDenied} \rbrace$ leaves $\lbrace \texttt{PermDenied} \rbrace$ in the residual. Group catches (e.g. $\textbf{catch}~\vert~\texttt{IOError} \to \ldots$) expand to their member set via $\text{members}(G)$ at parse time; the formal rule sees only the expanded constructor list (see [Exception Groups](../exception-groups)). Arms may add new effects $\rho_i$ (if an arm itself throws), which always join the residual row regardless of catch-all status.

<a id="T-While"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \text{pure}(\Gamma_c) \quad\text{(cond evaluated each iteration must not consume linears)} \\[2pt]
  \Gamma_c;\, \rho_q \vdash_e e_c : \tau_c \mathbin{!} \rho_c \qquad
  \text{unify}(\tau_c, \texttt{bool}) \\[2pt]
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \overline{s} : \Gamma' \mathbin{!} \rho_b \\[2pt]
  \lbrace x :^1 S \in \Gamma' \rbrace = \lbrace x :^1 S \in \Gamma \rbrace \quad\text{(P-Loop: linear set preserved across iterations)} \\[2pt]
  \text{where}~\Gamma_c~\text{is the}~\omega\text{-restriction of}~\Gamma~\text{(every}~\omega\text{-bound entry of}~\Gamma\text{; no linear entries)}
  \end{array}
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{while}~e_c~\textbf{do}~\overline{s}~\textbf{end} : \Gamma \mathbin{!} \rho_c \cup \rho_b
} \;\textsc{T-While}$$
</div>

T-While types a while loop as a statement of unit-shaped effect: the body may run zero or more times, so the output environment is fixed to the input Γ (no new bindings escape — the loop is block-scoped) and the linear set must be **invariant across one iteration**. P-Loop is the loop-specific analogue of P-Block: every linear binding in Γ must survive unchanged in $\Gamma'$, and $\Gamma'$ contains no linear binding absent from Γ. Equivalently — using the env-difference notation from §Environment and Usage — the linear *restriction* of $\Gamma'$ matches that of Γ as sets of $(name, q=1, scheme)$ triples.

**Cond must be linear-pure.** The condition expression $e_c$ is typed under $\Gamma_c$, the ω-restriction of Γ — every ω-bound entry is in $\Gamma_c$; no linear entries. This is *not* a $\otimes$-split (which would route a linear to one side or the other): the loop body must see *all* of Γ's linears intact in order for P-Loop's set equality to hold, and the condition is re-evaluated on every iteration, so consuming a linear in it would be a single-use-resource–used-twice hazard. The $\text{pure}(\Gamma_c)$ premise (defined in §Expressions) enforces that the cond's local env contains no live linear; in practice the cond can read any ω binding but cannot mention a $\%$-bound variable. A linear $\%q$ may still be observed by **passing a borrow at the call site**: `while is_empty(p: &%queue)` is well-typed because $\&\%q$ in argument position is admitted by [T-App](#T-App)'s borrow-of-linear carve-out (the call's argument typing reads the binding via borrow without consuming it, and discharges the borrow on the call's return). Writing $\&\%q$ as a bare expression at the let-RHS position remains rejected — [T-Borrow](#T-Borrow)'s $x :^{\omega}$ premise blocks the standalone form. The asymmetry matches the impl in `src/typecheck/infer.nx`, which only admits linear borrows when they appear directly as a call argument.

The premise rejects three failure modes:

- **Consume-then-loop.** If body iteration 1 consumes a linear $\%h$ from Γ ($\%h \in \Gamma$ but $\%h \notin \Gamma'$), iteration 2 has no $\%h$ — would be a use-after-consume on a value the type system claims is still available outside the loop. P-Loop's $\subseteq$ direction rejects this.
- **Leak-into-loop.** If the body introduces a new linear $\%g$ that survives to body end ($\%g \in \Gamma'$ but $\%g \notin \Gamma$), the loop would either accumulate $\%g$ instances across iterations or silently drop them. P-Loop's $\supseteq$ direction rejects this — matching the impl's "while body must preserve linear set" check (`src/typecheck/linearity.nx`).
- **Shadow-rebind of outer linear.** A body $\textbf{let}~\%h = \ldots$ that shadows an outer $\%h$ to a different scheme falls under leak-into-loop after the inner shadow's consumption: the shadow's scheme differs from $\Gamma(\%h)$, so the set equality fails.

Surface `for x in start..end do s̄ end` desugars to `while` with an explicit counter binding and increment; the desugaring is handled at lowering, before T-While fires. Surface `break` / `continue` are also lowered (to early-exit on a synthesized boolean), so the core calculus sees only the form above. The output Γ is the *input* Γ even when the body diverges (`return` inside the body short-circuits the enclosing function via **return**'s own typing; T-While simply records that the loop produces no observable binding update).

<a id="T-LetPat"></a>

<div markdown="0">
$$\dfrac{
  \neg\text{diverges}(e) \qquad
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \qquad
  \text{exhaustive}(\text{strip}(\tau), [p]) \qquad
  (\Gamma \setminus\!\!\setminus e) \vdash p : \text{strip}(\tau) \Rightarrow \Gamma'
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{let}~p = e : \Gamma' \mathbin{!} \rho_0
} \;\textsc{T-LetPat}$$
</div>

$\text{strip}(\tau)$ peels any $\%$ sigil wrapper before exhaustiveness and pattern-typing, mirroring [T-Match](#T-Match)'s use of `strip`. Without this, a linear scrutinee $e : \%\sigma$ would require the pattern to match $\%\sigma$ directly — but the Maranget rules and pattern premises operate on the inner σ, not on the sigil-wrapped type. The asymmetry between T-LetPat and T-Match would have made linear destructuring via `let` formally non-derivable even when the equivalent `match e { p -> ... }` succeeds. The $\setminus\!\!\setminus$ consumption of the scrutinee's linear resources still fires through the $e$ premise.

<a id="T-LetPat-Diverge"></a>

<div markdown="0">
$$\dfrac{
  \text{diverges}(e) \qquad
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{let}~p = e : \Gamma \mathbin{!} \rho_0
} \;\textsc{T-LetPat-Diverge}$$
</div>

$\text{diverges}(e)$ holds iff $e$ is syntactically $\textbf{throw}~e'$ (for any $e'$) — the only expression form that produces no value. The split rules avoid the ill-defined case $\text{exhaustive}(?\alpha, [p])$ that would otherwise arise: T-Throw gives **throw** the type $?\alpha$ (a fresh unification variable), against which the Maranget head-shape rules (Exh-Bool, Exh-Sum, Exh-Record) cannot fire — a non-wildcard pattern like $\texttt{Some}(y)$ would leave the check stuck. T-LetPat-Diverge bypasses exhaustiveness because divergence semantically *short-circuits* the binding: the pattern is never destructured at runtime. Since the statement diverges, the residual environment is Γ (unchanged — no pattern binders are introduced into the post-statement env): any names $p$ would have bound are unreachable, and exposing them in $\Gamma'$ would cause P-FnEnd / P-Block to falsely report them as linearity leaks. The pattern typing premise is therefore dropped entirely in this rule; only the throw expression is typed to establish the effect row $\rho_0$. This carve-out mirrors the $\text{tail}(\overline{s})$ classification of $\textbf{let}~\mu\,x = \textbf{throw}~e'$ as $\bot$ (§Expressions, T-If/T-Match), and is consistent with T-Seq-Cons's requirement that no statement follows a diverging one.

### Statement Sequences

Function bodies, branch arms, and the bodies of **inject** and **try** are all sequences $\overline{s} = s_1; s_2; \ldots; s_n$. The sequence judgment $\Gamma;\,\rho_q;\,\tau_r \vdash_s \overline{s} : \Gamma' \mathbin{!} \rho_e$ is built from two rules:

<a id="T-Seq-Empty"></a>

<div markdown="0">
$$\dfrac{}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \cdot : \Gamma \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Seq-Empty}$$
</div>

<a id="T-Seq-Cons"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  \Gamma;\, \rho_q;\, \tau_r \vdash_s s : \Gamma_1 \mathbin{!} \rho_1 \\[2pt]
  \Gamma_1;\, \rho_q;\, \tau_r \vdash_s \overline{s'} : \Gamma_2 \mathbin{!} \rho_2 \\[2pt]
  \text{tail}(s) \neq \bot \;\vee\; \overline{s'} = \cdot
  \end{array}
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s s; \overline{s'} : \Gamma_2 \mathbin{!} \rho_1 \cup \rho_2
} \;\textsc{T-Seq-Cons}$$
</div>

T-Seq-Cons threads the environment ($\Gamma_1$ from the head feeds into the tail) and unions the effect rows. The premise $\text{tail}(s) \neq \bot \vee \overline{s'} = \cdot$ rejects **dead statements after divergence**: if $s$ is $\textbf{return}~e$, $\textbf{throw}~e$ (as expression statement), $\textbf{let}~\mu\,x = \textbf{throw}~e'$, or $\textbf{let}~p = e$ with $\text{diverges}(e)$, then $\text{tail}(s) = \bot$ and the sequence must end there. Programs with statements after a **return** are rejected at type-checking time rather than silently dropped — the rejection surfaces a likely programmer error (writing past a return) and avoids the question of how to type-check unreachable code. The destructuring form $\textbf{let}~p = e$ with a divergent RHS is the [T-LetPat-Diverge](#T-LetPat-Diverge) carve-out — both single-binder and pattern-destructuring lets diverge symmetrically when their RHS does. The same `tail` predicate used in [T-If](#T-If)/[T-Match](#T-Match) is reused here, so divergence handling stays uniform across the spec.

### Metatheoretic Properties

The type system commits to five soundness properties (P1–P5) plus the three local properties stated inline at their respective sections (P6 Exhaustiveness, [Pattern Matching](#pattern-matching); P7 Unification, §Unification; P8 No implicit generalization, §Polymorphism Introduction). The five global properties are:

<div markdown="0">
$$\textbf{P1}~\text{(Progress)}.\quad \text{If}~\emptyset;\,\lbrace\rbrace;\,\bot \vdash_s s : \Gamma' \mathbin{!} \rho_e,~\text{then either:}$$
</div>

<div markdown="0">
$$\quad\text{(a)}~s~\text{reduces to some}~s'~\text{by an operational step, or (b)}~s~\text{is a terminal form (value, terminating}~\textbf{return}, \text{escaping}~\textbf{throw}\text{).}$$
</div>

<div markdown="0">
$$\textbf{P2}~\text{(Preservation)}.\quad \text{If}~\Gamma;\,\rho_q;\,\tau_r \vdash_s s : \Gamma' \mathbin{!} \rho_e~\text{and}~s \longrightarrow s',~\text{then}$$
</div>

<div markdown="0">
$$\quad \Gamma;\,\rho_q;\,\tau_r \vdash_s s' : \Gamma'' \mathbin{!} \rho_e'~\text{with}~\Gamma'' \sqsubseteq \Gamma'~\text{and}~\rho_e' \subseteq \rho_e.$$
</div>

The environment **refinement relation** $\Gamma'' \sqsubseteq \Gamma'$ ("$\Gamma''$ refines $\Gamma'$") is defined as:

<div markdown="0">
$$\Gamma'' \sqsubseteq \Gamma' \;\Longleftrightarrow\; \text{dom}(\Gamma'') \subseteq \text{dom}(\Gamma') \;\wedge\; \exists\,\theta.\;\forall x \in \text{dom}(\Gamma'').\;\Gamma''(x) = \theta(\Gamma'(x))$$
</div>

where $\theta$ is a substitution of unification variables in $\Gamma'$ accumulated during the reduction $s \longrightarrow s'$ (the same shape of substitution produced by [Unification](#unification)). Two readings are implied:

- $\text{dom}(\Gamma'') \subseteq \text{dom}(\Gamma')$ — reduction may *remove* bindings (a linear $\%x$ consumed by the step disappears), but may not *introduce* names absent from the typed source. The names in $\Gamma''$ are a subset of $\Gamma'$'s.
- $\Gamma''(x) = \theta(\Gamma'(x))$ for surviving $x$ — usage annotations $q$ and schemes $S$ may be specialised by $\theta$, but not loosened (an ω entry stays ω; a $\forall \overline{\alpha}.\tau$ may have $\overline{\alpha}$ pinned to concrete types).

The condition $\rho_e' \subseteq \rho_e$ is plain row subset (no row-tail refinement; the reduction never *introduces* new effect variants beyond those the typed source declared).

<div markdown="0">
$$\textbf{P3}~\text{(Linear consumption)}.\quad \text{For any closing scope discharged by [P-FnEnd](#T-Lambda) (function body), [P-Block](#environment-and-usage)}$$
</div>

<div markdown="0">
$$\quad \text{(}\textbf{inject}/\textbf{try}\text{), or [P-Loop](#T-While) (}\textbf{while}\text{), every linear binding introduced inside the scope is consumed exactly once before the scope closes.}$$
</div>

<div markdown="0">
$$\textbf{P4}~\text{(Capability containment)}.\quad \text{For any well-typed function body typed under declared}~\rho_q,~\text{every [T-CapCall](#T-CapCall)}$$
</div>

<div markdown="0">
$$\quad \text{and [T-App](#T-App) inside the body satisfies its respective}~\alpha \subseteq \rho_q~\text{premise.}$$
</div>

<div markdown="0">
$$\textbf{P5}~\text{(Exception containment)}.\quad \text{For any well-typed function body typed under declared}~\rho_e,~\text{every [T-Throw-Ctor](#T-Throw-Ctor)}$$
</div>

<div markdown="0">
$$\quad \text{/ [T-Throw-CtorNullary](#T-Throw-CtorNullary) / [T-Throw-Val](#T-Throw-Val) inside the body produces a row entry that is in}~\rho_e~\text{or subsumed by}~\texttt{Exn} \in \rho_e~\text{via [U-Row-Exn](#U-Row-Exn).}$$
</div>

P1 and P2 are stated relative to an operational semantics — the spec does not give small-step rules in this document; the reduction relation $\longrightarrow$ is defined narratively in [semantics.md](../semantics) and is the obligation of the runtime/codegen pipeline. The other three properties (P3–P5) are *structural*: every `check` pass on a term derives them by induction over the relevant rules' premises, with [P-FnEnd](#T-Lambda)/[P-Block](#environment-and-usage)/[P-Loop](#T-While) discharging P3, the $\subseteq$ premises of T-App / T-CapCall discharging P4, and the row-entry constructions in T-Throw-* discharging P5. In this sense P3–P5 are *intrinsic* to the rules' shape — any conformant implementation that admits a rule's conclusion has already established the corresponding fragment of the property.

The numbering reserves P1–P5 for these global properties so the rule-local P6–P8 (which are convenient where they're stated, but not architectural) can stay in their natural sections without renumbering. A future revision may add P9, P10 etc.\ for new local properties.

---

## 3. Top-Level Declarations

A program is a sequence of top-level declarations followed by zero or more top-level **let** bindings. Declarations populate the global tables — Γ (term bindings), `typedef` (named type schemes), `variants` (sum-type constructor sets), `methods` (cap method signatures), and `members` (exception-group expansion) — that the per-expression rules in §2 read as preconditions. §1 described these declarations as "not terms; preconditions on Γ"; the judgments in this section spell out exactly how the preconditions are produced.

We write $\mathcal{T} = \langle \Gamma,\, \text{typedef},\, \text{variants},\, \text{methods},\, \text{members},\, \text{exports} \rangle$ for the six-tuple of tables. `exports` is the set of binder names declared with the `export` prefix in the current module; the field is populated incrementally as the per-rule folds run (each $\textbf{export}~\text{decl}$ adds the bound name(s) to `exports` in addition to whatever effect the underlying `decl` has on the other tables — see [§Visibility](#visibility-export)). `exports` is the only $\mathcal{T}$-component that distinguishes `export` from non-`export` declarations within a single module; the others are populated identically by both forms. The declaration judgment

<div markdown="0">
$$\mathcal{T} \;\vdash_d\; \text{decl} \;\Rightarrow\; \mathcal{T}'$$
</div>

says that processing `decl` against the current tables produces the updated tables $\mathcal{T}'$. Sequencing through a file folds the rules left-to-right; processing through imports updates the tables before the importing module's own declarations fire (see [imports.md](../imports) for module ordering).

In each rule below, components of $\mathcal{T}$ not mentioned in the conclusion are unchanged. All tables grow monotonically — declarations only extend; existing entries are never removed or rewritten.

**Two-phase processing for type declarations.** A naive left-to-right fold cannot type a self-referential `type Tree<T> = Leaf | Node(left: Tree<T>, …)` (Tree's field references Tree before Tree is in `typedef`) or a mutually-recursive `type Even = Zero | ESucc(odd: Odd); type Odd = OSucc(even: Even)` (Odd is forward-referenced by Even). The same hazard applies to recursive top-level **let** functions (`let factorial = fn ... factorial(...) ... end`). To handle all of these uniformly, file processing runs a **forward-registration judgment** $\vdash_d^{\text{pre}}$ before the body-resolution judgment $\vdash_d$:

<a id="D-Type-Forward"></a>

<div markdown="0">
$$\dfrac{
  D = \textbf{type}~x\langle \overline{\alpha} \rangle = \ldots~\text{(body unresolved)}
}{
  \mathcal{T} \;\vdash_d^{\text{pre}}\; D \;\Rightarrow\; \mathcal{T}[\text{typedef}(x) \mathrel{:=} \forall \overline{\alpha}.\,x\langle \overline{\alpha} \rangle]
} \;\textsc{D-Type-Forward}$$
</div>

<a id="D-Let-Forward"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  D = \textbf{let}~x = \textbf{fn}~[\langle \overline{X} \rangle]\,(\overline{\ell:\tau}) \to \tau_r;\,\rho_q;\,\rho_e~\textbf{do}~\overline{s}~\textbf{end} \\[2pt]
  S_{\text{pre}} = \begin{cases} \forall \overline{X{:}\kappa}.\,(\overline{\ell:\tau}) \to \tau_r;\,\rho_q;\,\rho_e & \text{if}~\overline{X}~\text{non-empty} \\ \text{mono}((\overline{\ell:\tau}) \to \tau_r;\,\rho_q;\,\rho_e) & \text{otherwise} \end{cases}
  \end{array}
}{
  \mathcal{T} \;\vdash_d^{\text{pre}}\; D \;\Rightarrow\; \mathcal{T}[\Gamma \mathrel{:=} \Gamma,\, x :^{\omega} S_{\text{pre}}]
} \;\textsc{D-Let-Forward}$$
</div>

D-Type-Forward and D-Let-Forward are the only $\vdash_d^{\text{pre}}$ rules; every other declaration form (**cap**, **exception**, **exception group**, **external**, top-level **let** whose RHS is *not* a **fn** literal, destructuring $\textbf{let}~p = e$) is a no-op under $\vdash_d^{\text{pre}}$ — they introduce no forward-referenceable name. File-level processing is then the composition

<div markdown="0">
$$\text{processFile}(\overline{D}) \;=\; (\text{fold}_{\vdash_d}\; \overline{D}) \;\circ\; (\text{fold}_{\vdash_d^{\text{pre}}}\; \overline{D})$$
</div>

with both folds running left-to-right over the same declaration sequence. After the pre-pass, every type name is in `typedef` as a placeholder and every recursive **fn** is in Γ at its declared signature; the body-pass D-Type-Record / D-Type-Sum / D-Type-Sum-Opaque / D-Let-Top / D-LetPat-Top rules then run with the recursive references already resolvable through the pre-pass tables. Conflicts where the body-pass needs a resolved variant set against a still-placeholder name (e.g.\ [Exh-Sum](#Exh-Sum) inside a top-level **let** whose body matches against a sum that is declared later) are well-typed because the body-pass runs to completion *before* per-expression typing inside top-level **let** bodies fires the [Exh-Sum](#Exh-Sum) lookups.

The implementation realises this in `src/typecheck/check.nx`'s declaration-walk + `infer.nx::infer_let`'s "Pre-register for recursive lambdas" path; the spec's two-pass shape is the metatheoretic counterpart.

<a id="D-Type-Record"></a>

<div markdown="0">
$$\dfrac{
  D = \textbf{type}~x\langle \overline{\alpha} \rangle = \lbrace \overline{\ell : \tau} \rbrace \qquad
  \text{distinct}(\overline{\ell}) \qquad
  \forall \ell.\;\text{wfRef}(\tau_\ell) \wedge \neg\text{escapesRef}(\tau_\ell)
}{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}[\text{typedef}(x) \mathrel{:=} \forall \overline{\alpha}.\, \lbrace \overline{\ell : \tau} \rbrace]
} \;\textsc{D-Type-Record}$$
</div>

<a id="D-Type-Sum"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  D = \textbf{type}~x\langle \overline{\alpha} \rangle = c_1\,\overline{F_1} \mathbin{\vert} \ldots \mathbin{\vert} c_n\,\overline{F_n} \quad\text{where each}~\overline{F_i}~\text{is either}~(\overline{\ell_i : \tau_i})~\text{or empty} \\[2pt]
  \text{distinct}(c_1, \ldots, c_n) \qquad
  \forall i \in \lbrace 1,\ldots,n \rbrace.\;\overline{F_i} \neq \emptyset \implies \text{distinct}(\overline{\ell_i}) \\[2pt]
  \forall i.\;\forall \ell \in \overline{\ell_i}.\;\text{wfRef}(\tau_{i,\ell}) \wedge \neg\text{escapesRef}(\tau_{i,\ell}) \\[2pt]
  S_i = \begin{cases} \forall \overline{\alpha}.\,(\overline{\ell_i : \tau_i}) \to x\langle \overline{\alpha} \rangle;\,\lbrace\rbrace;\,\lbrace\rbrace & \text{if}~\overline{F_i}~\text{is non-empty (arity} \geq 1\text{)} \\ \forall \overline{\alpha}.\, x\langle \overline{\alpha} \rangle & \text{if}~\overline{F_i}~\text{is empty (nullary)} \end{cases}
  \end{array}
}{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}\!\begin{bmatrix} \Gamma & \mathrel{:=} & \Gamma,\, \overline{c_i :^{\omega} S_i} \\ \text{typedef}(x) & \mathrel{:=} & \forall \overline{\alpha}.\, x\langle \overline{\alpha} \rangle \\ \text{variants}(x) & \mathrel{:=} & \lbrace c_1, \ldots, c_n \rbrace \end{bmatrix}
} \;\textsc{D-Type-Sum}$$
</div>

D-Type-Sum simultaneously installs each constructor $c_i$ as an ω-bound polymorphic entry in Γ: an arrow type when the constructor has fields, a *value-typed* scheme when it is nullary (e.g.\ `None` in $\textbf{type}~\texttt{Option}\langle T \rangle = \texttt{None} \mathbin{\vert} \texttt{Some}(\textit{val}: T)$ is bound at $\forall T.\, \texttt{Option}\langle T \rangle$, not at $\forall T.\, () \to \texttt{Option}\langle T \rangle$). The value-typed form is what lets the surface form `None` (no parentheses) type-check as an expression via [T-Var](#T-Var) and as a pattern via [P-CtorNullary](#P-CtorNullary). $x$ is registered in `typedef`, and the variant set is recorded so that [Exh-Sum](#Exh-Sum) and [P-Ctor](#P-Ctor) / [P-CtorNullary](#P-CtorNullary) can read constructors by name.

<a id="D-Type-Sum-Opaque"></a>

D-Type-Sum-Opaque, alone among §3 rules, depends on the **current module being typed**. We thread the current module identity $M_\text{now}$ as an annotation on the declaration judgment, writing $M_\text{now} \vdash \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}'$ when the rule reads $M_\text{now}$. For every other rule in §3 the annotation is universally quantified ($M_\text{now}$ is unused), so we elide it from those rules' presentations.

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  D = \textbf{opaque type}~x\langle \overline{\alpha} \rangle = c_1\,\overline{F_1} \mathbin{\vert} \ldots \mathbin{\vert} c_n\,\overline{F_n} \quad\text{where each}~\overline{F_i}~\text{is either}~(\overline{\ell_i : \tau_i})~\text{or empty} \\[2pt]
  \text{distinct}(c_1, \ldots, c_n) \qquad
  \forall i \in \lbrace 1,\ldots,n \rbrace.\;\overline{F_i} \neq \emptyset \implies \text{distinct}(\overline{\ell_i}) \\[2pt]
  \forall i.\;\forall \ell \in \overline{\ell_i}.\;\text{wfRef}(\tau_{i,\ell}) \wedge \neg\text{escapesRef}(\tau_{i,\ell}) \\[2pt]
  S_i = \begin{cases} \forall \overline{\alpha}.\,(\overline{\ell_i : \tau_i}) \to x\langle \overline{\alpha} \rangle;\,\lbrace\rbrace;\,\lbrace\rbrace & \text{if}~\overline{F_i}~\text{is non-empty (arity} \geq 1\text{)} \\ \forall \overline{\alpha}.\, x\langle \overline{\alpha} \rangle & \text{if}~\overline{F_i}~\text{is empty (nullary)} \end{cases} \\[2pt]
  M_\text{defining}~\text{is the module in whose source}~D~\text{appears} \\[2pt]
  \mathcal{T}_\text{update} = \begin{cases} \mathcal{T}\!\begin{bmatrix} \Gamma & \mathrel{:=} & \Gamma,\, \overline{c_i :^{\omega} S_i} \\ \text{typedef}(x) & \mathrel{:=} & \forall \overline{\alpha}.\, x\langle \overline{\alpha} \rangle \\ \text{variants}(x) & \mathrel{:=} & \lbrace c_1, \ldots, c_n \rbrace \end{bmatrix} & \text{if}~M_\text{now} = M_\text{defining} \\[12pt] \mathcal{T}[\text{typedef}(x) \mathrel{:=} \forall \overline{\alpha}.\, x\langle \overline{\alpha} \rangle] & \text{otherwise} \end{cases}
  \end{array}
}{
  M_\text{now} \vdash \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}_\text{update}
} \;\textsc{D-Type-Sum-Opaque}$$
</div>

D-Type-Sum-Opaque restricts the visibility of the constructor entries and the `variants` set to the *defining module* $M_\text{defining}$: when $M_\text{now} = M_\text{defining}$, the rule fires the full sum-type effects (constructors in Γ, variant set populated, typedef registered); when $M_\text{now} \neq M_\text{defining}$ (the rule is processed during another module's typing, e.g.\ via an `import` that brought the projected $\mathcal{T}^{\text{export}}_{M_\text{defining}}$ in), only $\text{typedef}(x)$ enters — the constructor schemes and variant set are withheld. Importing code therefore cannot apply $c_i$ as a constructor ([T-App](#T-App) looks $c_i$ up in Γ and fails) or write a $c_i(\overline{\ell : p})$ pattern ([P-Ctor](#P-Ctor) also fails the lookup); construction and destructuring are only possible through the module's exported functions. The opaque modifier is accepted only on sum-type definitions in the surface grammar; record types and aliases have no opaque variant (`src/frontend/parse_topdef.nx::parse_type_def` reads `is_opaque` only for the enum branch). The nullary-variant case (e.g.\ $\textbf{opaque type}~\texttt{Set} = \texttt{Empty} \mathbin{\vert} \texttt{NonEmpty}(\textit{id}: \texttt{i64})$) follows the same two-branch $S_i$ split as [D-Type-Sum](#D-Type-Sum): `Empty` is installed at value scheme $\forall\overline{\alpha}.\, x\langle\overline{\alpha}\rangle$, matching the surface form where nullary constructors appear without parentheses and are used via [T-Var](#T-Var) / [P-CtorNullary](#P-CtorNullary).

<a id="D-External"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  D = \textbf{external}~x = \texttt{"} w \texttt{"} : \langle \overline{\alpha} \rangle (\overline{\ell : \tau}) \to \tau_r \\[2pt]
  \forall \ell.\;\text{wfRef}(\tau_\ell) \qquad \text{wfRef}(\tau_r) \qquad \neg\text{escapesRef}(\tau_r) \\[2pt]
  \forall i.\;\kappa_i = \text{kindOf}(\alpha_i,\;(\overline{\ell : \tau}) \to \tau_r;\,\lbrace\rbrace;\,\lbrace\rbrace) \quad\text{(see §Polymorphism Introduction)} \\[2pt]
  S = \forall \overline{\alpha_i{:}\kappa_i}.\,(\overline{\ell : \tau}) \to \tau_r;\,\lbrace\rbrace;\,\lbrace\rbrace \quad\text{(empty require / throws)}
  \end{array}
}{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}[\Gamma \mathrel{:=} \Gamma,\, x :^{\omega} S]
} \;\textsc{D-External}$$
</div>

External declarations bind a name $x$ to a fixed Wasm export $w$ at a stated arrow type. The type-parameter list $\langle \overline{\alpha} \rangle$ may be empty (monomorphic external) or non-empty (polymorphic in the same predicative System-F sense as [T-Let-PolyFn](#T-Let-PolyFn)): the parser accepts both forms (`parse_external_sig`'s `type_params` field). The require and throw rows are forced to empty because the Wasm side has no Nexus-level effects to track; capability access through an external is mediated by the surrounding `inject` if the external takes capability-shaped parameters. The mapping between $x$ and the Wasm symbol $w$ is consumed by the backend codegen — the type system observes only $S$.

<a id="D-Cap"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  D = \textbf{cap}~X~\textbf{do}~\overline{\textbf{fn}~\ell_j(\overline{\pi_j}) \to \kappa_j;\,\alpha_j;\,\beta_j}~\textbf{end} \\[2pt]
  X \notin \lbrace \texttt{Exn} \rbrace \cup \texttt{SysCaps} \cup \text{dom}(\text{methods}) \quad\text{(cap name fresh — Exn and system caps are reserved; see §Row Types)} \\[2pt]
  \text{distinct}(\overline{\ell_j \mid j \in J}) \quad\text{(method names are distinct across the cap)} \\[2pt]
  \forall j \in J.\;\text{distinct}(\text{labels}(\overline{\pi_j})) \quad\text{(each method's parameter labels are distinct)} \\[2pt]
  \forall j \in J.\;\forall i.\;\text{wfRef}(\pi_{j,i}) \quad \forall j \in J.\;\text{wfRef}(\kappa_j) \wedge \neg\text{escapesRef}(\kappa_j) \\[2pt]
  \forall j \in J.\;\text{wfCap}(\alpha_j) \wedge \text{wfThrow}(\beta_j) \quad\text{(per-method declared rows reference known caps / variants)}
  \end{array}
}{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}[\text{methods}(X) \mathrel{:=} \lbrace \ell_j : (\overline{\pi_j}) \to \kappa_j;\,\alpha_j;\,\beta_j \mid j \in J \rbrace]
} \;\textsc{D-Cap}$$
</div>

Cap declarations populate `methods` alone; they do not enter a value-level binding in Γ for $X$. $X$ becomes available as a row-entry symbol in $\rho_q$ via the *user-declared cap names* source described in §Row Types, and as a method-lookup namespace via [T-CapCall](#T-CapCall).

<a id="D-Exception"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  D = \textbf{exception}~C\,\overline{F} \qquad
  C \notin \lbrace \texttt{Exn} \rbrace \cup \texttt{SysCaps} \cup \text{dom}(\text{methods}) \cup \text{variants}(\texttt{Exn}) \quad\text{(constructor name fresh; reserved names rejected)} \\[2pt]
  \overline{F} \neq \emptyset \implies \text{distinct}(\overline{\ell}) \quad\text{(field labels within this constructor are distinct)} \\[2pt]
  S = \begin{cases} (\overline{\ell : \tau}) \to \texttt{Exn};\,\lbrace\rbrace;\,\lbrace\rbrace & \text{if}~\overline{F} = (\overline{\ell : \tau}),~\text{non-empty} \\ \texttt{Exn} & \text{if}~\overline{F}~\text{is omitted (nullary)} \end{cases}
  \end{array}
}{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}\!\begin{bmatrix} \Gamma & \mathrel{:=} & \Gamma,\, C :^{\omega} S \\ \text{variants}(\texttt{Exn}) & \mathrel{:=} & \text{variants}(\texttt{Exn}) \cup \lbrace C \rbrace \end{bmatrix}
} \;\textsc{D-Exception}$$
</div>

Exception declarations admit both the parameterised form $\textbf{exception}~\texttt{NotFound}(\textit{path}: \texttt{string})$ — installed as an arrow constructor — and the nullary form $\textbf{exception}~\texttt{MissingMain}$ (no parentheses on declaration or use) — installed as a value of type `Exn`, matching the *"Zero-field exceptions omit parentheses"* convention from [Exception Groups](../exception-groups). The nullary form is the unique reason [P-CtorNullary](#P-CtorNullary) exists; the parameterised form goes through ordinary [P-Ctor](#P-Ctor). The freshness premise $C \notin \text{variants}(\texttt{Exn})$ is the analogue of [D-Type-Sum](#D-Type-Sum)'s $\text{distinct}(c_1,\ldots,c_n)$ for the open `Exn` union: it prevents two incompatible schemes from co-inhabiting Γ under the same constructor name across any reachable module boundary.

Exception declarations are the only rule that mutates a *pre-existing* table entry: $\text{variants}(\texttt{Exn})$ is the union of every **exception** declaration reached from the program root. The *cross-module extensibility hazard* called out in [T-TryCatch](#T-TryCatch) — a closed-enumeration catch over a `Exn` row becoming inexhaustive when a downstream module adds a variant — is exactly the cross-module application of D-Exception against the importer's $\text{variants}(\texttt{Exn})$.

<a id="D-ExceptionGroup"></a>

<div markdown="0">
$$\dfrac{
  \begin{array}{l}
  D = \textbf{exception group}~G = C_1 \mathbin{\vert} \ldots \mathbin{\vert} C_n \\[2pt]
  \text{distinct}(C_1, \ldots, C_n) \quad\text{(member names are distinct within this group declaration)} \\[2pt]
  \forall i \in \lbrace 1,\ldots,n \rbrace.\; C_i \in \text{variants}(\texttt{Exn}) \quad\text{(every member is a declared exception constructor)}
  \end{array}
}{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}[\text{members}(G) \mathrel{:=} \lbrace C_1, \ldots, C_n \rbrace]
} \;\textsc{D-ExceptionGroup}$$
</div>

Group declarations affect only the parse-time expansion table `members`. No typing rule reads `members` directly — the parser uses it to fan out $\textbf{catch}~\vert~G \to \ldots$ into one arm per constructor before the rule fires. The `distinct` premise prevents the same constructor from appearing twice in a group's member list (a duplicate would silently produce redundant catch arms). The membership premise $C_i \in \text{variants}(\texttt{Exn})$ ensures every listed name is a previously declared exception constructor, not an undeclared identifier or another group name (see nexus-8n1b).

<a id="D-Let-Top"></a>

<div markdown="0">
$$\dfrac{
  \Gamma;\,\lbrace\rbrace;\,\bot \;\vdash_s\; \textbf{let}~\mu\,x = e \;:\; \Gamma' \mathbin{!} \lbrace\rbrace
}{
  \mathcal{T} \;\vdash_d\; \textbf{let}~\mu\,x = e \;\Rightarrow\; \mathcal{T}[\Gamma \mathrel{:=} \Gamma']
} \;\textsc{D-Let-Top}$$
</div>

<a id="D-LetPat-Top"></a>

<div markdown="0">
$$\dfrac{
  \Gamma;\,\lbrace\rbrace;\,\bot \;\vdash_s\; \textbf{let}~p = e \;:\; \Gamma' \mathbin{!} \lbrace\rbrace
}{
  \mathcal{T} \;\vdash_d\; \textbf{let}~p = e \;\Rightarrow\; \mathcal{T}[\Gamma \mathrel{:=} \Gamma']
} \;\textsc{D-LetPat-Top}$$
</div>

A top-level **let** is type-checked as an ordinary statement under an empty ambient capability row, an empty effect row, and a $\bot$ return-type (no enclosing function): D-Let-Top reuses [T-Let](#T-Let), [T-Let-PolyFn](#T-Let-PolyFn), or [T-Let-Alias](#T-Let-Alias) according to the RHS shape; D-LetPat-Top covers destructuring binders by reusing [T-LetPat](#T-LetPat) (or [T-LetPat-Diverge](#T-LetPat-Diverge) when the RHS is a **throw**). The pure-row premise rejects top-level expressions that require capabilities the program root cannot grant; an **inject** at the top level is the recommended way to introduce capabilities for an evaluating block.

Self-recursive (`let factorial = fn ... factorial(n: n - 1) ... end`) and mutually-recursive top-level functions are handled by the unified two-phase scheme stated at the top of this section: [D-Let-Forward](#D-Let-Forward) seeds Γ with each `let x = fn ...`'s declared signature scheme during the $\vdash_d^{\text{pre}}$ pre-pass; D-Let-Top / D-LetPat-Top then run with that environment, so a self-call $x(\ldots)$ or mutual call $g(\ldots)$ inside $f$'s body resolves through [T-Var](#T-Var). `let x = e` whose RHS is *not* a **fn** literal (data binding, computed value) does not participate in $\vdash_d^{\text{pre}}$ and cannot be self-referential through the top-level `let` channel — recursive data constructors go through [D-Type-Sum](#D-Type-Sum)'s forward registration instead.

### Visibility (export)

Every declaration above admits an optional `export` prefix in the surface syntax (`export let foo = ...`, `export type Foo = ...`, etc.). The modifier does *not* alter the rule's effect on Γ / `typedef` / `methods` / `variants` / `members` within the declaring module — `export` and non-`export` declarations populate those five components identically *inside* their module. The modifier governs the sixth component, `exports`:

<div markdown="0">
$$\dfrac{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}'
}{
  \mathcal{T} \;\vdash_d\; \textbf{export}~D \;\Rightarrow\; \mathcal{T}'[\text{exports} \mathrel{:=} \text{exports} \cup \text{declNames}(D)]
} \;\textsc{D-Export}$$
</div>

$\text{declNames}(D)$ is the **set** of names a declaration introduces:

<div markdown="0">
$$\begin{array}{rcl}
\text{declNames}(\textbf{let}~\mu\,x = e) & = & \lbrace x \rbrace \\
\text{declNames}(\textbf{let}~p = e) & = & \text{bv}(p) \\
\text{declNames}(\textbf{type}~X\langle \overline{\alpha} \rangle = \lbrace \overline{\ell : \tau} \rbrace) & = & \lbrace X \rbrace \quad (\text{record}) \\
\text{declNames}(\textbf{type}~X\langle \overline{\alpha} \rangle = c_1\,\overline{F_1} \mathbin{\vert} \ldots \mathbin{\vert} c_n\,\overline{F_n}) & = & \lbrace X, c_1, \ldots, c_n \rbrace \quad (\text{sum}) \\
\text{declNames}(\textbf{opaque type}~X\langle \overline{\alpha} \rangle = c_1\,\overline{F_1} \mathbin{\vert} \ldots) & = & \lbrace X \rbrace \quad (\text{opaque sum: constructors withheld}) \\
\text{declNames}(\textbf{exception}~C\,\overline{F}) & = & \lbrace C \rbrace \\
\text{declNames}(\textbf{exception group}~G = \ldots) & = & \lbrace G \rbrace \\
\text{declNames}(\textbf{cap}~X~\textbf{do}~\ldots~\textbf{end}) & = & \lbrace X \rbrace \quad (\text{cap methods are accessed via}~X.\ell\text{, not as standalone names}) \\
\text{declNames}(\textbf{external}~x = w : \ldots) & = & \lbrace x \rbrace
\end{array}$$
</div>

D-Export is a *wrapper* — for any declaration form $D$ admitted by §3's other rules, $\textbf{export}~D$ runs $D$'s rule unchanged and additionally records the bound name(s) in `exports`. The set-valued `declNames` captures the multi-name forms cleanly: $\textbf{export type Option<T> = None | Some(val: T)}$ exports $\lbrace \texttt{Option}, \texttt{None}, \texttt{Some} \rbrace$; $\textbf{export opaque type Set = Set(id: i64)}$ exports only $\lbrace \texttt{Set} \rbrace$ (the constructor is hidden by [D-Type-Sum-Opaque](#D-Type-Sum-Opaque) and therefore must also be excluded from `exports`). The `exports` set is the **inter-module visibility gate**: when another module imports from this one, only entries whose names are in `exports` enter the importing $\mathcal{T}$ (see [imports.md](../imports)).

D-Type-Sum-Opaque is the one place where module identity directly enters a typing rule: the constructor visibility depends on whether the typing-time module is the defining module $M$. All other rules are module-local in the trivial sense (their effects apply inside whichever module is being type-checked).

### Program Entry Point

A complete program is a (possibly multi-file) declaration sequence whose root module declares a top-level binding named *main*. The entry point carries four constraints not enforced by the per-declaration rules above:

<div markdown="0">
$$\textbf{P9}~\text{(Main well-formedness)}.\quad \text{wfMain}(\mathcal{T}) \;\Longleftrightarrow\;$$
</div>

<div markdown="0">
$$\quad \exists~\textit{main} \in \text{dom}(\Gamma).\;\Gamma(\textit{main}) = (\omega,\, \text{mono}((\,) \to \texttt{unit};\,\rho_q;\,\lbrace\rbrace)) \;\wedge\; \rho_q \subseteq \texttt{SysCaps} \;\wedge\; \textit{main} \notin \text{exports}(\mathcal{T})$$
</div>

The four conjuncts encode the constraints stated narratively in [semantics.md](../semantics) §Entrypoint and [effects.md](../effects) §Main Constraints:

- **Signature** — $(\,) \to \texttt{unit}$ with no arguments and a `unit` return.
- **Empty throws row** — `main`'s declared $\rho_e$ is $\lbrace\rbrace$. Every exception that the program may throw must be handled by an inner **try** before propagating out of `main`; the runtime has no exception consumer outside of `main`.
- **Require subset of SysCaps** — `main` may declare any subset of system capabilities (`PermFs`, `PermNet`, etc.) which the runtime grants from the WASI environment. User-declared cap names may **not** appear in `main`'s $\rho_q$ — there is no enclosing **inject** to provide them.
- **Non-exported** — `main` is not in $\text{exports}(\mathcal{T})$. Other modules cannot import `main`; it is a runtime-side hook, not part of any module's API.

A program is **well-formed** iff $\text{wfMain}(\mathcal{T})$ holds for the root module's resolved $\mathcal{T}$. If the property fails — `main` is missing, has the wrong signature, declares a non-empty throws row, requires a non-system capability, or is exported — the type-checker rejects the program at the program-entry check after the per-module folds complete. This is the only program-global property in §3; every other rule and property is module-local.

{% endraw %}
