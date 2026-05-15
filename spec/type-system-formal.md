---
layout: default
title: Type System — Formal Rules
---

{% raw %}
# Type System — Formal Rules

This document defines the typing rules of Nexus as inference rules. It serves as a specification for property-based testing and as a reference for future mechanization.

> **Terminology — port ≡ cap.** This document uses **port** as the abstract name for a capability interface (e.g. $\textbf{port}\;\texttt{Logger}$, $\text{methods}(x)$, [T-PortCall](#T-PortCall)). The corresponding surface keyword is `cap` — see [effects.md](./effects) and [syntax.md](./syntax). The two names refer to the same construct: a top-level declaration that introduces a row-entry symbol and a method signature table. The formal rules use "port" uniformly; readers should treat any `cap X do ... end` declaration in surface code as a `port X` introduction in $\Gamma$.

## 1. Syntax

The abstract syntax of the core calculus. See [Syntax](../syntax) for the full surface syntax.

### Terms

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
  & \mid & \textbf{raise}~e & \text{raise exception} \\
  & \mid & \textbf{handler}~x~[\textbf{require}~\rho]~\textbf{do}~\overline{\ell = e}~\textbf{end} & \text{handler (each } e \text{ is a lambda)} \\[6pt]
s & ::= & \textbf{let}~\mu\,x = e & \text{binding} \\
  & \mid & \textbf{let}~p = e & \text{destructuring} \\
  & \mid & \textbf{return}~e & \text{return} \\
  & \mid & \mathord{\sim}x \leftarrow e & \text{assignment} \\
  & \mid & \textbf{inject}~\overline{h}~\textbf{do}~\overline{s}~\textbf{end} & \text{capability injection} \\
  & \mid & \textbf{try}~\overline{s}~\textbf{catch}~\overline{p \to s}~\textbf{end} & \text{exception handling} \\
  & \mid & \textbf{while}~e~\textbf{do}~\overline{s}~\textbf{end} & \text{while loop} \\
  & \mid & e & \text{expression statement} \\[6pt]
p & ::= & x & \text{variable pattern (} x \notin \text{dom}(\Gamma)~\text{or}~\Gamma(x)~\text{is not a constructor scheme)} \\
  & \mid & \_ \mid n & \text{wildcard / literal pattern} \\
  & \mid & c & \text{nullary constructor pattern (} c \in \text{dom}(\Gamma),~\text{arity 0)} \\
  & \mid & c(\overline{\ell : p}) & \text{constructor pattern (} c \in \text{dom}(\Gamma),~\text{arity} \geq 1 \text{)} \\
  & \mid & \lbrace \overline{\ell : p} \rbrace & \text{record pattern} \\
  & \mid & p_1 \mathbin{\vert} p_2 & \text{or-pattern (alternation)}
\end{array}$$

Bare identifiers in pattern position are disambiguated **by $\Gamma$-lookup**: if the identifier resolves to a constructor scheme in $\Gamma$, it parses as a nullary constructor pattern (via [P-CtorNullary](#P-CtorNullary)); otherwise it parses as a variable binder (via [P-Var](#P-Var)). The split mirrors the surface convention "zero-field exceptions omit parentheses both at declaration and at match" (see [Exception Groups](../exception-groups)) and matches `src/typecheck/exhaustive.nx`'s pattern dispatch, which checks $\text{variants}$ before treating a bare identifier as a binder.

The core calculus omits several surface language features that are either desugared or handled as environment preconditions:

- **Constructors** ($c$) — assumed predefined in $\Gamma$ with a function type (n-ary) or a value type (nullary). Application $f(\overline{\ell : e})$ covers both function calls and constructor application. In patterns, $c$ is syntactically distinguished from variable patterns $x$.
- **Port declarations** — top-level declarations that populate $\Gamma$ with method signatures. Not terms; they are preconditions on $\Gamma$.
- **Exception / exception group declarations** — extend the $\texttt{Exn}$ sum type in $\Gamma$. Same status as port declarations.
- **For loops** — present in the surface syntax but desugared to a $\textbf{while}$ with an explicit index counter and bound; the formal rule covers only $\textbf{while}$ (see [T-While](#T-While)).
- **Import statements** — resolved before type checking; not modeled here.
- **List literals and the $\mathord{::}$ cons operator** — desugared to the prelude $\texttt{List}$ enum: $[\,]$ becomes $\texttt{Nil}$, $e_h :: e_t$ becomes $\texttt{Cons}(v: e_h,\, \text{rest}: e_t)$, $[e_1, \ldots, e_n]$ becomes a right-associated chain of $\texttt{Cons}$ ending in $\texttt{Nil}$. The list type $[\tau]$ is an alias for $\texttt{List}\langle\tau\rangle$. List patterns desugar identically. Typing and exhaustiveness are then handled by [T-App](#T-App) (constructor application), [P-Ctor](#P-Ctor), and [Exh-Sum](#Exh-Sum) — no list-specific rules are needed.
- **Array values** — the linear type $[\lvert\tau\rvert]$ has no in-core introduction or elimination rule. Construction, indexing, length, mutation, and iteration go through stdlib intrinsic functions (e.g. $\texttt{array\_init} : (n: \texttt{i64}, v: \tau) \to [\lvert\tau\rvert]$, $\texttt{array\_get} : (a: \&[\lvert\tau\rvert], i: \texttt{i64}) \to \tau$) that are populated into $\Gamma$ as preconditions. The type system observes only their declared signatures via [T-App](#T-App). Array exhaustiveness in [match](#T-Match) is handled by allowing only wildcard-like patterns (a value-level constructor for arrays is not exposed).

### Types

$$\begin{array}{rcll}
\tau & ::= & b \mid \texttt{intlit} \mid \texttt{floatlit} & \text{base type / inference-internal numeric} \\
    & \mid & \alpha \mid {?}\alpha & \text{type variable / unification variable} \\
    & \mid & (\overline{\ell : \tau}) \to \tau;\, \rho;\, \rho & \text{function (params, return, capability, effect)} \\
    & \mid & \lbrace \overline{\ell : \tau} \rbrace & \text{record} \\
    & \mid & x\langle \overline{\tau} \rangle & \text{named type (e.g.\ } \texttt{Option}\langle\texttt{i64}\rangle\text{)} \\
    & \mid & [\tau] \mid [\lvert\,\tau\,\rvert] & \text{list / array (array is always linear)} \\
    & \mid & \%\tau \mid \mathord{\sim}\tau \mid \&\tau \mid @\tau & \text{linear / mutable ref / borrow / lazy} \\
    & \mid & \textbf{handler}\;x\;\rho & \text{handler for port } x \\[6pt]
b & ::= & \texttt{i32} \mid \texttt{i64} \mid \texttt{f32} \mid \texttt{f64} \mid {} & \\
  &     & \texttt{bool} \mid \texttt{char} \mid \texttt{string} \mid \texttt{unit} & \\[6pt]
\eta & ::= & X \mid \texttt{Exn} & \text{row entry (an identifier or the catch-all sentinel)} \\[6pt]
\rho & ::= & \lbrace \overline{\eta} \rbrace \mid \lbrace \overline{\eta} \mid {?}r \rbrace & \text{row (closed / open with row variable } {?}r\text{)}
\end{array}$$

We write $\overline{X}$ for a finite sequence $X_1, \ldots, X_n$. $\alpha, \beta, \gamma$ range over type variables; ${?}\alpha$ denotes a type unification variable introduced during inference (the distinction matters in generalization). $r, s$ range over **row variables** (the tail position of an open row $\lbrace \overline{\tau} \mid r \rbrace$); ${?}r$ denotes a row unification variable. $\lvert\overline{X}\rvert$ denotes the length of a sequence.

The statement judgment $\Gamma;\,\rho_q;\,\tau_r \vdash_s s : \Gamma' \mathbin{!} \rho_e$ uses an **extended return-context** $\tau_r \in \tau \cup \lbrace \bot \rbrace$. The sentinel $\bot$ marks "no enclosing function": it appears only at top-level statement contexts ([D-Let-Top](#D-Let-Top), [D-LetPat-Top](#D-LetPat-Top)) where there is no function to return to. $\bot$ is *not* a type — it is not a member of $\tau$ in the grammar above and never appears in $\Gamma$, in row entries, or as the result of [inst](#inst). The only rule that inspects $\tau_r$ is [T-Return](#T-Return), which carries the side condition $\tau_r \neq \bot$ to reject $\textbf{return}$ statements at module scope.

$\texttt{intlit}$ and $\texttt{floatlit}$ are **singleton kind-restricted constants** assigned to integer and float literals before their concrete type is known. They are *not* fresh per literal occurrence: every $n$ in source code is typed at the same shared $\texttt{intlit}$ symbol, every $f$ at the same $\texttt{floatlit}$. Resolution proceeds in two stages: (1) any unification of $\texttt{intlit}$ with a concrete type $\tau \in \text{kind}(\texttt{intlit})$ emits a substitution $\lbrace \texttt{intlit} := \tau \rbrace$ via [U-IntLit](#U-IntLit) / [U-FloatLit](#U-FloatLit), which propagates to every literal occurrence simultaneously (matching the implementation in `src/typecheck/infer.nx`); (2) if the substitution chain still leaves an $\texttt{intlit}$/$\texttt{floatlit}$ at a binding site, $\text{default}$ in [T-Let](#T-Let) pins it to $\texttt{i64}$/$\texttt{f64}$. The shared symbol behavior is harmless in practice because every well-typed program's literals either get pinned to the same concrete type by surrounding context or get defaulted at the nearest let — distinct numeric "shapes" (e.g. an $\texttt{i32}$ literal next to an $\texttt{i64}$ one) are forced into separate bindings before they meet at a unification site. The $\text{kind}(\cdot)$ of $\texttt{intlit}$ is $\lbrace \texttt{i32}, \texttt{i64} \rbrace$ and of $\texttt{floatlit}$ is $\lbrace \texttt{f32}, \texttt{f64} \rbrace$ — unification with any other type fails.

### Modalities

The modality $\mu$ determines how a binding is introduced and used. $\varepsilon$ (plain) is elided in notation; we write $x$ for $\varepsilon\,x$. The modalities $\%$, $\mathord{\sim}$, $\&$, $@$ correspond to the surface sigils `%x`, `~x`, `&x`, `@x`. A binding with type $\%\tau$, $@\tau$, or $[\lvert\,\tau\,\rvert]$ has usage $q = 1$ (linear); all others have $q = \omega$. $@\tau$ denotes a suspended computation (one-shot thunk). $\mathord{\sim}\tau$ is a mutable reference cell. $\&\tau$ is a read-only borrow.

In expression position, $\mu\,x$ with $\mu \in \{\varepsilon, \%, \mathord{\sim}\}$ is a variable reference. $@e$ (force) and $\&x$ (borrow) subsume the $\mu = @$ and $\mu = \&$ cases and are listed as separate expression forms since force applies to any expression.

### Row Types

The row type $\rho$ is used for both the effect position ($\rho_e$, in $\textbf{throws}$) and the capability position ($\rho_q$, in $\textbf{require}$) of function types. Both positions share the same structure — row extension, unification, row variable instantiation — so no separate syntactic category is needed. The distinction is semantic: $\rho_e$ ranges over exception types, $\rho_q$ ranges over a **mixed alphabet** of system capabilities and user-declared port names (defined immediately below). No kind system enforces the row-position invariant; it is maintained by the introduction rules (T-Raise adds to $\rho_e$; [T-Inject](#T-Inject) and port/cap declarations add to $\rho_q$).

In the current language, the only effect is checked exceptions. $\rho_e$ is a row of **exception-constructor names**: each user `exception C(...)` declaration extends the global $\texttt{Exn}$ sum with constructor $C$ and simultaneously introduces $C$ as a row-entry symbol usable in $\textbf{throws}$ rows. So $\rho_e$ may be $\lbrace\rbrace$ (pure), a closed set of specific variants $\lbrace C_1, \ldots, C_n \rbrace$, an open variant row $\lbrace C_1, \ldots, C_n \mid {?}r \rbrace$, or contain the catch-all sentinel $\texttt{Exn}$ (see below).

$\texttt{Exn}$ itself is the **top of the exception lattice** — the type assigned to a binding that captures *any* exception (e.g. $\textbf{catch}~e \to \ldots$ binds $e : \texttt{Exn}$). $\texttt{Exn}$ surfaces as a row entry only when re-raising such a catch-all binding: $\textbf{raise}~e$ for $e : \texttt{Exn}$ emits $\lbrace \texttt{Exn} \rbrace$, indicating "may raise any variant". Specific-variant rows $\lbrace C_i \rbrace$ are subsumed by $\lbrace \texttt{Exn} \rbrace$ via [U-Row-Exn](#U-Row-Exn) below; otherwise rows unify by entry equality (no implicit subtyping).

Exception groups (`exception group G = C_1 | C_2 | \ldots`, see [Exception Groups](../exception-groups)) are syntactic shortcuts: anywhere $G$ appears in a row position or a catch-arm pattern, it expands to its declared member set $\lbrace C_1, C_2, \ldots \rbrace$ at parse time. The formal rules never observe groups directly — only their expansions.

The capability row $\rho_q$ admits two disjoint sources of entries:

1. **System capabilities** — the closed set $\lbrace \texttt{PermFs}, \texttt{PermNet}, \texttt{PermConsole}, \texttt{PermRandom}, \texttt{PermClock}, \texttt{PermProc}, \texttt{PermEnv} \rbrace$ — corresponding to WASI interface grants at runtime. See [WASM and WASI](../../env/wasm) for the complete mapping.
2. **User-declared port names** — each $\textbf{port}\;X\;\textbf{do}\;\ldots\;\textbf{end}$ (also written $\textbf{cap}\;X$ in [effects.md](../effects)/[syntax.md](../syntax); the two surface keywords name the same construct) introduces $X$ as a row-entry symbol usable in $\textbf{require}$ rows. [T-Inject](#T-Inject) extends $\rho_q$ with $X$ when an $X$-implementing handler is injected; [T-PortCall](#T-PortCall) reads $x \in \rho_q$ off this row to authorize the call.

These two sources share the row vocabulary because $\rho_q$ unification, weakening, and `require` checking treat both kinds of entries uniformly. The disjointness is by declaration site: system-capability names are reserved (parser rejects redeclaration); port/cap names are user-defined and live in the same namespace as type/term identifiers.

Let $\texttt{SysCaps} = \lbrace \texttt{PermFs}, \texttt{PermNet}, \texttt{PermConsole}, \texttt{PermRandom}, \texttt{PermClock}, \texttt{PermProc}, \texttt{PermEnv} \rbrace$. The well-formedness predicate

$$\text{wfCap}(\rho_q) \;\Longleftrightarrow\; \forall X \in \overline{\eta}.\;X \in \texttt{SysCaps} \cup \text{dom}(\text{methods}) \quad\text{where}~\rho_q = \lbrace \overline{\eta} \rbrace~\text{or}~\lbrace \overline{\eta} \mid {?}r \rbrace$$

requires every named entry of a capability row to be either a system capability or a port previously declared by [D-Port](#D-Port) (which populates $\text{methods}$). Row tail variables ${?}r$ are unconstrained — they stand for "any further entries" and are pinned by unification against a closed-row context, where the pinned content is itself well-formed by transitivity.

$\text{wfCap}$ is checked at every **introduction site** of a $\rho_q$ row: the require clause on a $\textbf{fn}$ arrow ([T-Lambda](#T-Lambda)), the optional require annotation on a $\textbf{handler}$ ([T-Handler](#T-Handler)), and the per-method declared require row inside [D-Port](#D-Port). Use sites ([T-App](#T-App), [T-PortCall](#T-PortCall), [T-Inject](#T-Inject)) operate on already-well-formed rows and need not re-check. Without $\text{wfCap}$ at the introduction sites, a typo such as `require { Logr }` (intended `Logger`) would propagate as an uninhabitable row entry and surface only at a use site that happens to look it up — moving the diagnostic far from the source of the typo.

**Notation note.** Earlier sections (and most rules below) write row entries as $\overline{\tau}$ rather than the precise $\overline{\eta}$. The two conventions are interchangeable: $\eta$ is the metavariable for "row entry" (an identifier or the $\texttt{Exn}$ sentinel), and the $\tau$ notation is a legacy from when rows were typed at the outer-syntactic level. Wherever a row appears, the entries are semantically constrained to be identifiers; type-grammar productions like $\%\sigma$ or $(\overline{\ell:\tau}) \to \tau_r$ never appear as row entries and are rejected by the parser. The wf-checks above pin this constraint formally.

$\rho_e$ (throws row) carries an analogous well-formedness condition: every named entry must be a constructor of $\texttt{Exn}$ — i.e.\ in $\text{variants}(\texttt{Exn})$ — or the catch-all sentinel $\texttt{Exn}$ itself. We write this as $\text{wfThrow}(\rho_e)$ and rely on the same introduction-site discipline (every $\textbf{throws}$ annotation passes through one of the introduction rules).

### Row Set Operations

The typing rules use three set-like operations on rows: subset ($\subseteq$), entry-name set difference ($\setminus$), and membership ($\in$). Each is defined uniformly over closed and open rows. Where a row tail variable ${?}r$ appears, the operation is interpreted *up to row unification*: it holds iff there is a substitution of the unification tails that makes the closed-row equation hold, and that substitution is committed as a side-effect (the same convention as elsewhere in §Unification).

**Subset** ($\rho_1 \subseteq \rho_2$).

$$\begin{array}{rcl}
\lbrace \overline{\tau_1} \rbrace \subseteq \lbrace \overline{\tau_2} \rbrace & \Longleftrightarrow & \overline{\tau_1} \subseteq \overline{\tau_2}~\text{(multiset inclusion)} \\
\lbrace \overline{\tau_1} \rbrace \subseteq \lbrace \overline{\tau_2} \mid {?}r \rbrace & \Longleftrightarrow & \exists \overline{\tau'}.\;{?}r \mathrel{:=} \overline{\tau'},\;\overline{\tau_1} \subseteq \overline{\tau_2} \cup \overline{\tau'} \\
\lbrace \overline{\tau_1} \mid {?}r \rbrace \subseteq \lbrace \overline{\tau_2} \rbrace & \Longleftrightarrow & {?}r \mathrel{:=} \lbrace\rbrace,\;\overline{\tau_1} \subseteq \overline{\tau_2} \\
\lbrace \overline{\tau_1} \mid {?}r_1 \rbrace \subseteq \lbrace \overline{\tau_2} \mid {?}r_2 \rbrace & \Longleftrightarrow & \overline{\tau_1} \subseteq \overline{\tau_2} \cup \overline{\tau'},\;{?}r_1 \mathrel{:=} \lbrace \overline{\tau''} \mid {?}r_2 \rbrace
\end{array}$$

The open-on-the-right cases refine ${?}r$ to absorb the entries missing on its side; the open-on-the-left cases pin ${?}r_1$ so that its (yet unknown) entries can only come from what the right side already provides (closed) or from ${?}r_2$ (open). Concretely: at the call to [T-Inject](#T-Inject), $\rho_i \subseteq \rho_q$ with $\rho_i = \lbrace \texttt{Logger} \mid {?}r_1 \rbrace$ and $\rho_q = \lbrace \texttt{Logger}, \texttt{Fs} \rbrace$ refines ${?}r_1 \mathrel{:=} \lbrace\rbrace$ — the handler's row-poly tail collapses because the ambient row is closed.

**Set difference** ($\rho \setminus S$ where $S$ is a name set). This is a syntactic transformation; it does not constrain unification variables. The tail (if any) is preserved verbatim:

$$\rho \setminus S = \begin{cases}
\lbrace \overline{\tau} \setminus S \rbrace & \text{if}~\rho = \lbrace \overline{\tau} \rbrace \\
\lbrace (\overline{\tau} \setminus S) \mid {?}r \rbrace & \text{if}~\rho = \lbrace \overline{\tau} \mid {?}r \rbrace
\end{cases}$$

Reading: a catch arm subtracts caught-variant names from the *known* part of the try-body's throws row; whatever the tail ${?}r$ stands for (variants the body could raise that the typer hasn't pinned yet) is forwarded unchanged into the residual. [T-TryCatch](#T-TryCatch)'s $\rho_\text{residual}$ uses exactly this operation; the catch-all carve-out additionally subtracts $\texttt{Exn}$.

**Membership** ($x \in \rho$).

$$\begin{array}{rcl}
x \in \lbrace \overline{\tau} \rbrace & \Longleftrightarrow & x \in \overline{\tau}~\text{(set membership)} \\
x \in \lbrace \overline{\tau} \mid {?}r \rbrace & \Longleftrightarrow & x \in \overline{\tau} \quad\text{or}\quad {?}r \mathrel{:=} \lbrace x \mid {?}r' \rbrace~(\text{fresh}~{?}r')
\end{array}$$

The open-row branch may pin ${?}r$ to expose the missing entry; this matches the way [T-PortCall](#T-PortCall)'s $x \in \rho_q$ premise admits a call whose port is not yet visible in the ambient row but can be introduced by refining the row tail.

These three definitions all reduce to row unification at base; their separate names exist only because the typing rules read more naturally when "is in / is contained / minus" appear instead of bare $\text{unify}$.

---

## 2. Typing Rules

### Environment and Usage

$$S ::= \forall \overline{\alpha}.\,\tau \qquad q \in \lbrace 1, \omega \rbrace \qquad \Gamma ::= \lbrace\; \overline{x :^{q} S} \;\rbrace$$

$S$ is a type scheme. Each binding in $\Gamma$ carries a **usage** annotation $q$: $1$ (must be used exactly once) or $\omega$ (may be used any number of times). The sigils $\%$ and $@$ introduce bindings with $q = 1$; all others have $q = \omega$.

The split operation $\Gamma_1 \otimes \Gamma_2 = \Gamma$ distributes bindings to sub-derivations. For each $x :^{q} S \in \Gamma$, the split assigns $x :^{q_1} S \in \Gamma_1$ and $x :^{q_2} S \in \Gamma_2$ according to:

$$\begin{array}{c|ccc}
q_1 + q_2 = q & q_2 = \cdot & q_2 = 1 & q_2 = \omega \\
\hline
q_1 = \cdot & \cdot & 1 & \omega \\
q_1 = 1 & 1 & — & — \\
q_1 = \omega & \omega & — & \omega
\end{array}$$

$\cdot$ means the binding is absent from that side of the split. A linear binding ($q = 1$) splits as $(1, \cdot)$ or $(\cdot, 1)$ — the choice of which side receives it is arbitrary (determined by the derivation). An unrestricted binding ($q = \omega$) splits as $(\omega, \omega)$ — both sides share it. "$—$" is forbidden ($1 + 1$ would use a linear resource twice).

$\Gamma$ is a **finite partial map** from binder names to $(q, S)$ pairs. There is at most one entry per name; shadowing within a single $\Gamma$ does not occur because env extension by comma overwrites a same-name binding (the inner binder hides the outer at the term-syntax level; the sequence-level $\text{fv}$ already strips shadowed names from a tail's free set, see §Free Variables). The following operations are defined on $\Gamma$ and used throughout the typing rules:

$$\begin{array}{rcl}
\text{dom}(\Gamma) & = & \lbrace x \mid (x :^q S) \in \Gamma \rbrace \quad\text{(a name set)} \\[2pt]
\Gamma(x) & = & \text{the unique } (q, S)~\text{such that}~(x :^q S) \in \Gamma; \text{ undefined if}~x \notin \text{dom}(\Gamma) \\[2pt]
\Gamma \setminus \lbrace x \rbrace & = & \lbrace y :^q S \in \Gamma \mid y \neq x \rbrace \\[2pt]
\Gamma_1 \setminus \Gamma_2 & = & \lbrace x :^q S \in \Gamma_1 \mid x \notin \text{dom}(\Gamma_2) \rbrace \\[2pt]
\Gamma_1 \uplus \Gamma_2 & = & \begin{cases} \Gamma_1 \cup \Gamma_2 & \text{if}~\text{dom}(\Gamma_1) \cap \text{dom}(\Gamma_2) = \emptyset \\ \text{undefined} & \text{otherwise} \end{cases} \\[2pt]
\Gamma,\, x :^q S & = & (\Gamma \setminus \lbrace x \rbrace) \cup \lbrace x :^q S \rbrace \quad\text{(comma is overwriting extension)}
\end{array}$$

Two readings follow from these definitions:

- **$\Gamma_i \setminus \Gamma$ in the pattern rules** ([P-Ctor](#P-Ctor), [P-Record](#P-Record), [P-Or](#pattern-matching)) reads as "the bindings $\Gamma_i$ introduced beyond $\Gamma$". Since each $\Gamma_i$ extends the same input $\Gamma$ with a few new pattern binders, $\Gamma_i \setminus \Gamma$ is exactly the new-binding contribution of one sub-pattern; $\biguplus_i (\Gamma_i \setminus \Gamma)$ then asserts the new binders are mutually disjoint across sub-patterns.
- **$\otimes$-split is non-deterministic.** The table relates $(q_1, q_2)$ to $q$ pointwise; multiple satisfying choices exist when $q = 1$ (either $(1, \cdot)$ or $(\cdot, 1)$). The spec rule is satisfied if *any* choice makes both sub-derivations type-check. The implementation makes a single deterministic pick (`src/typecheck/infer.nx`'s left-then-right scan); soundness does not depend on which.

#### Linear consumption and the env residual $\Gamma \setminus\!\!\setminus e$

The expression judgment $\Gamma;\,\rho_q \vdash_e e : \tau \mathbin{!} \rho_0$ has no explicit output environment, but consumption of linear bindings *is* operational — it is realised by the $\otimes$-split mechanism at every multi-premise rule.

**Operational role of $\otimes$-split.** Every expression rule that has multiple expression premises ([T-App](#T-App), [T-Inject](#T-Inject)'s argument typing, etc.) opens with $\Gamma = \Gamma_1 \otimes \ldots \otimes \Gamma_k$ — a partition of $\Gamma$ into $k$ sub-environments, one per sub-derivation. Each $\Gamma_i$ is then *fully* the responsibility of its sub-derivation: linear bindings in $\Gamma_i$ must be consumed by some leaf inside that sub-derivation, $\omega$ bindings may be referenced any number of times. At an expression *leaf*:

- [T-Var](#T-Var) consumes the binding it references: if $x :^1 S \in \Gamma$, the leaf's $\Gamma$ is exactly the singleton (or the singleton plus $\omega$ entries the unifier may need); the linear $x$ disappears from the rest of the derivation because no other partition received it.
- [T-Const](#T-Const) and other no-variable leaves carry the side condition $\text{pure}(\Gamma)$ — the leaf's local $\Gamma$ may not contain *any* live linear (every linear must have already been routed away by a $\otimes$-split, otherwise the leaf would consume nothing while a linear sits unconsumed).

We write

$$\Gamma \setminus\!\!\setminus e \;=\; \lbrace x :^q S \in \Gamma \mid q = \omega \;\vee\; x \notin \text{linConsumed}(e\text{'s derivation}) \rbrace$$

for the **residual** of $\Gamma$ after typing $e$, where $\text{linConsumed}(e\text{'s derivation})$ is the union of linear bindings drawn into [T-Var](#T-Var) leaves anywhere in the derivation tree of $e$. Equivalently: $\text{linConsumed}$ is the set of linear $x \in \text{dom}(\Gamma)$ that the $\otimes$-splits of $e$'s derivation routed into a consuming leaf rather than the residual partition. The residual is well-defined *per derivation* (different $\otimes$-split choices yield different residuals; soundness holds for every choice that lets the derivation type-check).

**Syntactic computation of $\text{linConsumed}$.** Given $\Gamma$, we can also compute $\text{linConsumed}(e, \Gamma)$ structurally on the syntax of $e$ — this is the algorithm the implementation runs and is equivalent to the metatheoretic "T-Var leaves of the derivation" reading whenever a derivation exists. Sub-expression results combine by **disjoint union** $\uplus$, which is undefined when two sub-expressions consume the same linear binding (matching the $\otimes$-split's "$1 + 1 = -$" forbid clause):

$$\begin{array}{rcl}
\text{linConsumed}(\mu\,x, \Gamma) & = & \begin{cases} \lbrace x \rbrace & \text{if}~\Gamma(x) = (1, S)~\text{and}~\mu \in \lbrace \varepsilon, \%, \mathord{\sim} \rbrace \\ \emptyset & \text{otherwise} \end{cases} \\[8pt]
\text{linConsumed}(\&x, \Gamma) & = & \emptyset \quad\text{(borrow does not consume)} \\[2pt]
\text{linConsumed}(c, \Gamma) = \text{linConsumed}(n, \Gamma) = \text{linConsumed}((), \Gamma) & = & \emptyset \\[2pt]
\text{linConsumed}(@e, \Gamma) = \text{linConsumed}(e.\ell, \Gamma) & = & \text{linConsumed}(e, \Gamma) \\[2pt]
\text{linConsumed}(e_1 \oplus e_2, \Gamma) & = & \text{linConsumed}(e_1, \Gamma) \uplus \text{linConsumed}(e_2, \Gamma) \\[2pt]
\text{linConsumed}(f(\overline{\ell : e}), \Gamma) & = & \text{linConsumed}(f, \Gamma) \;\uplus\; \biguplus_i \text{linConsumed}(e_i, \Gamma) \\[2pt]
\text{linConsumed}(\lbrace \overline{\ell : e} \rbrace, \Gamma) & = & \biguplus_i \text{linConsumed}(e_i, \Gamma) \\[2pt]
\text{linConsumed}(\textbf{raise}~e, \Gamma) & = & \text{linConsumed}(e, \Gamma) \\[6pt]
\text{linConsumed}(\textbf{fn}~(\ldots)~\textbf{do}~\overline{s}~\textbf{end}, \Gamma) & = & \lbrace x \in \text{fv}(\overline{s}) \cap \text{dom}(\Gamma) \mid \Gamma(x) = (1, S) \rbrace \\
& & \text{(captured linears are consumed by the closure)} \\[2pt]
\text{linConsumed}(\textbf{handler}~x~[\textbf{require}~\rho]~\textbf{do}~\overline{\ell_j = e_j}~\textbf{end}, \Gamma) & = & \lbrace y \in \textstyle\bigcup_j \text{fv}(e_j) \cap \text{dom}(\Gamma) \mid \Gamma(y) = (1, S) \rbrace \\
& & \text{(captured linears across all arms are consumed by the handler value)} \\[6pt]
\text{linConsumed}(\textbf{if}~e_c~\textbf{then}~\overline{s_1}~\textbf{else}~\overline{s_2}, \Gamma) & = & \text{linConsumed}(e_c, \Gamma) \;\uplus\; \text{linConsumed}(\overline{s_1}, \Gamma') \\
& & \text{requires}~\text{linConsumed}(\overline{s_1}, \Gamma') = \text{linConsumed}(\overline{s_2}, \Gamma') \\
& & \text{where}~\Gamma' = \Gamma \setminus\!\!\setminus e_c \\
\text{linConsumed}(\textbf{match}~e~\lbrace \overline{p_i \to s_i} \rbrace, \Gamma) & = & \text{linConsumed}(e, \Gamma) \;\uplus\; (\text{linConsumed}(\overline{s_1}, \Gamma_1) \setminus \text{bv}(p_1)) \\
& & \text{requires}~\forall i, j.\;(\text{linConsumed}(\overline{s_i}, \Gamma_i) \setminus \text{bv}(p_i)) = (\text{linConsumed}(\overline{s_j}, \Gamma_j) \setminus \text{bv}(p_j)) \\
& & \text{requires}~\forall i.\;\forall y :^1 S \in \Gamma_i \setminus \Gamma.\;y \in \text{linConsumed}(\overline{s_i}, \Gamma_i) \\
& & \text{(pattern-introduced linear binders consumed within their arm)}
\end{array}$$

Branch constructs require **arm equality** of the linear-consumption sets, **projected onto the outer environment**: every branch must consume the same subset of input linears, ignoring the binders the pattern itself introduced (which are arm-local). The intersection formulation $\cap$ would have admitted a program where one arm consumes $\lbrace a, b \rbrace$ and the other consumes $\lbrace a \rbrace$, leaving $b$ in the residual — but iteration through the first arm would have already consumed $b$, breaking the use-after-consume invariant on whichever arm runs at runtime. Arm equality is the only choice that keeps the residual sound across both control-flow paths, and it matches the impl's `vars_equal` check in `src/typecheck/linearity.nx`'s if/match handling.

For $\textbf{match}$, the projection step is explicit: each arm's $\Gamma_i$ extends $\Gamma$ with pattern binders (e.g.\ the $x$ in `Some(%x) ->`), and a linear pattern binder is required to be consumed *within its arm* rather than crossing into the outer-Γ equality check. Equivalently, $\text{linConsumed}(\overline{s_i}, \Gamma_i) \setminus \text{bv}(p_i)$ is the arm's consumption restricted to outer-Γ linears, and the second `requires` clause discharges the per-arm obligation on $\Gamma_i \setminus \Gamma$ (the new bindings introduced by $p_i$). $\textbf{if}$ has no pattern binders, so the projection collapses to the plain set equality already shown above.

For statement sequences, $\text{linConsumed}(\overline{s}, \Gamma)$ folds left-to-right, threading $\Gamma$ through each statement's residual:

$$\text{linConsumed}(\cdot, \Gamma) = \emptyset \qquad \text{linConsumed}(s; \overline{s'}, \Gamma) = \text{linConsumed}(s, \Gamma) \cup \text{linConsumed}(\overline{s'}, \Gamma \setminus\!\!\setminus s)$$

where $\Gamma \setminus\!\!\setminus s$ removes the linears consumed by $s$ before typing the tail. The base cases for individual statements ($\textbf{let}$, $\textbf{return}$, $\mathord{\sim}x \leftarrow e$, etc.) reduce to $\text{linConsumed}$ of their sub-expressions plus any new linear bindings introduced (e.g. $\textbf{let}~\%y = e$ adds $y$ to the env for the tail, but does not itself consume anything from the input $\Gamma$ beyond what $e$ consumed).

The two readings — "T-Var leaves of any derivation" and the syntactic recursion above — coincide on every well-typed program: the recursion eagerly commits to the unique consumption set the $\otimes$-splits would have produced, and undefined-$\uplus$ at any node signals exactly the "$1 + 1 = -$" reject case.

**Statement-judgment outputs read modulo the residual.** Where a rule's conclusion writes $\Gamma' = \Gamma,\, x :^q S$ for a fresh binder $x$, the operational reading is

$$\Gamma' \;=\; (\Gamma \setminus\!\!\setminus e),\, x :^q S$$

with the residual computed against the rule's expression premise(s). Every statement-level conclusion in §2 should be read this way; T-Let and T-LetPat write the residual explicitly as the anchoring examples, and T-Seq-Cons threads it transitively through `Γ_1` from the head into the tail. The closeBlock narrative's claim — *"a linear outer binding consumed inside the block is removed from $\Gamma_\text{inner}$"* — discharges by induction over the body's statements: each statement's output is its input minus what its expressions consumed, so $\Gamma_\text{inner}$ at the body's end equals $\Gamma_\text{body} \setminus\!\!\setminus \overline{s}$ (treating $\setminus\!\!\setminus$ as iterated over the sequence).

**P-Block soundness.** With the residual reading, P-Block's $\forall x :^1 S \in \Gamma_\text{inner}.\;x \in \text{dom}(\Gamma_\text{outer}) \wedge x :^1 S \in \Gamma_\text{outer}$ scans only the linears that *survived* every consumption inside the block. A correctly-consumed inner $\%h$ is absent from $\Gamma_\text{inner}$ and therefore vacuously satisfies the premise; only genuinely-leaked or shadowed-divergent linears trigger the rejection. The same reading rescues P-FnEnd and P-Loop from the same false-positive trap.

**Implementation correspondence.** `src/typecheck/linearity.nx` carries a *live-linear set* (`LinState(vars, frame_stack)`) separate from the $\Gamma$ map: the set shrinks on every linear use and grows on every linear-introducing $\textbf{let}$. The spec's $\Gamma \setminus\!\!\setminus e$ is the metatheoretic projection of that live-set onto $\Gamma$'s linear restriction; the impl's bookkeeping is the operational embodiment of the $\otimes$-split's residual.

### Auxiliary Functions

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

$\text{typedef}(x)$ denotes the definition of named type $x$ in the global type-definition environment.

Other functions are introduced where first used: $\text{linear}$, $\text{autoDrop}$ (Linearity), $\text{strip}$ (Pattern Matching), $\text{open}$ and $\text{selectInt}$/$\text{selectFloat}$ and $\text{comparable}$ (Expressions), $\text{default}$, $\text{wrapSigil}$ (Statements), $\text{merge}$ (Statements), $\text{tail}$, $\text{branchType}$ (Expressions), $\text{methods}$ (Expressions), $\text{caughtVariants}$, $\text{hasCatchAll}$, $\text{members}$, $\text{diverges}$ (Statements), $\text{closeBlock}$ (Statements).

### Free Variables

$\text{fv}$ is overloaded — on a *type*, it returns the free unification variables (used by $\text{occurs}$ in the unification rules); on a *term*, it returns the free term variables (used by [T-Lambda](#T-Lambda) and [T-Handler](#T-Handler) to compute the captured-binding partition $\Gamma_\text{cap}$). Disambiguation is by the argument's syntactic category.

The companion $\text{bv}(p)$ returns the binder names introduced by a pattern; it cooperates with $\text{fv}$ when stripping shadowed names from a statement-sequence's free set.

Free variables of expressions (selected cases — clauses for forms with no binders trivially recurse into subterms):

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
\text{fv}(\textbf{raise}~e) & = & \text{fv}(e) \\
\text{fv}(\textbf{handler}~x~[\textbf{require}~\rho]~\textbf{do}~\overline{\ell = e}~\textbf{end}) & = & \textstyle\bigcup_j \text{fv}(e_j)
\end{array}$$

Free variables of statement sequences are defined cumulatively from the right, with $\text{bv}(p)$ stripping shadowed names introduced earlier in the sequence:

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

Bound variables of patterns:

$$\begin{array}{rcl}
\text{bv}(x) & = & \lbrace x \rbrace \\
\text{bv}(\_) = \text{bv}(n) & = & \emptyset \\
\text{bv}(c(\overline{\ell : p})) & = & \textstyle\bigcup_i \text{bv}(p_i) \\
\text{bv}(\lbrace \overline{\ell : p} \rbrace) & = & \textstyle\bigcup_i \text{bv}(p_i) \\
\text{bv}(p_1 \mathbin{\vert} p_2) & = & \text{bv}(p_1) = \text{bv}(p_2)~\text{(both alternatives must bind the same set; see [P-Or](#pattern-matching))}
\end{array}$$

The sequence-level $\text{fv}$ accounts for shadowing: a $\textbf{let}~x = \ldots$ removes $x$ from the tail's free set, so a later capture site sees through the binding to whatever $x$ refers to in *its* enclosing scope. Without the subtraction, $\textbf{fn}\;()~\textbf{do}\;\textbf{let}~x = 1;\;\textbf{return}~x~\textbf{end}$ would compute $\text{fv} = \lbrace x \rbrace$ and try to capture an outer $x$ that does not exist.

Free unification variables of a *type* (used by $\text{occurs}$ in unification) include both type-kinded `${?}\alpha$` and row-kinded `${?}r$`. Rigid quantifiers ($\alpha$, $r$) are not free unification variables — they're parameters of the surrounding scheme, not refinement targets:

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

The last clause is load-bearing for unification termination: when [U-Var](#U-Var) attempts $\text{unify}({?}\alpha, \tau)$ with $\tau$ containing an open row $\lbrace \overline{\tau} \mid {?}\alpha \rbrace$, the $\text{occurs}({?}\alpha, \tau)$ check inspects $\text{fv}(\tau) \ni {?}\alpha$ and rejects, preventing the cycle $({?}\alpha \mathrel{:=} \lbrace \overline{\tau} \mid {?}\alpha \rbrace)$ that would diverge under substitution. Symmetrically for ${?}r$: a row unification variable participates in $\text{occurs}$ exactly when its enclosing type's $\text{fv}$ includes it.

### Linearity

$\text{linear}(\tau)$ is a structural (recursive) predicate: holds if $\tau$ is $\%\sigma$, $@\sigma$, or $[\lvert\,\sigma\,\rvert]$ at the outermost level, or if any transitive component of $\tau$ is linear. Components inspected by the recursion: fields of records, type arguments of named types, element types of lists, elements of rows, and **the payload of $\mathord{\sim}\sigma$** ($\text{linear}(\mathord{\sim}\sigma) \Longleftrightarrow \text{linear}(\sigma)$). Borrows $\&\sigma$ are *not* recursed into: a borrow is always reusable ($q = \omega$), so the borrow itself is non-linear regardless of $\sigma$; the underlying owner's linearity is tracked at the owner's binding, not at the borrow. Function arrows $(\overline{\ell:\tau}) \to \tau_r$ and handlers $\textbf{handler}\;x\;\rho$ are values whose own linearity is governed by capture-linearisation in [T-Lambda](#T-Lambda) / [T-Handler](#T-Handler) rather than by transitive recursion; $\text{linear}$ does not look inside them. Example: $\text{linear}(\text{Pair}\langle\%\texttt{i64}, \texttt{i64}\rangle)$ holds; $\text{linear}(\mathord{\sim}\%\texttt{i64})$ holds (caught by the new $\mathord{\sim}$-recursion clause — but see [§Mutable Reference Well-Formedness](#mutable-reference-well-formedness) below, which makes the type itself unrepresentable).

$\text{autoDrop}(\tau)$ holds if the innermost non-modality type of $\tau$ (recursively stripping $\%$, $\&$, $\mathord{\sim}$ — but **not** $@$) is in $\lbrace b, \texttt{intlit}, \texttt{floatlit} \rbrace$. Types whose linear wrapper can be silently discarded. Thunks $@\sigma$ are explicitly **not** auto-droppable: an unforced thunk holds a suspended computation (with potentially-captured linear state, ports, or other resources) that the runtime never runs if the binding is silently dropped — exactly the *one-shot lazy continuation* hazard called out in [drop.md](../drop). Likewise arrays $[\lvert\,\sigma\,\rvert]$ are not auto-droppable: their linear contents (allocated cells, captured handles) must be released explicitly. The narrow auto-drop set is intentional — only structurally trivial values (scalars, intlit/floatlit, base types) qualify; anything else must reach an explicit consumption channel.

**Variable cases.** Both predicates take the *conservative* answer on unresolved unification variables and on rigid type/row quantifiers:

$$\text{linear}({?}\alpha) = \text{linear}(\alpha) = \text{false}\qquad \text{autoDrop}({?}\alpha) = \text{autoDrop}(\alpha) = \text{false}$$

A $\%$- or $@$-wrapper around a variable, e.g.\ $\%{?}\alpha$ or $\%\alpha$, is still linear by the outermost-wrapper clause — only a bare variable defaults to non-linear. The convention is conservative in two opposite ways:

- $\text{linear} = \text{false}$ on a bare variable means [P-Var](#P-Var) assigns $q = \omega$ to a pattern bound at type $?\alpha$ (e.g.\ the divergent-RHS case where $\textbf{raise}~e$ returns $?\alpha$). The binding never carries a linear obligation; the unifier may later refine $?\alpha$ to a non-linear concrete type without re-evaluation. If a later occurrence demands linear ($\%\sigma$), unification refines $?\alpha$ at the wrapped position and the $\%$-clause makes linearity locally visible.
- $\text{autoDrop} = \text{false}$ on a bare variable means [P-Wild](#P-Wild) rejects discarding any binding whose type is still $?\alpha$ until it's resolved — the lambda body's $\textbf{let}~\_ = e$ for $e : ?\alpha$ is statically rejected as a possible silent leak. This is conservative *the other direction*: we prefer false-positive errors over silent linear discard.

The two conventions together preserve soundness: any program that type-checks under the variable cases also type-checks at every later refinement of those variables (provided the refinement is consistent with the rest of the derivation). Mechanically, `src/typecheck/linearity.nx`'s `is_linear_binding_type` and `is_auto_droppable` implement these defaults — both fall through to $\text{false}$ on $\texttt{TyVar}$.

**Recursive named types: cycle-guarded fixpoint.** When $\text{linear}(\tau)$ recurses into a named type $x\langle \overline{\tau} \rangle$, it must unfold $x$'s declaration to inspect field/variant types — but a self-referential or mutually-recursive declaration (e.g.\ $\textbf{type}~\texttt{Tree}\langle T \rangle = \texttt{Leaf} \mathbin{\vert} \texttt{Node}(\textit{left}: \texttt{Tree}\langle T \rangle, \ldots)$) makes naive structural recursion non-terminating. The evaluation is therefore parameterised by a **visited set** $V$ and computed as a least fixpoint:

$$\text{linear}(\tau) \;=\; \text{linear}'(\tau, \emptyset) \qquad \text{autoDrop}(\tau) \;=\; \text{autoDrop}'(\tau, \emptyset)$$

with the cycle guard

$$\text{linear}'(x\langle \overline{\tau} \rangle, V) = \begin{cases}
\text{false} & \text{if}~x \in V \quad (\text{cycle: minimum fixpoint}) \\
\bigvee_{F~\text{a field-or-variant-arg type of}~\text{unfold}(x\langle \overline{\tau} \rangle)} \text{linear}'(F, V \cup \lbrace x \rbrace) & \text{otherwise}
\end{cases}$$

and analogously for $\text{autoDrop}'$. All other clauses (the $\%\sigma$, $@\sigma$, $[\lvert\sigma\rvert]$ outermost wrappers, base types, records, lists, type-arg recursion) thread $V$ unchanged. The cycle case returns *false* — the conservative answer that makes the predicate the minimum fixpoint and keeps a recursive type non-linear unless one of its non-recursive components forces linearity. Concretely:

- $\text{linear}(\texttt{Tree}\langle T \rangle)$ where $\texttt{Tree}\langle T \rangle = \texttt{Leaf} \mathbin{\vert} \texttt{Node}(\textit{left}: \texttt{Tree}\langle T \rangle, \textit{val}: T, \textit{right}: \texttt{Tree}\langle T \rangle)$ unfolds to fields $\lbrace \texttt{Tree}\langle T \rangle, T, \texttt{Tree}\langle T \rangle \rbrace$. The two recursive references hit the cycle guard and return $\text{false}$; $T$ is a rigid quantifier (also $\text{false}$). Result: $\text{false}$ — Tree is non-linear unless $T$ is later instantiated to a linear type.
- $\text{linear}(\texttt{LList}\langle T \rangle)$ where $\texttt{LList}\langle T \rangle = \texttt{Empty} \mathbin{\vert} \texttt{Cons}(\textit{head}: T, \textit{tail}: \%\texttt{LList}\langle T \rangle)$ unfolds to fields $\lbrace T, \%\texttt{LList}\langle T \rangle \rbrace$. The second field's outermost $\%$ wrapper trips the linear clause *before* the cycle guard fires, returning $\text{true}$. Result: $\text{true}$ — the explicit $\%$ on the recursive tail makes the list itself linear.

The implementation memoises by $x \mapsto (\text{linear}, \text{autoDrop})$ to avoid re-walking the body; the spec's $V$ parameter is the metatheoretic counterpart of that memo table.

Linearity is entirely structural: the split $\otimes$ ensures each linear binding ($q = 1$) goes to exactly one sub-derivation, and branching constructs give both arms the same portion of $\Gamma$.

<a id="mutable-reference-well-formedness"></a>

**Mutable-reference well-formedness ($\text{wfRef}$).** A mutable reference cell $\mathord{\sim}\sigma$ permits unrestricted reads (each $\mathord{\sim}x$ via [T-Deref](#T-Deref) yields a fresh $\sigma$) and assignments (via [T-Assign](#T-Assign)). If $\sigma$ were linear, each read would produce a fresh copy of the linear payload, duplicating the resource — incompatible with linearity's single-use discipline. The type system therefore rejects $\mathord{\sim}\sigma$ as malformed when $\sigma$ is linear:

$$\text{wfRef}(\mathord{\sim}\sigma) \;\Longleftrightarrow\; \neg\text{linear}(\sigma)$$

$\text{wfRef}$ is checked at every **type-formation site** that can introduce a $\mathord{\sim}\sigma$: parameter and return slots of $\textbf{fn}$ literals ([T-Lambda](#T-Lambda) / [T-Let-PolyFn](#T-Let-PolyFn)), the signature of a method declared by [D-Port](#D-Port), the type annotation of [D-External](#D-External), the field types of [D-Type-Record](#D-Type-Record) / [D-Type-Sum](#D-Type-Sum), and any explicit type annotation on [T-Let](#T-Let). The check fails fast at declaration time rather than letting a $\mathord{\sim}\%T$-shaped value smuggle in through e.g.\ an externally-declared signature, then duplicate the inner linear via successive $\mathord{\sim}x$ reads. T-Let itself also carries the rule-local guard $\mu = \mathord{\sim} \implies \neg\text{linear}(\tau')$ (see [T-Let](#T-Let)); $\text{wfRef}$ is the global counterpart that catches the same hazard when the type sneaks in through a non-sigil channel.

Two additional behaviors are embedded in specific rules rather than stated as standalone inference rules:

- **Weakening** (in [T-App](#T-App)): when a parameter has type $\%\tau$ and the argument has type $\sigma$ with $\neg\text{linear}(\sigma)$, $\text{unify}(\sigma, \tau)$ is used instead of $\text{unify}(\sigma, \%\tau)$. This applies only to the linear modality $\%$, not to $@$ or other linear-producing forms.
- **Closure linearization** (in [T-Lambda](#T-Lambda)): when a lambda captures any linear binding from $\Gamma$, its closure type is wrapped with $\%$ (making the closure itself linear).

### Unification

Unification is symmetric: $\text{unify}(\tau_1, \tau_2) = \text{unify}(\tau_2, \tau_1)$ unless otherwise noted. The rules below are written with the "interesting" argument on the left; the symmetric case is implied. U-Borrow is intentionally asymmetric (no symmetric counterpart); U-Expand is asymmetric in form but applies in both argument orders by the symmetry convention.

**Argument-order convention.** Where the rules below are asymmetric, the **left** argument is the *actual* (the type produced by an expression or read out of a binding) and the **right** argument is the *expected* (the type a context demands — a parameter slot, an annotation, a return type). All call sites in the typing rules follow this convention:

- [T-App](#T-App): $\text{unify}(\tau_i, P_i)$ with the argument's actual type on the left
- [T-Let](#T-Let): $\text{unify}(\tau', \sigma)$ with the inferred type on the left and the annotation on the right
- [T-Return](#T-Return): $\text{unify}(\tau, \tau_r)$ with the expression's type on the left
- [T-Assign](#T-Assign): $\text{unify}(\sigma, \tau)$ with the assigned expression on the left

This convention is what makes U-Borrow's asymmetry well-defined: $\&\sigma$ on the left (an actual borrow value being supplied) auto-derefs to $\sigma$; $\&\sigma$ on the right (a context demanding a borrow) does not. That choice means borrows can be passed where the underlying type is expected, but plain values are never auto-borrowed — call sites must use $\&x$ explicitly.

<a id="U-Refl"></a>

$$\dfrac{}{\text{unify}(\tau, \tau) = \emptyset} \;\textsc{U-Refl}$$

$$\dfrac{\neg\text{occurs}(\alpha, \tau)}{\text{unify}({?}\alpha, \tau) = \lbrace {?}\alpha := \tau \rbrace} \;\textsc{U-Var}
\qquad
\dfrac{\text{occurs}(\alpha, \tau)}{\text{unify}({?}\alpha, \tau) = \text{error}} \;\textsc{U-Occurs}$$

$$\dfrac{}{\text{unify}(\texttt{intlit}, \texttt{i32}) = \lbrace \texttt{intlit} := \texttt{i32} \rbrace} \quad
\dfrac{}{\text{unify}(\texttt{intlit}, \texttt{i64}) = \lbrace \texttt{intlit} := \texttt{i64} \rbrace} \;\textsc{U-IntLit}$$

$$\dfrac{}{\text{unify}(\texttt{floatlit}, \texttt{f32}) = \lbrace \texttt{floatlit} := \texttt{f32} \rbrace} \quad
\dfrac{}{\text{unify}(\texttt{floatlit}, \texttt{f64}) = \lbrace \texttt{floatlit} := \texttt{f64} \rbrace} \;\textsc{U-FloatLit}$$

Two $\texttt{intlit}$ (or two $\texttt{floatlit}$) occurrences unify by [U-Refl](#U-Refl) — both sides are the same singleton symbol, so syntactic identity holds trivially and the empty substitution suffices. Once *either* side later meets a concrete type via [U-IntLit](#U-IntLit) / [U-FloatLit](#U-FloatLit), the resulting substitution propagates to every $\texttt{intlit}$ / $\texttt{floatlit}$ in the term (because they all share the singleton symbol), pinning the whole chain in one step.

U-IntLit and U-FloatLit *do* rewrite — they substitute the literal's inference-internal type to the matched concrete type, propagating the resolution to all occurrences linked by previous unifications. U-Var, U-IntLit, and U-FloatLit apply in both argument orders via the symmetry convention above.

$$\dfrac{
  \begin{array}{l}
  \lvert\overline{p_1}\rvert = \lvert\overline{p_2}\rvert \qquad
  \forall i.\;\ell_i^1 = \ell_{\pi(i)}^2 \qquad
  \text{unify}(\tau_i^1, \tau_{\pi(i)}^2) \\[2pt]
  \text{unify}(\tau_{r1}, \tau_{r2}) \qquad
  \text{unify}(\rho_{q1}, \rho_{q2}) \qquad
  \text{unify}(\rho_{e1}, \rho_{e2})
  \end{array}
}{
  \text{unify}((\overline{p_1}) \to \tau_{r1};\, \rho_{q1};\, \rho_{e1},\;
  (\overline{p_2}) \to \tau_{r2};\, \rho_{q2};\, \rho_{e2})
} \;\textsc{U-Arrow}$$

where $\pi$ is the permutation matching labels by name ($\ell_i^1 = \ell_{\pi(i)}^2$). Parameters are matched by label, not position.

$$\dfrac{
  \lvert\overline{f_1}\rvert = \lvert\overline{f_2}\rvert \qquad
  \text{sorted by label} \qquad
  \forall i.\;\ell_i^1 = \ell_i^2 \qquad
  \forall i.\;\text{unify}(\tau_i^1, \tau_i^2)
}{
  \text{unify}(\lbrace \overline{f_1} \rbrace, \lbrace \overline{f_2} \rbrace)
} \;\textsc{U-Record}$$

$$\dfrac{
  \forall i.\;\text{unify}(\tau_i, \sigma_i)
}{
  \text{unify}(x\langle\overline{\tau}\rangle, x\langle\overline{\sigma}\rangle)
} \;\textsc{U-Named}$$

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

$$\dfrac{
  \overline{\tau_1} = \overline{\tau_2}~\text{as multisets (order-irrelevant)}
}{
  \text{unify}(\lbrace \overline{\tau_1} \rbrace, \lbrace \overline{\tau_2} \rbrace)
} \;\textsc{U-Row-Closed-Closed}$$

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

The three U-Row rules cover every combination of closed/open arguments. Closed-closed succeeds only when the multisets are equal — neither side has a tail to absorb the difference. Closed-open is the asymmetric mixed case: the right-hand tail must absorb whatever the left has beyond the common prefix, but the left being closed means the right cannot have entries the left lacks ($\overline{r_2} = \emptyset$). The open-closed case follows by the symmetry convention stated at the start of §Unification.

<a id="U-Row-Exn"></a>

$$\dfrac{
  \begin{array}{l}
  \texttt{Exn} \in \overline{\tau_2} \qquad
  \overline{c} = \overline{\tau_2} \setminus \lbrace \texttt{Exn} \rbrace \\[2pt]
  \forall C \in \overline{\tau_1}.\;\;C = \texttt{Exn} \;\vee\; C \in \overline{c} \;\vee\; C \in \text{variants}(\texttt{Exn})
  \end{array}
}{
  \text{unify}(\lbrace \overline{\tau_1} \rbrace,\; \lbrace \overline{\tau_2} \rbrace)
} \;\textsc{U-Row-Exn}$$

U-Row-Exn handles the variant-lattice subsumption of $\texttt{Exn}$ described in §1.3: when one side carries the catch-all sentinel $\texttt{Exn}$, any constructors of $\texttt{Exn}$ on the other side are absorbed by it. This is the *only* place the type system admits a row-inclusion relationship — every other row rule requires entry-by-entry equality. U-Row-Exn applies in both argument orders by the symmetry convention. It is intentionally restricted to closed-closed shapes; mixing $\texttt{Exn}$ with an open-row tail $\lbrace \overline{\tau} \mid {?}r \rbrace$ is handled by first instantiating $?r$ via U-Row-Closed-Open, then re-applying U-Row-Exn.

$$\dfrac{
  \neg\text{linear}(\tau_2) \qquad
  \text{unify}(\tau_1, \tau_2)
}{
  \text{unify}(\&\tau_1, \tau_2)
} \;\textsc{U-Borrow}$$

The $\neg\text{linear}(\tau_2)$ premise blocks borrow-to-ownership smuggling: a value of type $\&\sigma$ supplied where the context demands a linear $\tau_2$ would let the callee consume the underlying resource while the caller (still holding the borrow's source) believes the resource is alive. With the premise, $\textit{consume}(\&\%r)$ is rejected at unification — the borrow must be explicitly cloned or the caller must move ownership.

$$\dfrac{
  \text{fields}(x\langle\overline{\tau}\rangle) = \lbrace \overline{\ell : \sigma} \rbrace \qquad
  \text{unify}(\lbrace \overline{\ell : \sigma} \rbrace, R)
}{
  \text{unify}(x\langle\overline{\tau}\rangle, R)
} \;\textsc{U-Expand}$$

$$\dfrac{
  \text{unify}(\tau_1, \tau_2)
}{
  \text{unify}([\tau_1],\, \texttt{List}\langle\tau_2\rangle)
} \;\textsc{U-ListSugar}$$

U-ListSugar bridges the type-level alias: $[\tau]$ in source is identical to the prelude $\texttt{List}\langle\tau\rangle$ enum (see §1, "List literals and the :: cons operator"). Both directions are reachable by the symmetry convention.

U-Borrow auto-derefs $\&\sigma$ only when it appears on the left (the *actual* position — see the argument-order convention at the start of this section). U-Expand applies in both argument orders via the symmetry convention — the implementation handles both $\text{unify}(x\langle\overline{\tau}\rangle, R)$ and $\text{unify}(R, x\langle\overline{\tau}\rangle)$.

$$\textbf{P7}~\text{(Unification).}\quad \text{unify}(\tau_1, \tau_2)~\text{terminates and returns a most general unifier or fails}$$

### Polymorphism Introduction

Polymorphic schemes are introduced **only** by explicit type-parameter lists on top-level function declarations. The quantifier list is **kind-aware** — each user-named quantifier $X$ ranges over either type variables ($\kappa = \texttt{Type}$) or row variables ($\kappa = \texttt{Row}$):

$$\kappa ::= \texttt{Type} \mid \texttt{Row}$$

$$\textbf{fn}~\textit{foo}\langle X_1, \ldots, X_n\rangle(\overline{\ell:\tau}) \to \tau_r;\,\rho_q;\,\rho_e \quad\rightsquigarrow\quad \forall X_1{:}\kappa_1 \ldots X_n{:}\kappa_n.\,(\overline{\ell:\tau}) \to \tau_r;\,\rho_q;\,\rho_e$$

The kind $\kappa_i$ of each $X_i$ is **inferred from $X_i$'s occurrence position** in the function signature. We formalise the inference as the auxiliary $\text{kindOf}(X, \sigma)$, a partial function from a quantifier name and a signature to $\lbrace \texttt{Type}, \texttt{Row} \rbrace$:

$$\text{kindOf}(X, \sigma) = \begin{cases}
\texttt{Type} & \text{if}~\text{occurs}_\tau(X, \sigma)~\text{and not}~\text{occurs}_\rho(X, \sigma) \\
\texttt{Row} & \text{if}~\text{occurs}_\rho(X, \sigma)~\text{and not}~\text{occurs}_\tau(X, \sigma) \\
\text{undefined} & \text{otherwise (unused or kind clash)}
\end{cases}$$

with the position predicates defined recursively over the signature's structure:

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

In words: $\text{occurs}_\tau$ asks "does $X$ appear at any *type* position (anywhere a $\tau$ is expected, including row entries)?" and $\text{occurs}_\rho$ asks "does $X$ appear specifically as a *row tail*?". Their disjoint truth values pin $\kappa$. The clash case (both true) and the unused case (both false) are static errors at [T-Let-PolyFn](#T-Let-PolyFn) — both surface as a malformed quantifier list at the binding site, not at a use site.

The surface syntax `fn <R>(...)` carries no kind annotation; kind inference recovers $\kappa_i$ from the body. This is faithful to the implementation (`convert_ud_to_var` in `src/typecheck/check.nx`), which represents both kinds with the same $\texttt{TyVar}(n)$ constructor; the unifier then learns the kind from the first row/non-row context the variable meets, achieving the same fixpoint as the metatheoretic $\text{kindOf}$ above.

The $X_i$ are user-named quantifiers (predicative System-F extended with row kind). There is **no implicit generalization**: every let-binding produces a monomorphic scheme via $\text{mono}$. The two carve-outs are [T-Let-PolyFn](#T-Let-PolyFn) (the introduction site — fires when the RHS is a $\textbf{fn}$ literal with an explicit type-parameter list, generalizing the inferred arrow over $\overline{X_i}$) and [T-Let-Alias](#T-Let-Alias) (the forwarding site — copies an existing polymorphic scheme verbatim when the RHS is a bare polymorphic variable).

$$\text{mono}(\tau) = \forall\emptyset.\,\tau \qquad\text{(monomorphic scheme; empty quantifier list)}$$

The pattern rules ([P-Var](#P-Var)) and assignment rule ([T-Assign](#T-Assign)) write the equivalent 2-tuple form $(\emptyset,\,\tau)$ for the same monomorphic scheme — both denote $\forall\emptyset.\,\tau$.

$\text{inst}$ produces a fresh unification variable of the appropriate kind for each quantifier:

$$\text{inst}(\forall X_1{:}\kappa_1 \ldots X_n{:}\kappa_n.\, \tau) = \tau[X_1 := \nu_1, \ldots, X_n := \nu_n]$$

$$\nu_i = \begin{cases} {?}\beta_i & \text{if}~\kappa_i = \texttt{Type},~{?}\beta_i~\text{fresh type unification variable} \\ {?}r_i & \text{if}~\kappa_i = \texttt{Row},~{?}r_i~\text{fresh row tail variable} \end{cases}$$

$\text{inst}$ is used at every variable use site ([T-Var](#T-Var)). When the scheme is monomorphic ($n = 0$), $\text{inst}$ is the identity and $\tau' = \tau$.

$$\textbf{P8}~\text{(No implicit generalization).}\quad\text{For any binding}~x :^{q} S~\text{introduced by [T-Let](#T-Let) or [T-LetPat](#T-LetPat)},~S = \text{mono}(\tau)~\text{for some}~\tau.$$

Polymorphic schemes ($\forall\overline{X{:}\kappa}.\,\tau$ with $\overline{X} \neq \emptyset$) enter $\Gamma$ only via [T-Let-PolyFn](#T-Let-PolyFn) (top-level $\textbf{fn}$ declarations) or [T-Let-Alias](#T-Let-Alias) (bare-variable forwarding).

**Worked example (row polymorphism).** The library function

```nexus
fn <R>(f: () -> unit require { Logger | R }) -> unit require { Logger | R } do ...
```

has surface quantifier list $\langle R \rangle$. $R$ appears only in row-tail position ($\lbrace \texttt{Logger} \mid R \rbrace$), so kind inference sets $\kappa_R = \texttt{Row}$, yielding the scheme

$$\forall R{:}\texttt{Row}.\;(f: () \to \texttt{unit};\,\lbrace \texttt{Logger} \mid R \rbrace;\,\lbrace\rbrace) \to \texttt{unit};\,\lbrace \texttt{Logger} \mid R \rbrace;\,\lbrace\rbrace$$

At a call site, $\text{inst}$ replaces $R$ with a fresh row unification variable ${?}r$, which then unifies with the caller's residual capability tail by ordinary row unification.

### Pattern Matching

$$\Gamma \vdash p : \tau \Rightarrow \Gamma'$$

$\text{strip}$ removes the outermost modality before pattern matching. It peels $\%$ (linear) and $\&$ (borrow) only — it deliberately does **not** peel $@$ (thunk) or $\mathord{\sim}$ (mutable ref). Thunks must be forced explicitly via [T-Force](#T-Force) before destructuring; refs cannot be match scrutinees at all.

$$\text{strip}(\tau) = \begin{cases}
\sigma & \text{if } \tau \in \lbrace \%\sigma,\, \&\sigma \rbrace \\
\tau & \text{otherwise}
\end{cases}$$

The match expression ([T-Match](#T-Match)) consumes the linear scrutinee via $\otimes$; the pattern rules operate on the stripped type. A scrutinee of type $@\sigma$ therefore fails to match any structural pattern, surfacing a type error that directs the user to write $\textbf{match}\;@x\;\lbrace\ldots\rbrace$ — making the force explicit and ensuring T-Force's linear-consumption obligation is discharged.

<a id="P-Var"></a>

$$\dfrac{
  q = \begin{cases} 1 & \text{if } \text{linear}(\tau) \\ \omega & \text{otherwise} \end{cases}
}{
  \Gamma \vdash x : \tau \Rightarrow \Gamma,\, x :^{q} (\emptyset, \tau)
} \;\textsc{P-Var}$$

$$\dfrac{
  \text{linear}(\tau) \wedge \neg\text{autoDrop}(\tau) \implies \text{error}
}{
  \Gamma \vdash \_ : \tau \Rightarrow \Gamma
} \;\textsc{P-Wild}$$

$$\dfrac{
  \text{unify}(\tau, \text{typeof}(n))
}{
  \Gamma \vdash n : \tau \Rightarrow \Gamma
} \;\textsc{P-Lit}$$

<a id="P-Ctor"></a>

$$\dfrac{
  \begin{array}{l}
  \Gamma(c) = \forall\overline{\alpha}.\,(\overline{\ell : F}) \to \tau' \\[2pt]
  \text{unify}(\text{strip}(\tau),\, \tau'[\overline{\alpha := {?}\beta}]) \qquad
  \lvert\overline{p}\rvert = \lvert\overline{F}\rvert \\[2pt]
  \forall i.\;\Gamma \vdash p_i : F_i[\overline{\alpha := {?}\beta}] \Rightarrow \Gamma_i \\[2pt]
  \biguplus_i (\Gamma_i \setminus \Gamma)~\text{is defined}
  \end{array}
}{
  \Gamma \vdash c(\overline{\ell : p}) : \tau \Rightarrow \Gamma \uplus \textstyle\biguplus_i (\Gamma_i \setminus \Gamma)
} \;\textsc{P-Ctor}$$

Field patterns bind in parallel: each $p_i$ is checked against the same input $\Gamma$, and the new bindings $\Gamma_i \setminus \Gamma$ are combined by disjoint union $\uplus$. Disjoint union fails if any two field patterns introduce the same variable name (e.g. $c(a: x, b: x)$), so a single use of $x$ across fields is rejected at the rule level instead of silently shadowing.

<a id="P-CtorNullary"></a>

$$\dfrac{
  \Gamma(c) = \forall\overline{\alpha}.\,\tau' \qquad
  \tau'~\text{is not an arrow type} \qquad
  \text{unify}(\text{strip}(\tau),\, \tau'[\overline{\alpha := {?}\beta}])
}{
  \Gamma \vdash c : \tau \Rightarrow \Gamma
} \;\textsc{P-CtorNullary}$$

P-CtorNullary handles the bare-identifier form of a zero-field constructor, e.g.\ catching $\textbf{exception}~\texttt{MissingMain}$ (declared without a parameter list) via $\textbf{catch}~\texttt{MissingMain} \to \ldots$. The premise $\Gamma(c) = \forall\overline{\alpha}.\,\tau'$ with $\tau'$ a value type (not an arrow) distinguishes the nullary case from the variable pattern [P-Var](#P-Var): P-Var fires only when the identifier is *not* a constructor (the grammar's variable-pattern side-condition). For a sum-type variant $\texttt{None}$ with declaration $\textbf{type}~\texttt{Option}\langle T \rangle = \texttt{None} \mathbin{\vert} \texttt{Some}(\textit{val}: T)$, [D-Type-Sum](#D-Type-Sum) installs $\texttt{None} :^{\omega} \forall T.\, \texttt{Option}\langle T \rangle$ in $\Gamma$ (the zero-field constructor has the named type itself as its scheme, not an arrow), so P-CtorNullary applies. The output $\Gamma$ is unchanged — nullary constructors bind no field variables.

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

<a id="P-Or"></a>

$$\dfrac{
  \begin{array}{l}
  \Gamma \vdash p_1 : \tau \Rightarrow \Gamma_1 \qquad
  \Gamma \vdash p_2 : \tau \Rightarrow \Gamma_2 \\[2pt]
  \Gamma_1 \setminus \Gamma = \Gamma_2 \setminus \Gamma \quad\text{(both alternatives bind the same names at the same types and usages)}
  \end{array}
}{
  \Gamma \vdash p_1 \mathbin{\vert} p_2 : \tau \Rightarrow \Gamma_1
} \;\textsc{P-Or}$$

P-Or constrains both alternatives to introduce **identical** binding sets — same names, same types, same usage annotations — so the body that follows the pattern can refer to those bindings unambiguously regardless of which alternative matched. The output environment can be taken from either side ($\Gamma_1$, by convention). For exhaustiveness, an or-pattern $p_1 \mathbin{\vert} p_2$ in matrix row $(p_1 \mathbin{\vert} p_2 :: \overline{r})$ expands to two rows $(p_1 :: \overline{r})$ and $(p_2 :: \overline{r})$ before the standard $\text{spec}$/$D$ algorithm runs.

Exhaustiveness is checked via Maranget's pattern matrix algorithm:

$$\dfrac{M = \emptyset}{\text{check}(M, \overline{\tau}) = \text{error}} \;\textsc{Exh-Empty}
\qquad
\dfrac{M \neq \emptyset \qquad \lvert\overline{\tau}\rvert = 0}{\text{check}(M, \overline{\tau}) = \text{ok}} \;\textsc{Exh-Done}$$

$$\dfrac{
  \text{check}(\text{spec}(M, \texttt{true}), \overline{\tau}') \qquad
  \text{check}(\text{spec}(M, \texttt{false}), \overline{\tau}')
}{
  \text{check}(M, \texttt{bool} :: \overline{\tau}')
} \;\textsc{Exh-Bool}$$

<a id="Exh-Sum"></a>

$$\dfrac{
  \begin{array}{l}
  \text{variants}(\tau_1) = \overline{c_j(\overline{F_j})} \\[2pt]
  \forall j.\;\text{check}(\text{spec}(M, c_j), \overline{F_j} \mathbin{+\!\!+} \overline{\tau}')
  \end{array}
}{
  \text{check}(M, \tau_1 :: \overline{\tau}')
} \;\textsc{Exh-Sum}$$

$$\dfrac{
  \begin{array}{l}
  \text{fields}(\tau_1) = \overline{\ell : \sigma} \\[2pt]
  \text{check}(\text{spec}_R(M, \overline{\ell}), \overline{\sigma} \mathbin{+\!\!+} \overline{\tau}')
  \end{array}
}{
  \text{check}(M, \tau_1 :: \overline{\tau}')
} \;\textsc{Exh-Record}$$

$\text{spec}_R(M, \overline{\ell})$ specializes the matrix for a record scrutinee: rows whose first pattern is $\lbrace \overline{\ell : p} \rbrace$ contribute $\overline{p}$ prepended to the rest; wildcard-like rows (matching $\text{wild}$, defined below) are replicated with $\lvert\overline{\ell}\rvert$ fresh wildcards.

$$\dfrac{
  D = \lbrace\, \overline{r} \mid (p :: \overline{r}) \in M,\; \text{wild}(p) \,\rbrace \qquad
  \text{check}(D, \overline{\tau}')
}{
  \text{check}(M, \tau_1 :: \overline{\tau}')
} \;\textsc{Exh-Default}$$

Exh-Default applies when the first column has no complete constructor coverage — it computes the default matrix $D$ by collecting rows whose first pattern is wildcard-like.

$$\text{wild}(p) = (p = \_) \;\vee\; (p~\text{is a variable pattern}~x)$$

A variable pattern $x$ binds the scrutinee under name $x$; from an exhaustiveness standpoint it succeeds against every value, exactly like $\_$. Treating $x$ as wildcard-like in the matrix algorithm restores Maranget's invariant that $\textbf{match}~e~\lbrace x \to \ldots \rbrace$ is exhaustive — which is also required for [T-LetPat](#T-LetPat) to admit single-variable patterns.

$$\text{spec}(M, c) = \lbrace\, \overline{p'} \mathbin{+\!\!+} \overline{r} \mid (c(\overline{p'}) :: \overline{r}) \in M \,\rbrace \;\cup\; \lbrace\, \underbrace{\_,\ldots,\_}_{a(c)} \mathbin{+\!\!+} \overline{r} \mid (p :: \overline{r}) \in M,\; \text{wild}(p) \,\rbrace$$

where $a(c)$ is the arity of constructor $c$. Rows whose first pattern is $c(\overline{p'})$ contribute $\overline{p'}$ prepended to the rest; wildcard-like rows (including variable patterns) are replicated with $a(c)$ fresh wildcards.

$$\textbf{P6}~\text{(Exhaustiveness).}\quad \text{check}(M, [\tau]) = \text{ok} \implies \forall v : \tau.\;\exists i.\; v \in \text{match}(p_i)$$

### Expressions

$$\Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_e$$

All linear bindings in $\Gamma$ must be consumed by the derivation; $\otimes$ distributes them among sub-expressions. $\rho_e$ ($\mathbin{!}$) is the effect produced. Literal rules carry the side-condition $\text{pure}(\Gamma)$, defined below, to make "no unspent linears at a leaf" a checkable premise rather than a narrative obligation:

$$\text{pure}(\Gamma) = \forall x :^{q} S \in \Gamma.\;q = \omega$$

<a id="T-IntLit"></a>
<a id="T-FloatLit"></a>

$$\dfrac{\text{pure}(\Gamma)}{\Gamma;\, \rho_q \vdash_e n : \texttt{intlit} \mathbin{!} \lbrace\rbrace} \;\textsc{T-IntLit}
\qquad
\dfrac{\text{pure}(\Gamma)}{\Gamma;\, \rho_q \vdash_e f : \texttt{floatlit} \mathbin{!} \lbrace\rbrace} \;\textsc{T-FloatLit}$$

$$\dfrac{\text{pure}(\Gamma)}{\Gamma;\, \rho_q \vdash_e b : \texttt{bool} \mathbin{!} \lbrace\rbrace} \;\textsc{T-Bool}
\qquad
\dfrac{\text{pure}(\Gamma)}{\Gamma;\, \rho_q \vdash_e ch : \texttt{char} \mathbin{!} \lbrace\rbrace} \;\textsc{T-Char}$$

$$\dfrac{\text{pure}(\Gamma)}{\Gamma;\, \rho_q \vdash_e s : \texttt{string} \mathbin{!} \lbrace\rbrace} \;\textsc{T-Str}
\qquad
\dfrac{\text{pure}(\Gamma)}{\Gamma;\, \rho_q \vdash_e () : \texttt{unit} \mathbin{!} \lbrace\rbrace} \;\textsc{T-Unit}$$

<a id="T-Var"></a>

$$\dfrac{
  x :^{q} \forall\overline{\alpha}.\,\tau \in \Gamma \qquad
  \tau' = \text{inst}(\forall\overline{\alpha}.\,\tau) \qquad
  \text{pure}(\Gamma \setminus \lbrace x \rbrace)
}{
  \Gamma;\, \rho_q \vdash_e x : \tau' \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Var}$$

If $q = 1$, the binding $x$ is consumed by this use. T-Var applies to the bare variable form $x$ ($\mu = \varepsilon$). Sigil-prefixed variable forms have dedicated rules: [T-Borrow](#T-Borrow) for $\&x$, [T-Force](#T-Force) for $@x$ (which subsumes $@e$ for any expression), and [T-Deref](#T-Deref) below for $\mathord{\sim}x$.

<a id="T-Deref"></a>

$$\dfrac{
  x :^{\omega} \forall\overline{\alpha}.\,\tau \in \Gamma \qquad
  \tau' = \text{inst}(\forall\overline{\alpha}.\,\tau) \qquad
  \tau' = \mathord{\sim}\sigma \qquad
  \text{pure}(\Gamma \setminus \lbrace x \rbrace)
}{
  \Gamma;\, \rho_q \vdash_e \mathord{\sim}x : \sigma \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Deref}$$

T-Deref reads through a mutable reference cell. The binding is not consumed (refs are $q = \omega$ — matching [T-Assign](#T-Assign)'s precondition $x :^\omega (\emptyset, \mathord{\sim}\tau)$). Mirrors [T-Borrow](#T-Borrow)'s structure: variable-only, no row effect, instantiation against the looked-up scheme.

To allow functions with fewer capabilities/effects to be called in a context with more (row subsumption in [T-App](#T-App)), we introduce $\text{open}$:

$$\text{open}(\rho) = \begin{cases}
\lbrace \overline{\tau} \mid {?}r \rbrace & \text{if } \rho = \lbrace \overline{\tau} \rbrace,\; {?}r~\text{fresh} \\
\rho & \text{if } \rho = \lbrace \overline{\tau} \mid {?}r \rbrace
\end{cases}$$

<a id="T-App"></a>

$$\dfrac{
  \begin{array}{c}
  \Gamma = \Gamma_f \otimes \Gamma_1 \otimes \ldots \otimes \Gamma_k \\[2pt]
  \Gamma_f;\, \rho_q \vdash_e f : (\overline{\ell' : P}) \to \tau_r;\, \rho_q';\, \rho_e' \mathbin{!} \rho_f \\[2pt]
  \lbrace \overline{\ell} \rbrace = \lbrace \overline{\ell'} \rbrace \quad\text{(label sets match; no duplicates; full coverage)} \\[2pt]
  \pi: \lbrace 1,\ldots,k \rbrace \to \lbrace 1,\ldots,k \rbrace,\; \ell_i = \ell'_{\pi(i)} \quad\text{(unique permutation by label name)} \\[2pt]
  \forall i.\;\Gamma_i;\, \rho_q \vdash_e e_i : \tau_i \mathbin{!} \rho_i \\[2pt]
  \forall i.\;\begin{cases} \text{unify}(\tau_i, \text{strip}(P_{\pi(i)})) & \text{if } P_{\pi(i)} = \%\sigma \wedge \neg\text{linear}(\tau_i) \\ \text{unify}(\tau_i, P_{\pi(i)}) & \text{otherwise} \end{cases} \\[2pt]
  \text{unify}(\rho_q, \text{open}(\rho_q'))
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e f(\overline{\ell : e}) : \tau_r \mathbin{!} \rho_e' \cup \rho_f \cup \textstyle\bigcup_i \rho_i
} \;\textsc{T-App}$$

The caller's argument labels $\overline{\ell}$ are matched against the callee's parameter labels $\overline{\ell'}$ **by name**, not by position. The permutation $\pi$ aligns the caller's $i$-th argument to the callee's $\pi(i)$-th parameter so that $\ell_i = \ell'_{\pi(i)}$; both directions of the label-set equality must hold (every callee parameter is supplied, no extra caller labels). The permutation is unique because labels are required to be distinct on each side (the surface parser rejects duplicate-label calls and parameter lists). This formalises the *order-independent labeled arguments* guarantee from [semantics.md](../semantics) §Label Order Independence — `f(b: 2, a: 1)` and `f(a: 1, b: 2)` produce the same derivation up to $\pi$.

The weakening condition is explicit: when $P_{\pi(i)} = \%\sigma$ and $\tau_i$ is not linear, unification targets the inner type $\sigma$ (stripping the $\%$ wrapper). This does not apply to other linear forms like $@\sigma$.

**Capability-row enforcement is deferred** (nexus-mqin.14): the T-App premise $\text{unify}(\rho_q, \text{open}(\rho_q'))$ and the corresponding $\rho_q$ slot on T-Lambda's arrow type are part of the formal rule, but the self-host typechecker constructs lambda arrows with empty $\rho_q'$ and discards the callee's $\rho_q'$ at call sites. Capability admission is currently enforced by a downstream pass on MIR rather than by typecheck. The spec rule remains the reference target; closing the gap is tracked by mqin.14 (impl) — symmetric to how throws-row enforcement was tightened in mqin.1.1.

$\text{selectInt}$ and $\text{selectFloat}$ resolve operand types. Integer and float operators are separate ($+$ vs $+.$); they cannot mix. "$—$" = type error (no implicit coercion).

$$\text{selectInt}: \quad
\begin{array}{c|ccc}
 & \texttt{intlit} & \texttt{i32} & \texttt{i64} \\
\hline
\texttt{intlit} & \texttt{i64} & \texttt{i32} & \texttt{i64} \\
\texttt{i32} & \texttt{i32} & \texttt{i32} & — \\
\texttt{i64} & \texttt{i64} & — & \texttt{i64}
\end{array}
$$

$$\text{selectFloat}: \quad
\begin{array}{c|ccc}
 & \texttt{floatlit} & \texttt{f32} & \texttt{f64} \\
\hline
\texttt{floatlit} & \texttt{f64} & \texttt{f32} & \texttt{f64} \\
\texttt{f32} & \texttt{f32} & \texttt{f32} & — \\
\texttt{f64} & \texttt{f64} & — & \texttt{f64}
\end{array}$$

<a id="T-ArithInt"></a>

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

<a id="T-ArithFloat"></a>

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

Unresolved type variables (${?}\alpha$) are treated as $\texttt{intlit}$ in $\text{selectInt}$ and as $\texttt{floatlit}$ in $\text{selectFloat}$.

The $\oplus$ in [T-ArithInt](#T-ArithInt) ranges over the integer arithmetic, bitwise, and shift operators: $\oplus \in \lbrace +,\, -,\, *,\, /,\, \%,\, \mathbin{\\&},\, \mathbin{\vert},\, \mathbin{\hat{}},\, \ll,\, \gg \rbrace$. Float operators $\oplus_f \in \lbrace +.,\, -.,\, *.,\, /. \rbrace$ use $\text{selectFloat}$ in [T-ArithFloat](#T-ArithFloat). Integer and float operators are syntactically distinct (`+` vs `+.`) and cannot mix.

<a id="T-Cmp"></a>

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

$\odot$ ranges over comparison operators $\lbrace ==,\, !=,\, <,\, \leq,\, >,\, \geq \rbrace$. Both operands must unify (e.g. both numeric, both strings, both chars); the result is always $\texttt{bool}$. Equality on records and ADTs reduces structurally, requiring the operand types to match. The $\text{comparable}$ predicate excludes types whose runtime equality is undefined:

$$\text{comparable}(\tau) = \begin{cases}
\text{true} & \text{if}~\tau \in \lbrace b,\, \texttt{intlit},\, \texttt{floatlit} \rbrace \\
\text{true} & \text{if}~\tau = \lbrace \overline{\ell : \sigma} \rbrace \wedge \forall i.\;\text{comparable}(\sigma_i) \\
\text{true} & \text{if}~\tau = x\langle\overline{\sigma}\rangle \wedge \forall i.\;\text{comparable}(\sigma_i) \\
\text{true} & \text{if}~\tau = [\sigma] \wedge \text{comparable}(\sigma) \\
\text{false} & \text{if}~\tau~\text{is an arrow type, handler value, ref, borrow, thunk, or array}
\end{cases}$$

Functions, handlers, mutable refs ($\mathord{\sim}\sigma$), borrows ($\&\sigma$), thunks ($@\sigma$), and arrays ($[\lvert\,\sigma\,\rvert]$) have no defined value-equality at runtime; comparing them is a type error. (Identity comparison on these would be an explicit operator, not $==$.)

<a id="T-Logic"></a>

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

$\boxdot \in \lbrace \mathbin{\\&\\&},\, \mathbin{\vert\vert} \rbrace$. Note that the right-hand row $\rho_2$ joins unconditionally — this is **not** short-circuit-aware effect tracking; if you need pure short-circuit semantics, write the equivalent $\textbf{if}$.

<a id="T-Concat"></a>

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

To unify the result types of multi-branch expressions ([T-If](#T-If), [T-Match](#T-Match)), we introduce $\text{tail}$, which extracts the type produced by the last statement in a sequence, and $\text{branchType}$, which folds the per-branch tails into the conclusion type $\sigma$.

$$\text{tail}(\overline{s}) = \begin{cases} \bot & \text{if last statement is } \textbf{return},\; \textbf{raise}~e\;(\text{as expression statement}),\; \textbf{let}~\mu\,x = \textbf{raise}~e',\; \text{or}\; \textbf{let}~p = e~\text{with}~\text{diverges}(e) \\ \tau & \text{if last statement is an expression of type } \tau \\ \texttt{unit} & \text{otherwise (} \textbf{let},\; \mathord{\sim}x \leftarrow e,\; \textbf{inject},\; \textbf{try}\text{-}\textbf{catch}) \end{cases}$$

$$\text{branchType}(\overline{s_1}, \ldots, \overline{s_n}) = \begin{cases}
{?}\alpha~(\text{fresh}) & \text{if } \forall i.\;\text{tail}(\overline{s_i}) = \bot \\
\tau & \text{otherwise, where } \tau~\text{is any non-}\bot~\text{tail and } \forall i.\;\text{tail}(\overline{s_i}) \in \lbrace \bot, \tau \rbrace
\end{cases}$$

The "otherwise" case is well-defined because the per-branch unification premises in [T-If](#T-If) and [T-Match](#T-Match) require all non-$\bot$ tails to be pairwise-unified before $\text{branchType}$ is applied: every non-$\bot$ tail collapses to the same $\tau$, so picking "any" is canonical. Divergence propagates through a binding whose RHS is a $\textbf{raise}$: the binding never produces a value, so the arm should not be forced to unify against a concrete type. Without this case, $\textbf{match}~e~\lbrace A \to \textbf{raise}~X;\; B \to \textbf{let}~\_ = \textbf{raise}~Y \rbrace$ would have $\sigma = \texttt{unit}$ (only the B arm survives the $\bot$ filter), pinning the whole match's type spuriously.

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

$\sigma$ is fixed by the premise $\sigma = \text{branchType}(\overline{s_1}, \overline{s_2})$: when both branches yield a value, $\sigma$ is their (pairwise-unified) common tail; when one diverges, $\sigma$ is the survivor's tail; when both diverge, $\sigma$ is a fresh ${?}\alpha$. Both branches receive the **same** $\Gamma_b$ (since only one executes at runtime). The if-without-else form (surface only) desugars to $\textbf{if}~e_c~\textbf{then}~\overline{s_1}~\textbf{else}~()$ and therefore has type $\texttt{unit}$. Mirrors [T-Match](#T-Match)'s divergent-arm carve-out for symmetry.

<a id="T-Match"></a>

$$\dfrac{
  \begin{array}{l}
  \Gamma = \Gamma_e \otimes \Gamma_b \\[2pt]
  \Gamma_e;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \qquad
  \text{exhaustive}(\text{strip}(\tau), \overline{p}) \\[4pt]
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

$\sigma$ is fixed by the premise $\sigma = \text{branchType}(\overline{s_1}, \ldots, \overline{s_n})$: the common type of non-diverging ($\text{tail} \neq \bot$) arms, or a fresh ${?}\alpha$ if all arms diverge. All arms receive the same $\Gamma_b$. Because $\text{strip}$ does not peel $@$, a thunk scrutinee $\tau = @\sigma$ leaves the pattern facing $@\sigma$ rather than $\sigma$ — pattern rules ([P-Ctor](#P-Ctor), [P-Record](#pattern-matching)) then fail to unify against the constructor/record shape. The user must force the thunk explicitly: $\textbf{match}\;@x\;\lbrace\ldots\rbrace$ routes the linear consumption through [T-Force](#T-Force).

<a id="T-Lambda"></a>

$$\dfrac{
  \begin{array}{l}
  \Gamma_\text{cap} = \lbrace x :^{1} S \in \Gamma \mid x \in \text{fv}(\overline{s}) \rbrace \\[2pt]
  \Gamma_\omega = \lbrace x :^{\omega} S \in \Gamma \mid x \in \text{fv}(\overline{s}) \rbrace \\[2pt]
  \forall x \in \text{fv}(\overline{s}) \cap \text{dom}(\Gamma).\;\Gamma(x) \neq \mathord{\sim}\sigma \quad\text{(no ref capture)} \\[2pt]
  q_i = \begin{cases} 1 & \text{if } \text{linear}(\tau_i) \\ \omega & \text{otherwise} \end{cases} \\[2pt]
  \overline{s}^\dagger = \begin{cases} \overline{s};\,\textbf{return}~() & \text{if}~\tau_r = \texttt{unit}~\wedge~\text{tail}(\overline{s}) \neq \bot \\ \overline{s} & \text{otherwise} \end{cases} \\[2pt]
  \Gamma_\omega,\, \Gamma_\text{cap},\, \overline{x_i :^{q_i} \tau_i};\, \rho_q;\, \tau_r \vdash_s \overline{s}^\dagger : \Gamma' \mathbin{!} \rho_e \\[2pt]
  \tau_r \neq \texttt{unit} \implies \text{tail}(\overline{s}^\dagger) = \bot \quad\text{(non-unit returns require explicit termination)} \\[2pt]
  \forall y :^1 S \in \Gamma'.\;y \in \lbrace\overline{x_i}\rbrace \wedge \text{autoDrop}(S) \quad\text{(P-FnEnd: no leaked linear at body end)} \\[2pt]
  \text{wfCap}(\rho_q) \quad \text{wfThrow}(\rho_e) \quad\text{(declared rows reference known caps / variants)} \\[2pt]
  \tau_\to = (\overline{\ell : \tau}) \to \tau_r;\, \rho_q;\, \rho_e \\[2pt]
  \tau_\to^\star = \begin{cases} \%\tau_\to & \text{if } \Gamma_\text{cap} \neq \emptyset \\ \tau_\to & \text{otherwise} \end{cases}
  \end{array}
}{
  \Gamma_\text{cap};\, \rho_q' \vdash_e \textbf{fn}~(\overline{\ell : \tau}) \to \tau_r;\, \rho_q;\, \rho_e~\textbf{do}~\overline{s}~\textbf{end} : \tau_\to^\star \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Lambda}$$

The lambda is pure ($\mathbin{!} \lbrace\rbrace$). It consumes $\Gamma_\text{cap}$ (captured linear bindings). The body environment includes $\Gamma_\omega$ (captured unrestricted bindings), $\Gamma_\text{cap}$, and the parameters $\overline{x_i :^{q_i} \tau_i}$ — each parameter's usage $q_i$ matches its type's linearity (mirroring [T-Let](#T-Let)). The closure-linearization premise $\tau_\to^\star$ promotes the lambda's type to $\%\tau_\to$ whenever any linear binding is captured: a closure that owns a linear resource is itself one-shot, so two uses of the same closure value would imply two consumptions of the resource. The same shape is reused in [T-Handler](#T-Handler) to linearize handler values that capture linears.

The conclusion's ambient row $\rho_q'$ is **not bound by any premise** — it is the caller's ambient at the lambda's construction site. The rule reads as "for any $\rho_q'$, …": the caller may construct a lambda under any ambient because lambda construction itself produces no effect ($\mathbin{!} \lbrace\rbrace$) and reads no capabilities. The lambda's own body is typed under the **declared** $\rho_q$ (the require row written into the arrow type), not under $\rho_q'$; the connection between $\rho_q'$ and $\rho_q$ is enforced later, at the call site, by [T-App](#T-App)'s $\text{unify}(\rho_q, \text{open}(\rho_q'))$ premise. Treating $\rho_q'$ as universally quantified is the intentional formalisation of "lambda construction is ambient-independent".

**P-FnEnd (function-end no-leak).** The body's output environment $\Gamma'$ must contain no linear binding except parameters whose declared type is auto-droppable. This formalises [drop.md](../drop)'s function-end check (`require_empty_or_droppable` in `src/typecheck/linearity.nx`) as a premise of T-Lambda rather than leaving it as an out-of-band obligation. Concretely:

- **Captured linears** ($\Gamma_\text{cap}$) flow into the body and must be consumed before body end; otherwise they would be silently dropped when the closure value returns, but the caller still believes the resource is alive via the closure's captured-state contract.
- **Locally introduced linears** (let-bindings inside $\overline{s}$ with linear RHS) likewise must be consumed; they have no consumer in any caller.
- **Linear parameters** ($q_i = 1$) must either be consumed by the body (transferred via a return / raise / argument-passing channel, per [drop.md](../drop) §Linear Consumption) or have $\text{autoDrop}(\tau_i)$ — the carve-out admits e.g. an array-typed parameter whose linear wrapper is structural rather than semantically resource-bearing.

P-FnEnd is the analogue at function-body scope of P-Block at block scope: both reject linear-leak at a scope boundary. T-Lambda is the only construct that crosses a function-body boundary, so the function-end check lives uniquely here; [T-Inject](#T-Inject) and [T-TryCatch](#T-TryCatch) discharge P-Block instead. The two together cover every closing scope in the language.

**Implicit-return desugaring.** The auxiliary $\overline{s}^\dagger$ in T-Lambda's premise formalises the surface convention from [semantics.md](../semantics) §Implicit Unit Return: a $\textbf{unit}$-returning lambda whose body does not already end in a divergent statement (i.e.\ $\text{tail}(\overline{s}) \neq \bot$) is desugared to $\overline{s};\,\textbf{return}~()$ before body typing. Non-unit returns get no desugaring — the rule's $\tau_r \neq \texttt{unit} \implies \text{tail}(\overline{s}^\dagger) = \bot$ premise then statically rejects an `i64`-returning lambda whose body is a let-statement or a bare expression statement that produces a value but never $\textbf{return}$s it. Together, the desugar and the premise pin the surface convention at rule level: unit returners may omit `return ()`; non-unit returners must explicitly `return` (or $\textbf{raise}$ / loop forever) on every control-flow path.

<a id="T-Raise-Ctor"></a>

$$\dfrac{
  \begin{array}{l}
  e = c(\overline{\ell : e_a}) \qquad
  c \in \text{variants}(\texttt{Exn}) \\[2pt]
  \Gamma;\, \rho_q \vdash_e c(\overline{\ell : e_a}) : \texttt{Exn} \mathbin{!} \rho_0
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e \textbf{raise}~e : {?}\alpha \mathbin{!} \lbrace c \rbrace \cup \rho_0
} \;\textsc{T-Raise-Ctor}$$

<a id="T-Raise-CtorNullary"></a>

$$\dfrac{
  \begin{array}{l}
  e = c \qquad c \in \text{variants}(\texttt{Exn}) \qquad
  \Gamma(c) = (\omega,\,\forall \overline{\alpha}.\,\texttt{Exn}) \\[2pt]
  \Gamma;\, \rho_q \vdash_e c : \texttt{Exn} \mathbin{!} \rho_0
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e \textbf{raise}~e : {?}\alpha \mathbin{!} \lbrace c \rbrace \cup \rho_0
} \;\textsc{T-Raise-CtorNullary}$$

<a id="T-Raise-Val"></a>

$$\dfrac{
  e~\text{is neither a constructor application nor a bare exception-constructor identifier} \qquad
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \qquad
  \text{unify}(\tau, \texttt{Exn})
}{
  \Gamma;\, \rho_q \vdash_e \textbf{raise}~e : {?}\alpha \mathbin{!} \lbrace \texttt{Exn} \rbrace \cup \rho_0
} \;\textsc{T-Raise-Val}$$

The split records variant identity in the effect row. **T-Raise-Ctor** fires when the raise expression is syntactically a constructor application (e.g.\ $\textbf{raise}~\texttt{NotFound}(\textit{path}: p)$) — the row gets the precise constructor name $\lbrace \texttt{NotFound} \rbrace$. **T-Raise-CtorNullary** fires for the bare-identifier form of a zero-field exception (e.g.\ $\textbf{raise}~\texttt{MissingMain}$, where $\texttt{MissingMain}$ is bound at value scheme $\forall \overline{\alpha}.\,\texttt{Exn}$ by the nullary clause of [D-Exception](#D-Exception)) — the row again gets the precise variant name $\lbrace \texttt{MissingMain} \rbrace$, not the catch-all sentinel. **T-Raise-Val** fires for the residual case — a variable, projection, or other expression yielding $\texttt{Exn}$ (typically a catch-bound binding being re-raised: $\textbf{catch}~e \to \textbf{raise}~e$); the row gets the catch-all sentinel $\lbrace \texttt{Exn} \rbrace$, which subsumes any variant via [U-Row-Exn](#U-Row-Exn). All three rules produce the universal type $?\alpha$ since $\textbf{raise}$ never returns to its caller. The companion [T-TryCatch](#T-TryCatch) consumes these row entries — specific-variant arms subtract specific entries, catch-all arms subtract $\texttt{Exn}$ and any constructors covered by U-Row-Exn.

The disambiguation between T-Raise-CtorNullary and T-Raise-Val on a bare identifier follows [P-CtorNullary](#P-CtorNullary)'s convention: $\Gamma$-lookup decides. If $\Gamma(c)$ is a value scheme rooted at $\texttt{Exn}$ (i.e.\ $c$ was declared by the nullary clause of D-Exception), T-Raise-CtorNullary fires and preserves variant precision; otherwise (a catch-bound $e : \texttt{Exn}$, a record-field projection, etc.), T-Raise-Val fires and assigns the catch-all sentinel.

[T-Handler](#T-Handler) types $\textbf{handler}~x~[\textbf{require}~\rho]~\textbf{do}~\overline{\ell = e}~\textbf{end}$ — a record-of-lambdas implementing the methods of port $x$. We assume a global lookup $\text{methods}(x)$ returning the method signatures declared for port $x$ (populated by port declarations, see §1):

$$\text{methods}(x) = \lbrace\; \ell_j : (\overline{\pi_j}) \to \kappa_j;\, \alpha_j;\, \beta_j \;\mid\; j \in J \;\rbrace$$

where $\alpha_j$ and $\beta_j$ are the require row and throw row declared for method $\ell_j$ on port $x$. The handler's arms must be in 1-1 correspondence with $\text{methods}(x)$.

<a id="T-Handler"></a>

$$\dfrac{
  \begin{array}{l}
  \text{methods}(x) = \lbrace\; \ell_j : (\overline{\pi_j}) \to \kappa_j;\, \alpha_j;\, \beta_j \;\mid\; j \in J \;\rbrace \\[2pt]
  \Gamma_\text{cap} = \lbrace y :^{1} S \in \Gamma \mid y \in \textstyle\bigcup_j \text{fv}(e_j) \rbrace \\[2pt]
  \Gamma_\omega = \lbrace y :^{\omega} S \in \Gamma \mid y \in \textstyle\bigcup_j \text{fv}(e_j) \rbrace \\[2pt]
  \forall y \in \textstyle\bigcup_j \text{fv}(e_j) \cap \text{dom}(\Gamma).\;\Gamma(y) \neq \mathord{\sim}\sigma \\[2pt]
  \forall j \in J.\;\Gamma_\omega,\, \Gamma_\text{cap};\, \rho_q \vdash_e e_j : (\overline{\pi_j}) \to \kappa_j;\, \alpha_j;\, \beta_j \mathbin{!} \lbrace\rbrace \\[2pt]
  \text{wfCap}(\rho_\text{annot}) \quad\text{(handler's optional require annotation references known caps)} \\[2pt]
  \rho_\text{req} = \textstyle\bigcup_j \alpha_j \cup \rho_\text{annot} \\[2pt]
  \tau_h = \textbf{handler}\;x\;\rho_\text{req}
  \end{array}
}{
  \Gamma_\text{cap};\, \rho_q' \vdash_e \textbf{handler}~x~[\textbf{require}~\rho_\text{annot}]~\textbf{do}~\overline{\ell_j = e_j}~\textbf{end} : \tau_h^\star \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Handler}$$

$$\tau_h^\star = \begin{cases} \%\tau_h & \text{if } \Gamma_\text{cap} \neq \emptyset \\ \tau_h & \text{otherwise} \end{cases}$$

The handler is pure ($\mathbin{!} \lbrace\rbrace$) — its construction has no effect; effects are deferred until the handler is injected and a method is invoked. Each arm $e_j$ must be a lambda whose function type matches the port's declared signature for method $\ell_j$. The handler's require row $\rho_\text{req}$ aggregates each arm's declared require row $\alpha_j$ (carried on the lambda's arrow type and validated against the lambda body in [T-Lambda](#T-Lambda)/[T-App](#T-App)) and the optional surface annotation $\rho_\text{annot}$ (defaulting to $\lbrace\rbrace$ if absent). [T-Inject](#T-Inject) checks that $\rho_\text{req}$ is satisfied by the surrounding ambient row at the inject site. Closure linearization mirrors [T-Lambda](#T-Lambda): if any arm captures a linear binding, the entire handler value becomes $\%\tau_h$ — only one $\textbf{inject}$ may consume it.

As with [T-Lambda](#T-Lambda), the conclusion's ambient $\rho_q'$ is universally quantified — handler construction is ambient-independent (the per-arm $\alpha_j$ are validated against the arms' own bodies, not the surrounding ambient). The connection between $\rho_q'$ and $\rho_\text{req}$ is enforced at the [T-Inject](#T-Inject) site.

$$\dfrac{
  x :^{\omega} \forall\overline{\alpha}.\,\tau \in \Gamma \qquad
  \tau' = \text{inst}(\forall\overline{\alpha}.\,\tau) \qquad
  \sigma = \text{stripBorrow}(\tau')
}{
  \Gamma;\, \rho_q \vdash_e \&x : \&\sigma \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Borrow}$$

$$\text{stripBorrow}(\tau) = \begin{cases}
\sigma & \text{if } \tau \in \lbrace \%\sigma,\, @\sigma,\, \&\sigma,\, \mathord{\sim}\sigma \rbrace \\
\tau & \text{otherwise}
\end{cases}$$

Borrowing does not consume the binding. Only unrestricted bindings can be borrowed. T-Borrow uses $\text{stripBorrow}$ rather than $\text{strip}$ because borrowing a $\mathord{\sim}\tau$ binding should yield a $\&\tau$ borrow of the cell's contents, not a nonsensical $\&(\mathord{\sim}\tau)$ borrow-of-cell. The pattern-side $\text{strip}$ deliberately keeps $\mathord{\sim}$ in place — refs cannot be match scrutinees — so the two operators diverge precisely at the $\mathord{\sim}$ case.

<a id="T-Force"></a>

$$\dfrac{
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \qquad
  \sigma~\text{fresh} \qquad
  \text{unify}(\tau, @\sigma)
}{
  \Gamma;\, \rho_q \vdash_e @e : \sigma \mathbin{!} \rho_0
} \;\textsc{T-Force}$$

The thunk is consumed via [T-Var](#T-Var) ($q = 1$) in the sub-derivation. Premise uses $\text{unify}(\tau, @\sigma)$ with a fresh $\sigma$ rather than a structural pattern $\tau = @\sigma$ on the premise's right-hand side, so that an unresolved inference variable $\tau = {?}\alpha$ — common when $e$ is a generic-typed parameter inside a $\forall$-quantified body — is pinned to $@\sigma$ by the unifier instead of leaving the rule inapplicable. The two forms agree on already-concrete $\tau = @\sigma'$ shapes ($\text{unify}$ succeeds with $\sigma = \sigma'$); they diverge on unresolved $\tau$, where only the unification form makes the derivation tree mechanically constructible.

$$\dfrac{
  \Gamma = \Gamma_1 \otimes \ldots \otimes \Gamma_k \qquad
  \text{distinct}(\overline{\ell}) \qquad
  \forall i.\;\Gamma_i;\, \rho_q \vdash_e e_i : \tau_i \mathbin{!} \rho_i
}{
  \Gamma;\, \rho_q \vdash_e \lbrace \overline{\ell : e} \rbrace : \lbrace \overline{\ell : \tau_i} \rbrace \mathbin{!} \textstyle\bigcup_i \rho_i
} \;\textsc{T-Record}$$

$\text{distinct}(\overline{\ell})$ holds iff $\lvert\overline{\ell}\rvert = \lvert\lbrace \ell_1, \ldots, \ell_k \rbrace\rvert$ — the label sequence has no duplicates. This makes record types label-sets, not multisets: $\lbrace a:1, a:2\rbrace$ is rejected at construction time, so [T-Proj](#T-Proj) and $\text{fields}$ never face an ambiguous lookup.

<a id="T-Proj"></a>

$$\dfrac{
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \qquad
  \neg\text{linear}(\tau) \qquad
  (\ell : \sigma) \in \text{fields}(\tau)
}{
  \Gamma;\, \rho_q \vdash_e e.\ell : \sigma \mathbin{!} \rho_0
} \;\textsc{T-Proj}$$

The $\neg\text{linear}(\tau)$ premise rejects projection on linear records. Since $\text{linear}$ is structural (§Linearity), it holds whenever $\tau$ is itself $\%\sigma$/$@\sigma$/$[\lvert\,\sigma\,\rvert]$ *or* any field's type is linear. Allowing $e.\ell$ on such a record would consume $e$ via the sub-derivation while exposing only one field — silently dropping the other linear obligations. Linear-record destructuring is funneled exclusively through pattern matching ([P-Record](#pattern-matching)), where $\biguplus$ requires every linear field's binding to be picked up. This matches the consumption-channel list in [types.md](../types) (function call, pattern match, return, assignment).

### Statements

$$\Gamma;\, \rho_q;\, \tau_r \vdash_s s : \Gamma' \mathbin{!} \rho_e$$

$\Gamma'$ is the updated environment (new bindings from [T-Let](#T-Let)). $\tau_r$ is the expected return type of the enclosing function.

[T-Let](#T-Let) resolves numeric literals and applies sigil modalities via two auxiliaries. $\text{default}$ defaults $\texttt{intlit}$/$\texttt{floatlit}$ at binding sites where no concrete type was inferred:

$$\text{default}(\tau) = \begin{cases}
\texttt{i64} & \text{if } \tau = \texttt{intlit} \\
\texttt{f64} & \text{if } \tau = \texttt{floatlit} \\
\tau & \text{otherwise (applied recursively to all subterms)}
\end{cases}$$

$\text{wrapSigil}$ wraps the inferred type with the modality corresponding to the binding's sigil. It is **idempotent**: wrapping with a modality the type already carries at the outermost level returns the type unchanged, avoiding ill-formed double-wraps like $\%\%\sigma$ or $@@\sigma$ that no surface syntax can describe.

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

Idempotency makes $\textbf{let}~\%x = \textit{make\_linear}()$ produce $\%T$ regardless of whether $\textit{make\_linear}$ returns $T$ (weakened) or $\%T$ — the binding's stated modality is the truth. Pattern $\text{strip}$ removes one layer; idempotent $\text{wrapSigil}$ ensures that one layer is always present, never two.

<a id="T-Let"></a>

$$\dfrac{
  \begin{array}{l}
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \\[2pt]
  \tau' = \text{default}(\tau) \\[2pt]
  \mu = \mathord{\sim} \implies \neg\text{linear}(\tau') \\[2pt]
  \tau_f = \text{wrapSigil}(\mu, \tau') \qquad
  S = \text{mono}(\tau_f) \\[2pt]
  q = \begin{cases} 1 & \text{if } \text{linear}(\tau_f) \\ \omega & \text{otherwise} \end{cases}
  \end{array}
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{let}~\mu\,x = e : (\Gamma \setminus\!\!\setminus e),\, x :^{q} S \mathbin{!} \rho_0
} \;\textsc{T-Let}$$

When the surface syntax includes a type annotation ($\textbf{let}~\mu\,x : \sigma = e$), an additional premise $\text{unify}(\tau', \sigma)$ is required and $\tau'$ is replaced by $\sigma$. When the annotation is absent, $\tau'$ remains as inferred (possibly containing unification variables that are resolved later or defaulted).

The side-condition $\mu = \mathord{\sim} \implies \neg\text{linear}(\tau')$ enforces the [types.md](../types#mutable-references-) invariant that mutable-ref cells cannot hold linear values. Without it, $\textbf{let}~\mathord{\sim}r = \textit{make\_linear}()$ would produce a $\mathord{\sim}\%T$ binding; subsequent $\mathord{\sim}r$ deref-reads would each yield a fresh $\%T$ value, duplicating the linear resource. The check applies uniformly to inferred types and to explicit annotations ($\textbf{let}~\mathord{\sim}x : \%T = e$). Linearity is structural, so the check also rejects $\mathord{\sim}$ cells holding records or ADTs with any linear component.

T-Let always produces a monomorphic scheme (see P8). The single exception is the variable-aliasing form below, which fires only when the surface form is exactly $\textbf{let}~x = y$ with no sigil, no annotation, and $y$ bound to a polymorphic scheme. All other shapes — annotated, sigil-prefixed, or with a non-variable RHS — fall through to T-Let.

<a id="T-Let-Alias"></a>

$$\dfrac{
  y :^{\omega} \forall\overline{\alpha}.\,\sigma \in \Gamma \qquad
  \overline{\alpha} \neq \emptyset \qquad
  \text{pure}(\Gamma \setminus \lbrace y \rbrace)
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{let}~x = y : \Gamma,\, x :^{\omega} (\forall\overline{\alpha}.\,\sigma) \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Let-Alias}$$

T-Let-Alias preserves polymorphism across plain rebinding: subsequent uses of $x$ re-instantiate $\forall\overline{\alpha}.\,\sigma$ via [T-Var](#T-Var) just as uses of $y$ would. Without this rule, $\textbf{let}~f = \textit{id}$ would instantiate $\textit{id}$ once at the binding site (collapsing $f$ to a monotyped arrow), defeating the polymorphism of $\textit{id}$ at every use of $f$. The carve-out is intentionally narrow — RHS must be a bare variable — so that $\text{mono}$-by-default remains the rule, not the exception. Implementation: see `infer.nx::alias_poly_scheme`.

<a id="T-Let-PolyFn"></a>

The second carve-out fires when the RHS is a $\textbf{fn}$ literal carrying an explicit type-parameter list. This is the **only** way a fresh polymorphic scheme enters $\Gamma$ (per the narrative of §Polymorphism Introduction); T-Let-Alias only forwards an existing scheme.

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

T-Let-PolyFn formalises the rewrite given in §Polymorphism Introduction. The body $\overline{s}$ is typed under $\Gamma$ extended with the type-parameter symbols $\overline{X_i{:}\kappa_i}$: each $X_i$ behaves as a **rigid** variable — not a fresh unification variable. Parameter and return annotations that mention $X_i$ pass through unification unchanged (they unify only with themselves), so the body cannot specialise $X_i$ to a concrete type. Generalisation happens once, at the binding site, by quantifying the inferred $\tau_\to$ over $\overline{X_i}$.

Three restrictions are inherited from the surface notation:

- **Sigil-free, annotation-free LHS.** The carve-out fires only on $\textbf{let}~x = e$ without sigil or type annotation. Sigil-prefixed (`%x`, `~x`) or annotated forms fall through to [T-Let](#T-Let), which produces a monomorphic scheme; user code wanting a polymorphic scheme on a sigil binding does not exist in the surface.
- **No linear closure.** The premise $\tau_\to \neq \%\sigma$ rejects polymorphic generalisation over a closure that captured a linear binding — a $\%$-wrapped arrow is one-shot at every instantiation, which is incoherent with $\forall$. Capture-free lambdas (the common case for top-level $\textbf{fn}$ declarations) and lambdas closing only over $\omega$ bindings satisfy this premise.
- **Quantifier list is non-empty.** When $n = 0$, the rule reduces to T-Let (with $S = \text{mono}(\tau_\to)$); there is no observable difference, so the spec presents the polymorphic case as the carve-out.

Together with T-Let-Alias, these two rules exhaust the entry-points for polymorphic schemes in $\Gamma$, justifying P8's "no implicit generalization" property mechanically rather than only by side-remark.

$$\dfrac{
  \tau_r \neq \bot \qquad
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \qquad
  \text{unify}(\tau, \tau_r)
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{return}~e : \Gamma \mathbin{!} \rho_0
} \;\textsc{T-Return}$$

The premise $\tau_r \neq \bot$ rejects $\textbf{return}~e$ outside any enclosing function. $\bot$ is the **return-context sentinel** used to mark the absence of an enclosing function (see §1.2 below); a top-level $\textbf{let}$ via [D-Let-Top](#D-Let-Top) types its body under $\tau_r = \bot$, so a $\textbf{return}$ statement at module scope is statically rejected.

<a id="T-Assign"></a>

$$\dfrac{
  x :^{\omega} (\emptyset,\, \mathord{\sim}\tau) \in \Gamma \qquad
  \Gamma;\, \rho_q \vdash_e e : \sigma \mathbin{!} \rho_0 \qquad
  \text{unify}(\sigma, \tau)
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \mathord{\sim}x \leftarrow e : \Gamma \mathbin{!} \rho_0
} \;\textsc{T-Assign}$$

[T-Inject](#T-Inject) extends the ambient capability row with the ports each injected handler provides, after checking that the ambient row already satisfies what each handler requires. $\text{merge}$ unions two rows:

$$\text{merge}(\rho_1, \rho_2) = \rho_1 \cup \rho_2 \quad\text{(row union, deduplicating by type identity)}$$

Block-scoped constructs ($\textbf{inject}$, $\textbf{try}$/$\textbf{catch}$, and any future bracketing form) close their inner environment back to the outer scope via $\text{closeBlock}$, which drops bindings introduced *inside* the block from the output environment. The lexical-scoping rule from [semantics.md](../semantics) — *"Bindings are visible in the block where they are defined and in nested blocks"* — is enforced statically here: an inner $\textbf{let}$ may shadow an outer name within the block, but the shadow ceases to exist at block end and the outer binding becomes visible again. A companion premise rejects programs that leave a linear binding introduced *inside* the block unconsumed at block end — those resources have no consumer in the outer scope and would silently leak.

$$\text{closeBlock}(\Gamma_\text{inner}, \Gamma_\text{outer}) = \lbrace x :^q S \mid x \in \text{dom}(\Gamma_\text{outer}) \cap \text{dom}(\Gamma_\text{inner}),\; x :^q S \in \Gamma_\text{outer} \rbrace$$

Two design properties of this definition:

- **Binding info comes from $\Gamma_\text{outer}$, not $\Gamma_\text{inner}$.** When an inner $\textbf{let}$ shadows an outer name, the shadow lives only in $\Gamma_\text{inner}$ during the block; at block end, the outer value is restored. Filtering $\Gamma_\text{inner}$ by outer-dom alone would leak the shadowed scheme into the outer scope and break lexical scoping (e.g.\ outer `x : i64` shadowed by inner `let x = "s"` would surface as `x : string` after the block).
- **Membership in $\Gamma_\text{inner}$ still gates restoration.** A linear outer binding consumed inside the block is removed from $\Gamma_\text{inner}$, and the intersection therefore excludes it from the output. Consumption inside the block reaches the outer scope; only the shadowed-value channel is broken.

A corollary: shadowing a *linear* outer binding inside a closed block is operationally equivalent to consume-and-rebind for the duration of the block. The outer linear remains in $\Gamma_\text{outer}$ unchanged, but P-Block (below) requires the shadow itself to be consumed before block end, and the outer's quantity/scheme is then restored by the intersection. Programs relying on subtle re-resurrection of a shadowed outer linear should use distinct names.

$$\textbf{P-Block}~\text{(linear no-leak).}\quad\forall x :^1 S \in \Gamma_\text{inner}.\;x \in \text{dom}(\Gamma_\text{outer}) \wedge x :^1 S \in \Gamma_\text{outer}$$

P-Block rejects two failure modes at the block boundary: (i) a linear binding introduced inside the block ($x \notin \text{dom}(\Gamma_\text{outer})$) that survives to block end has no outer consumer and silently leaks; (ii) a linear outer binding shadowed by an inner $\textbf{let}$ to a *different* scheme — $x \in \text{dom}(\Gamma_\text{outer})$ but $x :^1 S \in \Gamma_\text{inner}$ with $S$ not matching $\Gamma_\text{outer}(x)$ — must have its shadow consumed before block end so the outer binding can be restored unambiguously.

P-Block is intentionally one-directional: a linear binding from $\Gamma_\text{outer}$ that survives unchanged through the body remains available for consumption after the block (the consumer runs in outer scope and still sees $x$). Only *newly introduced* linear bindings, and shadows that diverged from the outer scheme, must be consumed before block end. This mirrors the function-end check in [drop.md](../drop) but is strictly stronger: function-end catches leftover linears only at the outermost frame, while P-Block catches them at every nested block boundary.

<a id="T-Inject"></a>

$$\dfrac{
  \begin{array}{l}
  \Gamma = \Gamma_h \otimes \Gamma_\text{body} \\[2pt]
  \forall i.\;\text{strip}(\text{inst}(\Gamma_h(h_i))) = \textbf{handler}\;P_i\;\rho_i \\[2pt]
  \forall i.\;\rho_i \subseteq \rho_q \quad\text{(handler requires are satisfied by the ambient row)} \\[2pt]
  \rho_q' = \text{merge}(\rho_q,\, \lbrace \overline{P} \rbrace) \\[2pt]
  \Gamma_\text{body};\, \rho_q';\, \tau_r \vdash_s \overline{s} : \Gamma' \mathbin{!} \rho_0 \\[2pt]
  \forall x :^1 S \in \Gamma'.\;x \in \text{dom}(\Gamma_\text{body}) \wedge x :^1 S \in \Gamma_\text{body} \quad\text{(P-Block: no leaked linear, no diverged shadow)}
  \end{array}
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{inject}~\overline{h}~\textbf{do}~\overline{s}~\textbf{end} : \text{closeBlock}(\Gamma',\, \Gamma_\text{body}) \mathbin{!} \rho_0
} \;\textsc{T-Inject}$$

The handler's require row $\rho_i$ is a *precondition* on the inject site, not a grant to the body. The body sees only $\rho_q' = \rho_q \cup \lbrace \overline{P} \rbrace$ — the original ambient plus the ports each handler implements. The earlier formulation merged $\text{ports}(\overline{\rho_i})$ into $\rho_q'$ as well, which would let the body access capabilities the surrounding context never granted, breaking capability containment. With requires moved to a containment premise instead, the inject site fails to type-check unless the surrounding scope already provides every capability each handler needs.

Two linearity-related details:

- **Strip on handler-pattern match.** [T-Handler](#T-Handler) wraps the handler's type with $\%$ when any arm captures a linear binding, producing $\%(\textbf{handler}\;P\;\rho)$. Without $\text{strip}$, the structural pattern $\textbf{handler}\;P_i\;\rho_i$ in this premise would not match a $\%$-wrapped handler — every captured-linear handler would be unusable. $\text{strip}$ peels the $\%$ wrapper before the structural match, mirroring its use on match scrutinees in [T-Match](#T-Match). Note that $\text{strip}$ does **not** peel $@$: a handler of type $@(\textbf{handler}\;P\;\rho)$ fails this premise, requiring the user to force it explicitly (e.g. $\textbf{inject}\;@h\;\textbf{do}\;\ldots\;\textbf{end}$) so the thunk's linear consumption goes through [T-Force](#T-Force).
- **$\otimes$-split between handler lookup and body.** $\Gamma$ is split into $\Gamma_h$ (used to look up the handler bindings $h_i$) and $\Gamma_\text{body}$ (which flows into $\overline{s}$). For unrestricted handlers ($q = \omega$), $\otimes$ assigns the binding to both partitions, so the body can still call methods on the same handler. For linear handlers ($q = 1$, e.g. $\%h$), $\otimes$ assigns the binding to exactly one partition: when used at the inject site it is *not* available in the body, preventing the documented "only one inject may consume it" promise from being silently violated by an in-body re-use.

[T-PortCall](#T-PortCall) types a port-method invocation $x.\ell(\overline{\ell':e})$ inside a scope where a handler for port $x$ has been injected. Method signatures are read from the global $\text{methods}(x)$ environment populated by port declarations:

<a id="T-PortCall"></a>

$$\dfrac{
  \begin{array}{c}
  \Gamma = \Gamma_1 \otimes \ldots \otimes \Gamma_k \\[2pt]
  \text{methods}(x).\ell = (\overline{\ell' : P}) \to \kappa;\, \alpha;\, \beta \\[2pt]
  \alpha \subseteq \rho_q \qquad
  x \in \rho_q \\[2pt]
  \forall i.\;\Gamma_i;\, \rho_q \vdash_e e_i : \tau_i \mathbin{!} \rho_i \\[2pt]
  \forall i.\;\begin{cases} \text{unify}(\tau_i, \text{strip}(P_i)) & \text{if } P_i = \%\sigma \wedge \neg\text{linear}(\tau_i) \\ \text{unify}(\tau_i, P_i) & \text{otherwise} \end{cases}
  \end{array}
}{
  \Gamma;\, \rho_q \vdash_e x.\ell(\overline{\ell' : e}) : \kappa \mathbin{!} \beta \cup \textstyle\bigcup_i \rho_i
} \;\textsc{T-PortCall}$$

T-PortCall is the missing link between handler declarations and call sites. Three premises wire the rows:

- $\alpha \subseteq \rho_q$ — the method's declared **require** row must be a subset of the ambient capability row, so the caller already holds whatever capabilities this method invocation transitively needs (delegated to the handler's body).
- $x \in \rho_q$ — the port $x$ itself must be in the ambient row, meaning a handler for $x$ has been brought into scope by an enclosing [T-Inject](#T-Inject) (or by the function's own require annotation).
- $\beta$ joins the call's effect row — exceptions a method may raise propagate to the caller's $\rho_e$.

The argument unification follows [T-App](#T-App)'s shape, including the $\%$-weakening carve-out. Linear arguments ($\tau_i$ already linear) bypass weakening and unify directly against the linear parameter slot. The result type $\kappa$ is the method's declared return type; no instantiation step is needed because **port declarations are monomorphic at every level** — port names $X$ take no type parameters in the surface grammar (`cap X do ... end`, never `cap X<T> do ... end`), and method signatures inside a port are not generalised by [D-Port](#D-Port). The parser rejects the polymorphic-port form at the declaration site; the spec therefore needs no rule for "instantiating a port's type parameters at the call site".

If polymorphic ports become a surface feature in the future (e.g.\ for a collection-style cap `Vec<T>`), D-Port would have to store a scheme $\forall \overline{\alpha}.\,\text{methods}$ and T-PortCall would read the concrete instantiation $\overline{\sigma}$ off the injected handler's type (extending $\textbf{handler}\;X\;\rho$ to $\textbf{handler}\;X\langle \overline{\sigma}\rangle\;\rho$). This is recorded here as a forward-pointer, not a current rule.

<a id="T-TryCatch"></a>

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

The output environment is $\text{closeBlock}(\Gamma_1, \Gamma)$ — $\Gamma_1$ (the try-block's evolved environment) restricted to the outer scope $\Gamma$. Bindings introduced *inside* the try-body — pattern bindings on $\textbf{let}$, locals scoped to the try — are dropped at the construct's end, matching the lexical-scoping rule. The catch-arm output environments $\Gamma_i'$ are not threaded into the construct's output: the conservative choice picks the try-success path's view of $\Gamma$, because a catch arm runs only when the try-body raised before completing, leaving the precise consumption state of outer linears statically indeterminate. Both the try-body and every catch arm carry the P-Block premise, ensuring no linear binding introduced inside either branch leaks past the construct.

Variant-precise residual computation requires two auxiliaries:

$$\text{caughtVariants}(\overline{p}) = \bigcup_i \begin{cases}
\lbrace c \rbrace & \text{if}~p_i = c~\text{or}~p_i = c(\overline{\ell : p'})~\text{and}~c \in \text{variants}(\texttt{Exn}) \\
\emptyset & \text{otherwise (wildcard, variable pattern)}
\end{cases}$$

A group-name pattern $G$ has no clause here — group patterns are flattened to their member set $\lbrace C_1, \ldots, C_n \rbrace$ at parse time (see §Row Types) and surface as a fan of constructor-pattern arms before reaching the typing rules. caughtVariants therefore sees only individual constructors $c$. The auxiliary $\text{members}(G)$ is the parse-time projection that gives that fan its contents; it is *not* read by any typing rule but is referenced by D-ExceptionGroup and the parse-time expansion narrative.

$$\text{members}(G) = \lbrace C_1, C_2, \ldots, C_n \rbrace \quad\text{where}~G~\text{was declared}~\textbf{exception group}~G = C_1 \mathrel{\vert} \ldots \mathrel{\vert} C_n$$

Nesting is resolved transitively: if $G_2 = G_1 \mathrel{\vert} C_k$ and $G_1 = C_1 \mathrel{\vert} C_2$, then $\text{members}(G_2) = \lbrace C_1, C_2, C_k \rbrace$.

$$\text{hasCatchAll}(\overline{p}) = \exists i.\;p_i = \_ \;\vee\; p_i~\text{is a variable pattern}~x$$

The catch-all condition $\text{hasCatchAll}$ is *syntactic*: only an explicit wildcard arm $\_ \to \ldots$ or a single-variable arm $e \to \ldots$ (binding the exception value at type $\texttt{Exn}$) clears the catch-all sentinel and any remaining declared-variant entries. A *closed enumeration* of currently-declared $\texttt{Exn}$ variants does **not** count — because $\texttt{Exn}$ is extensible across modules, a closed enumeration that is exhaustive at the catch site can become inexhaustive when a downstream module declares a new variant, silently corrupting the throws-row of any function whose body contains the now-stale catch. Requiring a syntactic catch-all closes that cross-module hole.

Variant subtraction enables partial catches: catching only $\texttt{NotFound}$ from a try-row of $\lbrace \texttt{NotFound}, \texttt{PermDenied} \rbrace$ leaves $\lbrace \texttt{PermDenied} \rbrace$ in the residual. Group catches (e.g. $\textbf{catch}~\vert~\texttt{IOError} \to \ldots$) expand to their member set via $\text{members}(G)$ at parse time; the formal rule sees only the expanded constructor list (see [Exception Groups](../exception-groups)). Arms may add new effects $\rho_i$ (if an arm itself raises), which always join the residual row regardless of catch-all status.

<a id="T-While"></a>

$$\dfrac{
  \begin{array}{l}
  \Gamma;\, \rho_q \vdash_e e_c : \tau_c \mathbin{!} \rho_c \qquad
  \text{unify}(\tau_c, \texttt{bool}) \\[2pt]
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \overline{s} : \Gamma' \mathbin{!} \rho_b \\[2pt]
  \lbrace x :^1 S \in \Gamma' \rbrace = \lbrace x :^1 S \in \Gamma \rbrace \quad\text{(P-Loop: linear set preserved across iterations)}
  \end{array}
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{while}~e_c~\textbf{do}~\overline{s}~\textbf{end} : \Gamma \mathbin{!} \rho_c \cup \rho_b
} \;\textsc{T-While}$$

T-While types a while loop as a statement of unit-shaped effect: the body may run zero or more times, so the output environment is fixed to the input $\Gamma$ (no new bindings escape — the loop is block-scoped) and the linear set must be **invariant across one iteration**. P-Loop is the loop-specific analogue of P-Block: every linear binding in $\Gamma$ must survive unchanged in $\Gamma'$, and $\Gamma'$ contains no linear binding absent from $\Gamma$. Equivalently — using the env-difference notation from §Environment and Usage — the linear *restriction* of $\Gamma'$ matches that of $\Gamma$ as sets of $(name, q=1, scheme)$ triples.

The premise rejects three failure modes:

- **Consume-then-loop.** If body iteration 1 consumes a linear $\%h$ from $\Gamma$ ($\%h \in \Gamma$ but $\%h \notin \Gamma'$), iteration 2 has no $\%h$ — would be a use-after-consume on a value the type system claims is still available outside the loop. P-Loop's $\subseteq$ direction rejects this.
- **Leak-into-loop.** If the body introduces a new linear $\%g$ that survives to body end ($\%g \in \Gamma'$ but $\%g \notin \Gamma$), the loop would either accumulate $\%g$ instances across iterations or silently drop them. P-Loop's $\supseteq$ direction rejects this — matching the impl's "while body must preserve linear set" check (`src/typecheck/linearity.nx`).
- **Shadow-rebind of outer linear.** A body $\textbf{let}~\%h = \ldots$ that shadows an outer $\%h$ to a different scheme falls under leak-into-loop after the inner shadow's consumption: the shadow's scheme differs from $\Gamma(\%h)$, so the set equality fails.

Surface `for x in start..end do s̄ end` desugars to `while` with an explicit counter binding and increment; the desugaring is handled at lowering, before T-While fires. Surface `break` / `continue` are also lowered (to early-exit on a synthesized boolean), so the core calculus sees only the form above. The output Γ is the *input* Γ even when the body diverges (`return` inside the body short-circuits the enclosing function via $\textbf{return}$'s own typing; T-While simply records that the loop produces no observable binding update).

<a id="T-LetPat"></a>

$$\dfrac{
  \neg\text{diverges}(e) \qquad
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \qquad
  \text{exhaustive}(\tau, [p]) \qquad
  (\Gamma \setminus\!\!\setminus e) \vdash p : \tau \Rightarrow \Gamma'
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{let}~p = e : \Gamma' \mathbin{!} \rho_0
} \;\textsc{T-LetPat}$$

<a id="T-LetPat-Diverge"></a>

$$\dfrac{
  \text{diverges}(e) \qquad
  \Gamma;\, \rho_q \vdash_e e : \tau \mathbin{!} \rho_0 \qquad
  (\Gamma \setminus\!\!\setminus e) \vdash p : \tau \Rightarrow \Gamma'
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \textbf{let}~p = e : \Gamma' \mathbin{!} \rho_0
} \;\textsc{T-LetPat-Diverge}$$

$\text{diverges}(e)$ holds iff $e$ is syntactically $\textbf{raise}~e'$ (for any $e'$) — the only expression form that produces no value. The split rules avoid the ill-defined case $\text{exhaustive}(?\alpha, [p])$ that would otherwise arise: T-Raise gives $\textbf{raise}$ the type $?\alpha$ (a fresh unification variable), against which the Maranget head-shape rules (Exh-Bool, Exh-Sum, Exh-Record) cannot fire — a non-wildcard pattern like $\texttt{Some}(y)$ would leave the check stuck. T-LetPat-Diverge bypasses exhaustiveness because divergence semantically *short-circuits* the binding: the pattern is never actually destructured at runtime. The pattern is still typed via $\Gamma \vdash p : \tau$ so the body's $\Gamma'$ contains the right bindings (their types are $?\alpha$-instantiations, but they are unreachable). This carve-out mirrors the $\text{tail}(\overline{s})$ classification of $\textbf{let}~\mu\,x = \textbf{raise}~e'$ as $\bot$ (§Expressions, T-If/T-Match).

### Statement Sequences

Function bodies, branch arms, and the bodies of $\textbf{inject}$ and $\textbf{try}$ are all sequences $\overline{s} = s_1; s_2; \ldots; s_n$. The sequence judgment $\Gamma;\,\rho_q;\,\tau_r \vdash_s \overline{s} : \Gamma' \mathbin{!} \rho_e$ is built from two rules:

<a id="T-Seq-Empty"></a>

$$\dfrac{}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s \cdot : \Gamma \mathbin{!} \lbrace\rbrace
} \;\textsc{T-Seq-Empty}$$

<a id="T-Seq-Cons"></a>

$$\dfrac{
  \begin{array}{l}
  \Gamma;\, \rho_q;\, \tau_r \vdash_s s : \Gamma_1 \mathbin{!} \rho_1 \\[2pt]
  \Gamma_1;\, \rho_q;\, \tau_r \vdash_s \overline{s'} : \Gamma_2 \mathbin{!} \rho_2 \\[2pt]
  \text{tail}(s) \neq \bot \;\vee\; \overline{s'} = \cdot
  \end{array}
}{
  \Gamma;\, \rho_q;\, \tau_r \vdash_s s; \overline{s'} : \Gamma_2 \mathbin{!} \rho_1 \cup \rho_2
} \;\textsc{T-Seq-Cons}$$

T-Seq-Cons threads the environment ($\Gamma_1$ from the head feeds into the tail) and unions the effect rows. The premise $\text{tail}(s) \neq \bot \vee \overline{s'} = \cdot$ rejects **dead statements after divergence**: if $s$ is $\textbf{return}~e$, $\textbf{raise}~e$ (as expression statement), $\textbf{let}~\mu\,x = \textbf{raise}~e'$, or $\textbf{let}~p = e$ with $\text{diverges}(e)$, then $\text{tail}(s) = \bot$ and the sequence must end there. Programs with statements after a $\textbf{return}$ are rejected at type-checking time rather than silently dropped — the rejection surfaces a likely programmer error (writing past a return) and avoids the question of how to type-check unreachable code. The destructuring form $\textbf{let}~p = e$ with a divergent RHS is the [T-LetPat-Diverge](#T-LetPat-Diverge) carve-out — both single-binder and pattern-destructuring lets diverge symmetrically when their RHS does. The same $\text{tail}$ predicate used in [T-If](#T-If)/[T-Match](#T-Match) is reused here, so divergence handling stays uniform across the spec.

### Metatheoretic Properties

The type system commits to five soundness properties (P1–P5) plus the three local properties stated inline at their respective sections (P6 Exhaustiveness, [Pattern Matching](#pattern-matching); P7 Unification, §Unification; P8 No implicit generalization, §Polymorphism Introduction). The five global properties are:

$$\textbf{P1}~\text{(Progress)}.\quad \text{If}~\emptyset;\,\lbrace\rbrace;\,\bot \vdash_s s : \Gamma' \mathbin{!} \rho_e,~\text{then either:}$$

$$\quad\text{(a)}~s~\text{reduces to some}~s'~\text{by an operational step, or (b)}~s~\text{is a terminal form (value, terminating}~\textbf{return}, \text{escaping}~\textbf{raise}\text{).}$$

$$\textbf{P2}~\text{(Preservation)}.\quad \text{If}~\Gamma;\,\rho_q;\,\tau_r \vdash_s s : \Gamma' \mathbin{!} \rho_e~\text{and}~s \longrightarrow s',~\text{then}$$

$$\quad \Gamma;\,\rho_q;\,\tau_r \vdash_s s' : \Gamma'' \mathbin{!} \rho_e'~\text{with}~\Gamma''~\text{a refinement of}~\Gamma'~\text{and}~\rho_e' \subseteq \rho_e.$$

$$\textbf{P3}~\text{(Linear consumption)}.\quad \text{For any closing scope discharged by [P-FnEnd](#T-Lambda) (function body), [P-Block](#environment-and-usage)}$$

$$\quad \text{(}\textbf{inject}/\textbf{try}\text{), or [P-Loop](#T-While) (}\textbf{while}\text{), every linear binding introduced inside the scope is consumed exactly once before the scope closes.}$$

$$\textbf{P4}~\text{(Capability containment)}.\quad \text{For any well-typed function body typed under declared}~\rho_q,~\text{every [T-PortCall](#T-PortCall)}$$

$$\quad \text{and [T-App](#T-App) inside the body satisfies its respective}~\alpha \subseteq \rho_q~\text{premise.}$$

$$\textbf{P5}~\text{(Exception containment)}.\quad \text{For any well-typed function body typed under declared}~\rho_e,~\text{every [T-Raise-Ctor](#T-Raise-Ctor)}$$

$$\quad \text{/ [T-Raise-CtorNullary](#T-Raise-CtorNullary) / [T-Raise-Val](#T-Raise-Val) inside the body produces a row entry that is in}~\rho_e~\text{or subsumed by}~\texttt{Exn} \in \rho_e~\text{via [U-Row-Exn](#U-Row-Exn).}$$

P1 and P2 are stated relative to an operational semantics — the spec does not give small-step rules in this document; the reduction relation $\longrightarrow$ is defined narratively in [semantics.md](../semantics) and is the obligation of the runtime/codegen pipeline. The other three properties (P3–P5) are *structural*: every $\text{check}$ pass on a term derives them by induction over the relevant rules' premises, with [P-FnEnd](#T-Lambda)/[P-Block](#environment-and-usage)/[P-Loop](#T-While) discharging P3, the $\subseteq$ premises of T-App / T-PortCall discharging P4, and the row-entry constructions in T-Raise-* discharging P5. In this sense P3–P5 are *intrinsic* to the rules' shape — any conformant implementation that admits a rule's conclusion has already established the corresponding fragment of the property.

The numbering reserves P1–P5 for these global properties so the rule-local P6–P8 (which are convenient where they're stated, but not architectural) can stay in their natural sections without renumbering. A future revision may add P9, P10 etc.\ for new local properties.

---

## 3. Top-Level Declarations

A program is a sequence of top-level declarations followed by zero or more top-level $\textbf{let}$ bindings. Declarations populate the global tables — $\Gamma$ (term bindings), $\text{typedef}$ (named type schemes), $\text{variants}$ (sum-type constructor sets), $\text{methods}$ (port method signatures), and $\text{members}$ (exception-group expansion) — that the per-expression rules in §2 read as preconditions. §1 described these declarations as "not terms; preconditions on $\Gamma$"; the judgments in this section spell out exactly how the preconditions are produced.

We write $\mathcal{T} = \langle \Gamma,\, \text{typedef},\, \text{variants},\, \text{methods},\, \text{members} \rangle$ for the five-tuple of tables. The declaration judgment

$$\mathcal{T} \;\vdash_d\; \text{decl} \;\Rightarrow\; \mathcal{T}'$$

says that processing $\text{decl}$ against the current tables produces the updated tables $\mathcal{T}'$. Sequencing through a file folds the rules left-to-right; processing through imports updates the tables before the importing module's own declarations fire (see [imports.md](../imports) for module ordering).

In each rule below, components of $\mathcal{T}$ not mentioned in the conclusion are unchanged. All tables grow monotonically — declarations only extend; existing entries are never removed or rewritten.

**Two-phase processing for type declarations.** A naive left-to-right fold cannot type a self-referential `type Tree<T> = Leaf | Node(left: Tree<T>, …)` (Tree's field references Tree before Tree is in $\text{typedef}$) or a mutually-recursive `type Even = Zero | ESucc(odd: Odd); type Odd = OSucc(even: Even)` (Odd is forward-referenced by Even). The same hazard applies to recursive top-level $\textbf{let}$ functions (`let factorial = fn ... factorial(...) ... end`). To handle all of these uniformly, file processing runs a **forward-registration judgment** $\vdash_d^{\text{pre}}$ before the body-resolution judgment $\vdash_d$:

<a id="D-Type-Forward"></a>

$$\dfrac{
  D = \textbf{type}~x\langle \overline{\alpha} \rangle = \ldots~\text{(body unresolved)}
}{
  \mathcal{T} \;\vdash_d^{\text{pre}}\; D \;\Rightarrow\; \mathcal{T}[\text{typedef}(x) \mathrel{:=} \forall \overline{\alpha}.\,x\langle \overline{\alpha} \rangle]
} \;\textsc{D-Type-Forward}$$

<a id="D-Let-Forward"></a>

$$\dfrac{
  \begin{array}{l}
  D = \textbf{let}~x = \textbf{fn}~[\langle \overline{X} \rangle]\,(\overline{\ell:\tau}) \to \tau_r;\,\rho_q;\,\rho_e~\textbf{do}~\overline{s}~\textbf{end} \\[2pt]
  S_{\text{pre}} = \begin{cases} \forall \overline{X{:}\kappa}.\,(\overline{\ell:\tau}) \to \tau_r;\,\rho_q;\,\rho_e & \text{if}~\overline{X}~\text{non-empty} \\ \text{mono}((\overline{\ell:\tau}) \to \tau_r;\,\rho_q;\,\rho_e) & \text{otherwise} \end{cases}
  \end{array}
}{
  \mathcal{T} \;\vdash_d^{\text{pre}}\; D \;\Rightarrow\; \mathcal{T}[\Gamma \mathrel{:=} \Gamma,\, x :^{\omega} S_{\text{pre}}]
} \;\textsc{D-Let-Forward}$$

D-Type-Forward and D-Let-Forward are the only $\vdash_d^{\text{pre}}$ rules; every other declaration form ($\textbf{port}$, $\textbf{exception}$, $\textbf{exception group}$, $\textbf{external}$, top-level $\textbf{let}$ whose RHS is *not* a $\textbf{fn}$ literal, destructuring $\textbf{let}~p = e$) is a no-op under $\vdash_d^{\text{pre}}$ — they introduce no forward-referenceable name. File-level processing is then the composition

$$\text{processFile}(\overline{D}) \;=\; (\text{fold}_{\vdash_d}\; \overline{D}) \;\circ\; (\text{fold}_{\vdash_d^{\text{pre}}}\; \overline{D})$$

with both folds running left-to-right over the same declaration sequence. After the pre-pass, every type name is in $\text{typedef}$ as a placeholder and every recursive $\textbf{fn}$ is in $\Gamma$ at its declared signature; the body-pass D-Type-Record / D-Type-Sum / D-Type-Sum-Opaque / D-Let-Top / D-LetPat-Top rules then run with the recursive references already resolvable through the pre-pass tables. Conflicts where the body-pass needs a resolved variant set against a still-placeholder name (e.g.\ [Exh-Sum](#Exh-Sum) inside a top-level $\textbf{let}$ whose body matches against a sum that is declared later) are well-typed because the body-pass runs to completion *before* per-expression typing inside top-level $\textbf{let}$ bodies fires the [Exh-Sum](#Exh-Sum) lookups.

The implementation realises this in `src/typecheck/check.nx`'s declaration-walk + `infer.nx::infer_let`'s "Pre-register for recursive lambdas" path; the spec's two-pass shape is the metatheoretic counterpart.

<a id="D-Type-Record"></a>

$$\dfrac{
  D = \textbf{type}~x\langle \overline{\alpha} \rangle = \lbrace \overline{\ell : \tau} \rbrace
}{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}[\text{typedef}(x) \mathrel{:=} \forall \overline{\alpha}.\, \lbrace \overline{\ell : \tau} \rbrace]
} \;\textsc{D-Type-Record}$$

<a id="D-Type-Sum"></a>

$$\dfrac{
  \begin{array}{l}
  D = \textbf{type}~x\langle \overline{\alpha} \rangle = c_1\,\overline{F_1} \mathbin{\vert} \ldots \mathbin{\vert} c_n\,\overline{F_n} \quad\text{where each}~\overline{F_i}~\text{is either}~(\overline{\ell_i : \tau_i})~\text{or empty} \\[2pt]
  S_i = \begin{cases} \forall \overline{\alpha}.\,(\overline{\ell_i : \tau_i}) \to x\langle \overline{\alpha} \rangle & \text{if}~\overline{F_i}~\text{is non-empty (arity} \geq 1\text{)} \\ \forall \overline{\alpha}.\, x\langle \overline{\alpha} \rangle & \text{if}~\overline{F_i}~\text{is empty (nullary)} \end{cases}
  \end{array}
}{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}\!\begin{bmatrix} \Gamma & \mathrel{:=} & \Gamma,\, \overline{c_i :^{\omega} S_i} \\ \text{typedef}(x) & \mathrel{:=} & \forall \overline{\alpha}.\, x\langle \overline{\alpha} \rangle \\ \text{variants}(x) & \mathrel{:=} & \lbrace c_1, \ldots, c_n \rbrace \end{bmatrix}
} \;\textsc{D-Type-Sum}$$

D-Type-Sum simultaneously installs each constructor $c_i$ as an $\omega$-bound polymorphic entry in $\Gamma$: an arrow type when the constructor has fields, a *value-typed* scheme when it is nullary (e.g.\ $\texttt{None}$ in $\textbf{type}~\texttt{Option}\langle T \rangle = \texttt{None} \mathbin{\vert} \texttt{Some}(\textit{val}: T)$ is bound at $\forall T.\, \texttt{Option}\langle T \rangle$, not at $\forall T.\, () \to \texttt{Option}\langle T \rangle$). The value-typed form is what lets the surface form $\texttt{None}$ (no parentheses) type-check as an expression via [T-Var](#T-Var) and as a pattern via [P-CtorNullary](#P-CtorNullary). $x$ is registered in $\text{typedef}$, and the variant set is recorded so that [Exh-Sum](#Exh-Sum) and [P-Ctor](#P-Ctor) / [P-CtorNullary](#P-CtorNullary) can read constructors by name.

<a id="D-Type-Sum-Opaque"></a>

$$\dfrac{
  \begin{array}{l}
  D = \textbf{opaque type}~x\langle \overline{\alpha} \rangle = c_1(\overline{\ell_1 : \tau_1}) \mathbin{\vert} \ldots \mathbin{\vert} c_n(\overline{\ell_n : \tau_n}) \\[2pt]
  S_i = \forall \overline{\alpha}.\,(\overline{\ell_i : \tau_i}) \to x\langle \overline{\alpha} \rangle \quad (i = 1, \ldots, n) \\[2pt]
  M~\text{is the defining module}
  \end{array}
}{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}\!\begin{bmatrix} \Gamma & \mathrel{:=} & \Gamma,\, \overline{c_i :^{\omega} S_i}~\text{(only when typing inside}~M\text{)} \\ \text{typedef}(x) & \mathrel{:=} & \forall \overline{\alpha}.\, x\langle \overline{\alpha} \rangle \\ \text{variants}(x) & \mathrel{:=} & \lbrace c_1, \ldots, c_n \rbrace~\text{(only when typing inside}~M\text{)} \end{bmatrix}
} \;\textsc{D-Type-Sum-Opaque}$$

D-Type-Sum-Opaque restricts the visibility of the constructor entries and the $\text{variants}$ set to the *defining module* $M$: outside $M$, $x$ is in $\text{typedef}$ as an abstract named type (which can be referenced in signatures) but $\overline{c_i}$ are absent from $\Gamma$ and $\text{variants}(x)$ reports the empty set. Importing code therefore cannot apply $c_i$ as a constructor ([T-App](#T-App) looks $c_i$ up in $\Gamma$ and fails) or write a $c_i(\overline{\ell : p})$ pattern ([P-Ctor](#P-Ctor) also fails the lookup); construction and destructuring are only possible through the module's exported functions. The opaque modifier is accepted only on sum-type definitions in the surface grammar; record types and aliases have no opaque variant (`src/frontend/parse_topdef.nx::parse_type_def` reads `is_opaque` only for the enum branch).

<a id="D-External"></a>

$$\dfrac{
  \begin{array}{l}
  D = \textbf{external}~x = \texttt{"} w \texttt{"} : \langle \overline{\alpha} \rangle (\overline{\ell : \tau}) \to \tau_r \\[2pt]
  S = \forall \overline{\alpha}.\,(\overline{\ell : \tau}) \to \tau_r;\,\lbrace\rbrace;\,\lbrace\rbrace \quad\text{(empty require / throws)}
  \end{array}
}{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}[\Gamma \mathrel{:=} \Gamma,\, x :^{\omega} S]
} \;\textsc{D-External}$$

External declarations bind a name $x$ to a fixed Wasm export $w$ at a stated arrow type. The type-parameter list $\langle \overline{\alpha} \rangle$ may be empty (monomorphic external) or non-empty (polymorphic in the same predicative System-F sense as [T-Let-PolyFn](#T-Let-PolyFn)): the parser accepts both forms (`parse_external_sig`'s `type_params` field). The require and throw rows are forced to empty because the Wasm side has no Nexus-level effects to track; capability access through an external is mediated by the surrounding `inject` if the external takes capability-shaped parameters. The mapping between $x$ and the Wasm symbol $w$ is consumed by the backend codegen — the type system observes only $S$.

<a id="D-Port"></a>

$$\dfrac{
  \begin{array}{l}
  D = \textbf{port}~X~\textbf{do}~\overline{\textbf{fn}~\ell_j(\overline{\pi_j}) \to \kappa_j;\,\alpha_j;\,\beta_j}~\textbf{end} \\[2pt]
  \forall j \in J.\;\text{wfCap}(\alpha_j) \wedge \text{wfThrow}(\beta_j) \quad\text{(per-method declared rows reference known caps / variants)}
  \end{array}
}{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}[\text{methods}(X) \mathrel{:=} \lbrace \ell_j : (\overline{\pi_j}) \to \kappa_j;\,\alpha_j;\,\beta_j \mid j \in J \rbrace]
} \;\textsc{D-Port}$$

Port declarations populate $\text{methods}$ alone; they do not enter a value-level binding in $\Gamma$ for $X$. $X$ becomes available as a row-entry symbol in $\rho_q$ via the *user-declared port names* source described in §Row Types, and as a method-lookup namespace via [T-PortCall](#T-PortCall).

<a id="D-Exception"></a>

$$\dfrac{
  D = \textbf{exception}~C\,\overline{F} \qquad
  S = \begin{cases} (\overline{\ell : \tau}) \to \texttt{Exn} & \text{if}~\overline{F} = (\overline{\ell : \tau}),~\text{non-empty} \\ \texttt{Exn} & \text{if}~\overline{F}~\text{is omitted (nullary)} \end{cases}
}{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}\!\begin{bmatrix} \Gamma & \mathrel{:=} & \Gamma,\, C :^{\omega} S \\ \text{variants}(\texttt{Exn}) & \mathrel{:=} & \text{variants}(\texttt{Exn}) \cup \lbrace C \rbrace \end{bmatrix}
} \;\textsc{D-Exception}$$

Exception declarations admit both the parameterised form $\textbf{exception}~\texttt{NotFound}(\textit{path}: \texttt{string})$ — installed as an arrow constructor — and the nullary form $\textbf{exception}~\texttt{MissingMain}$ (no parentheses on declaration or use) — installed as a value of type $\texttt{Exn}$, matching the *"Zero-field exceptions omit parentheses"* convention from [Exception Groups](../exception-groups). The nullary form is the unique reason [P-CtorNullary](#P-CtorNullary) exists; the parameterised form goes through ordinary [P-Ctor](#P-Ctor).

Exception declarations are the only rule that mutates a *pre-existing* table entry: $\text{variants}(\texttt{Exn})$ is the union of every $\textbf{exception}$ declaration reached from the program root. The *cross-module extensibility hazard* called out in [T-TryCatch](#T-TryCatch) — a closed-enumeration catch over a $\texttt{Exn}$ row becoming inexhaustive when a downstream module adds a variant — is exactly the cross-module application of D-Exception against the importer's $\text{variants}(\texttt{Exn})$.

<a id="D-ExceptionGroup"></a>

$$\dfrac{
  D = \textbf{exception group}~G = C_1 \mathbin{\vert} \ldots \mathbin{\vert} C_n
}{
  \mathcal{T} \;\vdash_d\; D \;\Rightarrow\; \mathcal{T}[\text{members}(G) \mathrel{:=} \lbrace C_1, \ldots, C_n \rbrace]
} \;\textsc{D-ExceptionGroup}$$

Group declarations affect only the parse-time expansion table $\text{members}$. No typing rule reads $\text{members}$ directly — the parser uses it to fan out $\textbf{catch}~\vert~G \to \ldots$ into one arm per constructor before the rule fires.

<a id="D-Let-Top"></a>

$$\dfrac{
  \Gamma;\,\lbrace\rbrace;\,\bot \;\vdash_s\; \textbf{let}~\mu\,x = e \;:\; \Gamma' \mathbin{!} \lbrace\rbrace
}{
  \mathcal{T} \;\vdash_d\; \textbf{let}~\mu\,x = e \;\Rightarrow\; \mathcal{T}[\Gamma \mathrel{:=} \Gamma']
} \;\textsc{D-Let-Top}$$

<a id="D-LetPat-Top"></a>

$$\dfrac{
  \Gamma;\,\lbrace\rbrace;\,\bot \;\vdash_s\; \textbf{let}~p = e \;:\; \Gamma' \mathbin{!} \lbrace\rbrace
}{
  \mathcal{T} \;\vdash_d\; \textbf{let}~p = e \;\Rightarrow\; \mathcal{T}[\Gamma \mathrel{:=} \Gamma']
} \;\textsc{D-LetPat-Top}$$

A top-level $\textbf{let}$ is type-checked as an ordinary statement under an empty ambient capability row, an empty effect row, and a $\bot$ return-type (no enclosing function): D-Let-Top reuses [T-Let](#T-Let), [T-Let-PolyFn](#T-Let-PolyFn), or [T-Let-Alias](#T-Let-Alias) according to the RHS shape; D-LetPat-Top covers destructuring binders by reusing [T-LetPat](#T-LetPat) (or [T-LetPat-Diverge](#T-LetPat-Diverge) when the RHS is a $\textbf{raise}$). The pure-row premise rejects top-level expressions that require capabilities the program root cannot grant; an $\textbf{inject}$ at the top level is the recommended way to introduce capabilities for an evaluating block.

Self-recursive (`let factorial = fn ... factorial(n: n - 1) ... end`) and mutually-recursive top-level functions are handled by the unified two-phase scheme stated at the top of this section: [D-Let-Forward](#D-Let-Forward) seeds $\Gamma$ with each `let x = fn ...`'s declared signature scheme during the $\vdash_d^{\text{pre}}$ pre-pass; D-Let-Top / D-LetPat-Top then run with that environment, so a self-call $x(\ldots)$ or mutual call $g(\ldots)$ inside $f$'s body resolves through [T-Var](#T-Var). `let x = e` whose RHS is *not* a $\textbf{fn}$ literal (data binding, computed value) does not participate in $\vdash_d^{\text{pre}}$ and cannot be self-referential through the top-level `let` channel — recursive data constructors go through [D-Type-Sum](#D-Type-Sum)'s forward registration instead.

### Visibility (export)

Every declaration above admits an optional `export` prefix in the surface syntax (`export let foo = ...`, `export type Foo = ...`, etc.). The modifier does *not* alter the rule's effect on $\mathcal{T}$ within the declaring module — `export` and non-`export` declarations populate $\Gamma$ / $\text{typedef}$ / $\text{methods}$ / $\text{variants}$ / $\text{members}$ identically *inside* their module. The modifier governs **inter-module visibility**: only `export`ed entries enter the importing module's $\mathcal{T}$ when an `import` statement is resolved. Import resolution is described in [imports.md](../imports) and runs before the per-module declaration judgments above fire; the spec does not need a separate rule for `export` because it produces no new constraint on a single-module derivation.

D-Type-Sum-Opaque is the one place where module identity directly enters a typing rule: the constructor visibility depends on whether the typing-time module is the defining module $M$. All other rules are module-local in the trivial sense (their effects apply inside whichever module is being type-checked).

### Program Entry Point

A complete program is a (possibly multi-file) declaration sequence whose root module declares a top-level binding named $\textit{main}$. The entry point carries four constraints not enforced by the per-declaration rules above:

$$\textbf{P9}~\text{(Main well-formedness)}.\quad \text{wfMain}(\mathcal{T}) \;\Longleftrightarrow\;$$

$$\quad \exists~\textit{main} \in \text{dom}(\Gamma).\;\Gamma(\textit{main}) = (\omega,\, \text{mono}((\,) \to \texttt{unit};\,\rho_q;\,\lbrace\rbrace)) \;\wedge\; \rho_q \subseteq \texttt{SysCaps} \;\wedge\; \textit{main} \notin \text{exports}(\mathcal{T})$$

The four conjuncts encode the constraints stated narratively in [semantics.md](../semantics) §Entrypoint and [effects.md](../effects) §Main Constraints:

- **Signature** — $(\,) \to \texttt{unit}$ with no arguments and a $\texttt{unit}$ return.
- **Empty throws row** — `main`'s declared $\rho_e$ is $\lbrace\rbrace$. Every exception that the program may raise must be handled by an inner $\textbf{try}$ before propagating out of `main`; the runtime has no exception consumer outside of `main`.
- **Require subset of SysCaps** — `main` may declare any subset of system capabilities ($\texttt{PermFs}$, $\texttt{PermNet}$, etc.) which the runtime grants from the WASI environment. User-declared port names may **not** appear in `main`'s $\rho_q$ — there is no enclosing $\textbf{inject}$ to provide them.
- **Non-exported** — `main` is not in $\text{exports}(\mathcal{T})$. Other modules cannot import `main`; it is a runtime-side hook, not part of any module's API.

A program is **well-formed** iff $\text{wfMain}(\mathcal{T})$ holds for the root module's resolved $\mathcal{T}$. If the property fails — `main` is missing, has the wrong signature, declares a non-empty throws row, requires a non-system capability, or is exported — the type-checker rejects the program at the program-entry check after the per-module folds complete. This is the only program-global property in §3; every other rule and property is module-local.

{% endraw %}
