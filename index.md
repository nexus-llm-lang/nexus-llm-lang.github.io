---
layout: default
title: Nexus
---

<p class="hero-tagline">
<strong>Nexus</strong> is a language built on one bet: <strong>LLMs are good at code you can read on the page, and bad at code that depends on what's off the page.</strong>
GC, implicit casts, ambient I/O, hidden control flow — these are the spots where LLM-written code goes wrong, and where humans miss it on review. Nexus swaps each one for a form you can see in the source.
</p>

<div class="code-showcase code-showcase-top" markdown="1">
<div class="code-card" markdown="1">

### Capabilities -- Hello world

Each function says what caps it needs. You inject the caps with handlers at the call site.

```nexus
import { Console }, * as stdio from "std:stdio"

let main = fn () -> unit require { PermConsole } do
  inject stdio.system_handler do
    Console.println(val: "Hello, Nexus!")
  end
end
```

</div>
</div>

<div class="code-showcase" markdown="1">
<div class="code-card" markdown="1">

### Linear Types

Use each resource once, then it's gone. No GC. The compiler tracks every cell.

```nexus
let %h = Fs.open_read(path: "data.txt")
let %r = Fs.read(handle: %h)
match %r do
  | { content: text, handle: %h2 } ->
        Fs.close(handle: %h2)
end
```

</div>
<div class="code-card" markdown="1">

### Lazy and Parallel

A thunk waits to run. When two thunks don't depend on each other, the runtime fires them in parallel. Linear types keep each one to a single shot.

```nexus
let @a = compute_a()
let @b = compute_b()
// evaluate parallely
let result = @{ a, b }
```

</div>
</div>

## Quick Start

```bash
nexus                   # REPL
nexus run example.nx    # interpret
nexus build example.nx  # compile to main.wasm
nexus check example.nx  # typecheck only
```

---

<div class="doc-nav">
  <div class="doc-section">
    <h4>Design</h4>
    <ul>
      <li><a href="design">Design Thesis</a> — Why every construct is literal</li>
    </ul>
    <h4>Language Specification</h4>
    <ul>
      <li><a href="spec/syntax">Syntax</a> — Grammar and EBNF</li>
      <li><a href="spec/types">Types</a> — Type system, linear types, borrowing</li>
      <li><a href="spec/effects">Effects and Capabilities</a> — Caps, handlers, inject</li>
      <li><a href="spec/exception-groups">Exception Groups</a> — Structured exceptions, multi-arm catch</li>
      <li><a href="spec/lazy">Lazy, Concurrency, Parallelism</a> — <code>@</code> sigil, DAG parallel evaluation, linearity</li>
      <li><a href="spec/semantics">Semantics</a> — Evaluation model</li>
    </ul>
  </div>
  <div class="doc-section">
    <h4>Environment</h4>
    <ul>
      <li><a href="env/cli">CLI</a> — Command-line interface</li>
      <li><a href="env/wasm">WASM and WASI</a> — Capability mapping and ABI</li>
      <li><a href="env/ffi">FFI</a> — Wasm interop</li>
      <li><a href="env/stdlib">Standard Library</a> — Builtin modules</li>
      <li><a href="env/tools">Tools</a> — AI coding agent skill</li>
    </ul>
  </div>
</div>
