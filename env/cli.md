---
layout: default
title: CLI
---

# CLI

## Global Flags

| Flag | Description |
|---|---|
| `--verbose` / `-v` | Enable structured timing output to stderr |

## Commands

### `nexus run FILE`

Compile a Nexus source file and immediately execute it via wasmtime. Arguments after `--` are forwarded verbatim to the running program.

```bash
nexus run program.nx
nexus run program.nx -- arg1 arg2
```

Sandbox flags constrain the execution environment for reproducibility:

| Flag | Effect |
|---|---|
| `--seed N` | Fix the RNG seed for deterministic random output |
| `--frozen-clock[=EPOCH]` | Pin wall/mono clock to EPOCH (default 0) |
| `--max-time MS` | Abort the program after MS milliseconds |
| `--max-mem MB` | Cap wasm linear memory at MB MiB |
| `--no-net` / `--no-fs` / `--no-clock` / `--no-rand` | Strip the named capability (refuses if the program requires it) |
| `--tmp-fs DIR` | Rebind the `Fs` root to a scratch directory |
| `--record FILE` | Record the invocation as a JSONL session |
| `--replay FILE` | Replay a recorded session and assert byte-equivalence |

### `nexus build FILE`

Compile to a WASM component:

```bash
nexus build program.nx                  # outputs main.wasm
nexus build program.nx -o output.wasm   # custom output path
```

Requires `wasm-merge` for dependency bundling. Configure via:
- `--wasm-merge PATH` flag
- `NEXUS_WASM_MERGE` environment variable

Resolution order: `--wasm-merge` > `NEXUS_WASM_MERGE` > `wasm-merge` from `PATH`.

Inspect declared capabilities:

```bash
nexus build program.nx --explain-capabilities           # list capability names (default)
nexus build program.nx --explain-capabilities=none      # suppress capability output
nexus build program.nx --explain-capabilities=wasmtime  # show wasmtime run command
```

Output format:

```bash
nexus build program.nx --explain-capabilities-format=text  # human-readable (default)
nexus build program.nx --explain-capabilities-format=json  # machine-readable JSON
```

Run the built component:

```bash
wasmtime run -Scli main.wasm
wasmtime run -Scli -Shttp -Sinherit-network -Sallow-ip-name-lookup -Stcp main.wasm
```

### `nexus typecheck FILE`

Parse and typecheck only. No execution, no WASM output.

```bash
nexus typecheck program.nx
```

Structured JSON output for CI, scripting, and LLM tool use:

```bash
nexus typecheck --format json program.nx
```

```json
{
  "file": "program.nx",
  "ok": false,
  "diagnostics": [
    {
      "range": {
        "start": { "line": 5, "character": 9 },
        "end": { "line": 5, "character": 16 }
      },
      "severity": "error",
      "message": "Mismatch: string vs i64"
    }
  ],
  "symbols": [
    {
      "name": "main",
      "kind": "function",
      "range": {
        "start": { "line": 0, "character": 0 },
        "end": { "line": 10, "character": 3 }
      }
    }
  ]
}
```

Exit code is `0` on success, `1` if any errors are present. Warnings alone do not cause failure.

### `nexus lsp`

Start the Language Server Protocol server over stdio. Connect from any LSP-compatible editor (VS Code, Neovim, Emacs, Helix, etc.).

```bash
nexus lsp
```

Supported LSP features:

| Feature | Method | Description |
|---|---|---|
| Diagnostics | `publishDiagnostics` | Parse errors, type errors, warnings on open/change |
| Hover | `textDocument/hover` | Type info for variables, functions, types, enums |
| Go to Definition | `textDocument/definition` | Jump to definition (same file) |
| Document Symbols | `textDocument/documentSymbol` | List functions, types, enums, caps, exceptions |
| References | `textDocument/references` | Find all occurrences of an identifier |
| Rename | `textDocument/rename` | Rename an identifier across the file |
| Completion | `textDocument/completion` | Keywords, env symbols, module members |

Project root is detected by walking up from the file to the nearest `.git` directory.

### `nexus repl`

Launch an interactive session:

```bash
nexus repl
```

Each input line is parsed, typechecked, and evaluated against a persistent session; bindings established at one prompt are visible at the next. Press Ctrl-D to exit.

## Capabilities

Capabilities are **declared in source** via `require { ... }`, not passed on the command line. The compiler embeds the required set into the binary's `nexus:capabilities` custom section. `nexus run` reads that section and forwards the matching `wasmtime` flags for the program — no opt-in flag list is needed.

To inspect what a program requires:

```bash
nexus build program.nx --explain-capabilities           # list capability names
nexus build program.nx --explain-capabilities=wasmtime  # show wasmtime run command
nexus build program.nx --explain-capabilities=none      # suppress capability output
```

To *strip* capabilities at run time (the run aborts if the program declared one of the stripped caps):

| Flag | Effect |
|---|---|
| `--no-fs` | Refuse `Fs` |
| `--no-net` | Refuse `Net` |
| `--no-clock` | Refuse `Clock` |
| `--no-rand` | Refuse `Random` |

See [WASM and WASI](../wasm) for the per-capability WASI mapping.
