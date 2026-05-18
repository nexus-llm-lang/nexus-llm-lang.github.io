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

Compile a Nexus source file and run it on wasmtime. Args after `--` are passed straight through to the program.

```bash
nexus run program.nx
nexus run program.nx -- arg1 arg2
```

Sandbox flags pin the run environment so the result is reproducible:

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

Build needs `wasm-merge` to bundle deps. Set it via:
- `--wasm-merge PATH` flag
- `NEXUS_WASM_MERGE` env var

Lookup order: `--wasm-merge` first, then `NEXUS_WASM_MERGE`, then `wasm-merge` on the `PATH`.

Inspect declared caps:

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

Parse and typecheck only. No run, no WASM output.

```bash
nexus typecheck program.nx
```

Structured JSON output for CI, scripts, and LLM tool use:

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

The exit code is `0` on success and `1` if any error shows up. A warning alone does not fail the run.

### `nexus lsp`

Start the LSP server over stdio. Any LSP-aware editor can connect: VS Code, Neovim, Emacs, Helix, and so on.

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

The server walks up from the file to the nearest `.git` directory and uses that as the project root.

### `nexus repl`

Launch an interactive session:

```bash
nexus repl
```

Each input line is parsed, typechecked, and run against a persistent session. A binding made at one prompt is visible at the next. Press Ctrl-D to exit.

## Capabilities

Caps are **declared in source** with `require { ... }`. They never come from the command line. The compiler embeds the required set into the binary's `nexus:capabilities` custom section, and `nexus run` reads that section. The runner then forwards the matching `wasmtime` flags for the program. There's no opt-in flag list to maintain.

To inspect what a program requires:

```bash
nexus build program.nx --explain-capabilities           # list capability names
nexus build program.nx --explain-capabilities=wasmtime  # show wasmtime run command
nexus build program.nx --explain-capabilities=none      # suppress capability output
```

To *strip* caps at run time (the run aborts if the program declared one of the stripped caps):

| Flag | Effect |
|---|---|
| `--no-fs` | Refuse `Fs` |
| `--no-net` | Refuse `Net` |
| `--no-clock` | Refuse `Clock` |
| `--no-rand` | Refuse `Random` |

See [WASM and WASI](../wasm) for the per-cap WASI mapping.
