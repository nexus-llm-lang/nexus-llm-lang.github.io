---
layout: default
title: CLI
---

# CLI

## Global Flags

| Flag | Description |
|---|---|
| `--verbose` | Enable structured timing output to stderr |

## Commands

### Running a program

There is no `nexus run` subcommand. Compile with `nexus build`, then run the produced WASM directly under `wasmtime`:

```bash
nexus build program.nx -o out.wasm
wasmtime run -S threads --dir=. out.wasm
```

Determinism hooks are environment variables read at runtime, passed through wasmtime's `--env`:

| Env var | Effect |
|---|---|
| `NEXUS_SEED=N` | Fix the RNG seed for deterministic random output |
| `NEXUS_FROZEN_CLOCK=EPOCH_MS` | Pin wall/mono clock to EPOCH (in milliseconds) |

```bash
wasmtime run --env NEXUS_SEED=1 --env NEXUS_FROZEN_CLOCK=0 -S threads --dir=. out.wasm
```

### `nexus build FILE`

Compile to a WASM component:

```bash
nexus build program.nx                  # outputs out.wasm
nexus build program.nx -o output.wasm   # custom output path
```

Build bundles deps automatically; `wasm-merge` just needs to be on the `PATH`.

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
wasmtime run -Scli out.wasm
wasmtime run -Scli -Shttp -Sinherit-network -Sallow-ip-name-lookup -Stcp out.wasm
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

### LSP server

The LSP server is a separate binary, `lsp.wasm`, built by `./bootstrap.sh` (Stage L). It is not a `nexus` subcommand. Run it over stdio under wasmtime; any LSP-aware editor can connect: VS Code, Neovim, Emacs, Helix, and so on.

```bash
wasmtime run -Scli lsp.wasm
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

Caps are **declared in source** with `require { ... }`. They never come from the command line. Inspect what a program requires with `nexus caps` or at build time:

```bash
nexus caps main program.nx                              # caps required by a symbol
nexus build program.nx --explain-capabilities           # list capability names
nexus build program.nx --explain-capabilities=wasmtime  # show wasmtime run command
nexus build program.nx --explain-capabilities=none      # suppress capability output
```

Most caps (`Console`, `Random`, `Clock`, `Proc`, `Env`) are static, compile-time checks only. At run time, only `Fs` and `Net` are enforced through wasmtime flags: `--dir .` grants `Fs`, `--wasi inherit-network` grants `Net`. Omit the flag to deny the capability.

See [WASM and WASI](../wasm) for the per-cap WASI mapping.
