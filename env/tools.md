---
layout: default
title: Tools
---

# Tools

## Language server (LSP)

Nexus ships a built-in LSP server. The server hooks into editors and supports script-driven analysis.

### Usage

```bash
nexus lsp          # start LSP server (stdio)
```

Point your editor at `nexus lsp` as the LSP server for `.nx` files.

### Capabilities

| Feature | Description |
|---|---|
| Diagnostics | Parse errors, type errors, and warnings published on open/change |
| Hover | Type information for variables, functions, type definitions, enums |
| Go to Definition | Jump to the definition site of a symbol (same file) |
| Document Symbols | Outline of functions, types, enums, caps, exceptions |
| References | Find all occurrences of an identifier |
| Rename | Rename an identifier across the file |
| Completion | Keywords, symbols from the type environment, module members |

### CLI Diagnostics (LLM-friendly)

For non-interactive use — CI pipelines, LLM tool calls, scripts — `nexus check --format json` writes structured diagnostics to stdout:

```bash
nexus check --format json program.nx
```

The output has `file`, `ok` (bool), `diagnostics` (range, severity, message), and `symbols` (name, kind, range). The exit code is `0` on success and `1` on errors.

### Editor Setup Examples

**Neovim (nvim-lspconfig)**

```lua
vim.api.nvim_create_autocmd('FileType', {
  pattern = 'nexus',
  callback = function()
    vim.lsp.start({
      name = 'nexus',
      cmd = { 'nexus', 'lsp' },
      root_dir = vim.fs.root(0, '.git'),
    })
  end,
})
```

**VS Code (settings.json)**

Use a generic LSP client extension (such as [vscode-languageclient](https://github.com/AstroNvim/astrolsp)) and point it at `nexus lsp` as the server for `.nx` files.

**Helix (languages.toml)**

```toml
[[language]]
name = "nexus"
scope = "source.nexus"
file-types = ["nx"]
language-servers = ["nexus-lsp"]

[language-server.nexus-lsp]
command = "nexus"
args = ["lsp"]
```

---

## AI coding agent skill

Nexus is built for LLMs to write. To help coding agents land correct Nexus code, this repo ships a [Claude Code skill](https://docs.anthropic.com/en/docs/claude-code/skills) with the full language reference.

### Installation

```bash
npx skills add nexus-llm-lang/Nexus --skill nexus-lang
```

Claude Code activates the skill as soon as it touches a `.nx` file.

### Contents

| File | Description |
|---|---|
| `SKILL.md` | Quick reference: syntax rules, effect system, type summary, anti-patterns |
| `references/syntax.md` | Complete EBNF grammar and operator precedence |
| `references/types.md` | Type system: primitives, records, ADTs, linear types, borrowing, mutability |
| `references/effects.md` | Caps, handlers, inject, runtime permissions, checked exceptions |
| `references/stdlib.md` | Full standard library API (all modules and function signatures) |
| `references/patterns.md` | Idiomatic code patterns: list recursion, error handling, concurrency, web servers |
| `templates/*.nx` | Starter templates for hello-world, web server, CLI app, cap/handler DI |

### What the skill teaches agents

- **Labeled arguments** — every call site uses `f(param: value)`; positional forms are out.
- **Block delimiters** — `do ... end` and `then ... else ... end`; braces are out.
- **Linear types** (`%`) — used once, compiler-enforced
- **Borrowing** (`&`) — immutable views without consume
- **Cap system** — `cap` → `handler` → `inject` → `require` flow
- **Runtime perms** — `PermConsole`, `PermFs`, `PermNet`, and the rest
- **Stdlib** — correct import forms and function signatures

### Other agents

The skill is a set of Markdown files. Agents that lack Claude Code skill support can read the files straight from `skills/nexus-lang/`.

LLM agents can also call `nexus check --format json` as a tool. They get structured diagnostics without installing the skill.
