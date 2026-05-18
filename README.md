# nexus-llm-lang.github.io

Documentation site for [Nexus](https://github.com/nexus-llm-lang/Nexus).

Published at **https://nexus-llm-lang.github.io/**.

## Local development

```sh
nix develop
jekyll serve --source . --config _config.yml --baseurl /latest
```

A flake input pulls in Jekyll, Ruby, and the Nexus tree-sitter grammar
for the dev shell. When the shell starts, it writes a config file at
`~/.config/tree-sitter/config.json` so the `_plugins/nexus_highlight.rb`
plugin can find the `nexus` lang.

## Layout

- `_config.yml`, `_layouts/`, `_includes/` — Jekyll theme bits
- `_plugins/nexus_highlight.rb` — tree-sitter highlighter for `nexus`
  code blocks
- `spec/`, `env/`, `design.md`, `refactor_baseline.md` — site docs

## Deployment

On a `v*` tag push or a manual run, `.github/workflows/deploy.yml` builds
both the versioned and latest sites, then ships them to GitHub Pages.
