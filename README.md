# nexus-llm-lang.github.io

Documentation site for [Nexus](https://github.com/nexus-llm-lang/Nexus).

Published at **https://nexus-llm-lang.github.io/**.

## Local development

```sh
nix develop
jekyll serve --source . --config _config.yml --baseurl /latest
```

The devshell provisions Jekyll, Ruby, and the Nexus tree-sitter grammar
(via a flake input). Entering the shell writes `~/.config/tree-sitter/config.json`
so `_plugins/nexus_highlight.rb` can resolve the `nexus` language.

## Layout

- `_config.yml`, `_layouts/`, `_includes/` — Jekyll theme configuration
- `_plugins/nexus_highlight.rb` — tree-sitter-based syntax highlighter for
  `nexus` code blocks
- `spec/`, `env/`, `design.md`, `refactor_baseline.md` — documentation content

## Deployment

`.github/workflows/deploy.yml` builds versioned + latest sites on `v*` tag
push or manual dispatch and publishes to GitHub Pages.
