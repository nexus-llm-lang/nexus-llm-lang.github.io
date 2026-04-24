{
  inputs = {
    nixpkgs.url = "https://flakehub.com/f/NixOS/nixpkgs/*";
    flake-utils.url = "github:numtide/flake-utils";
    tree-sitter-grammar = {
      url = "github:nexus-llm-lang/tree-sitter-grammar";
      inputs.nixpkgs.follows = "nixpkgs";
      inputs.flake-utils.follows = "flake-utils";
    };
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
      tree-sitter-grammar,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};
        formatter = pkgs.nixfmt-tree;
      in
      {
        devShells.default = pkgs.mkShellNoCC {
          packages =
            with pkgs;
            [
              tree-sitter
              actionlint
              formatter
            ]
            ++ (with pkgs.rubyPackages; [
              pkgs.ruby
              jekyll
              jekyll-theme-slate
              jekyll-seo-tag
              kramdown-parser-gfm
            ]);
          shellHook = ''
            _grammar_dir="$(mktemp -d -t nexus-docs-parsers-XXXXXX)"
            ln -sfn "${tree-sitter-grammar}" "$_grammar_dir/tree-sitter-nexus"
            mkdir -p "$HOME/.config/tree-sitter"
            cat > "$HOME/.config/tree-sitter/config.json" <<EOF
            { "parser-directories": ["$_grammar_dir"] }
            EOF
            unset _grammar_dir
          '';
        };

        legacyPackages = pkgs;
        inherit formatter;
      }
    );
}
