{
  description = "kitcat — experimental univalent mathematics in Cubical Agda";

  inputs = {
    nixpkgs.url = "github:nixos/nixpkgs/nixpkgs-unstable";
    flake-utils.url = "github:numtide/flake-utils";
  };

  outputs =
    {
      self,
      nixpkgs,
      flake-utils,
    }:
    flake-utils.lib.eachDefaultSystem (
      system:
      let
        pkgs = nixpkgs.legacyPackages.${system};

        # The Agda toolchain. Dependencies are Agda builtins only — no
        # agda-stdlib, no cubical library — so bare agda (the latest
        # stable release nixpkgs-unstable tracks) is the whole toolchain.
        # This is the kernel `just check` runs against; pinning it here
        # is what makes a Gloss.* certificate's `@ <commit>` reproducible
        # across execution environments.
        agda = pkgs.agda;

        # Tools the agentic context layer relies on: source ingestion
        # (arXiv LaTeX / PDF → greppable text for resources/), doc
        # rendering, the bin/ scripts (GNU sed, ripgrep, fd), and the
        # recipe runner.
        contextTools = with pkgs; [
          just
          ripgrep
          fd
          gnused
          gnugrep
          coreutils
          findutils
          gitMinimal # bin/lint, bin/mmv, and the ingest path shell out to git
          curl # direct arXiv e-print/abs fetch (the R12 acquisition path)
          gnutar # extract the e-print tarball (the canonical LaTeX artifact)
          perl # shasum (canonical-artifact hashing) and bin/mmv's rewrite engine
          shellcheck
          poppler-utils # pdftotext, pdfinfo — the .pdftext extraction
          ocrmypdf # a broken text layer
          qpdf # repair a broken xref before extraction
          mupdf
          ghostscript
          pandoc # single-document preview/export
          python3 # site/build.py (html docs)
        ];
      in
      {
        devShells.default = pkgs.mkShell {
          packages = [ agda ] ++ contextTools;

          shellHook = ''
            echo "kitcat dev shell — $(agda --version)"
            echo "  just check-all      # typecheck the library via All.lagda.md"
            echo "  just check <Mod>    # typecheck one module"
            echo "  just lint           # width + flags"
            echo "  just sync           # All.lagda.md drift gate"
          '';
        };
      }
    );
}
