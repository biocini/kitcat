# kitcat — Cubical Agda library
set shell := ["bash", "-euo", "pipefail", "-c"]

agda := env("AGDA", "agda")

# Typecheck a module (dot-path or file path)
check module:
    #!/usr/bin/env bash
    set -euo pipefail
    mod="{{module}}"
    if [[ "$mod" == *.lagda.md ]]; then
        {{agda}} "$mod"
    elif [[ "$mod" == src/* ]]; then
        {{agda}} "$mod"
    else
        path="src/$(echo "$mod" | tr '.' '/').lagda.md"
        {{agda}} "$path"
    fi

# Typecheck entire library
check-all:
    {{agda}} src/All.lagda.md

# Create a new module
new module *flags:
    bin/new-module {{module}} {{flags}}

# Move/rename a module
mv old new *flags:
    bin/mmv {{old}} {{new}} {{flags}}

# Sync All.lagda.md with filesystem
sync *flags:
    bin/sync-all {{flags}}

# Module statistics
stats:
    #!/usr/bin/env bash
    set -euo pipefail
    total=$(fd -e lagda.md . src/ | grep -v Stash | grep -v '^src/Test/' | wc -l | tr -d ' ')
    namespaces=$(fd -e lagda.md --min-depth 2 . src/ | grep -v Stash | sed 's|^src/||;s|/.*||' | sort -u | tr '\n' ' ')
    wip=$(rg -c '^-- import' src/All.lagda.md || { [ $? -eq 1 ] && echo 0; })
    echo "Modules:    $total"
    echo "WIP:        $wip"
    echo "Namespaces: $namespaces"

# Run all lint checks
lint *checks:
    bin/lint {{checks}}

# Verify resources/ custody: recorded hashes vs vendored artifacts
# (--remote also reports latest arXiv versions for drift)
resources-verify *flags:
    bin/resources-verify {{flags}}

# List WIP modules
wip:
    @rg '^\-\- import' src/All.lagda.md

# Build HTML documentation
html:
    bin/html-build

# Preview HTML documentation locally (builds first if needed)
html-serve:
    bin/html-serve
