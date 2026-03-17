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

# Typecheck modules changed since last commit
check-dirty:
    #!/usr/bin/env bash
    set -euo pipefail
    files=$(git diff --name-only HEAD -- src/ | grep '\.lagda\.md$' || true; git diff --name-only --cached HEAD -- src/ | grep '\.lagda\.md$' || true)
    if [ -z "$files" ]; then
        echo "No dirty .lagda.md files."
        exit 0
    fi
    failed=0
    while read -r f; do
        if [ -f "$f" ]; then
            echo "Checking $f"
            {{agda}} "$f" || failed=$((failed + 1))
        fi
    done < <(echo "$files" | sort -u)
    if [ "$failed" -gt 0 ]; then
        echo "$failed file(s) failed." >&2
        exit 1
    fi

# Create a new module
new module *flags:
    bin/new-module {{module}} {{flags}}

# Move/rename a module
mv old new *flags:
    bin/mmv {{old}} {{new}} {{flags}}

# Sync All.lagda.md with filesystem
sync *flags:
    bin/sync-all {{flags}}

# Show/generate dependency info
deps module *flags:
    bin/deps {{module}} {{flags}}

# Full dependency graph → SVG
deps-graph:
    bin/deps --all --dot | dot -Tsvg -o deps.svg
    @echo "Wrote deps.svg"

# List orphan modules
orphans:
    bin/deps --orphans

# Module statistics
stats:
    #!/usr/bin/env bash
    set -euo pipefail
    total=$(fd -e lagda.md . src/ | grep -v Stash | wc -l | tr -d ' ')
    namespaces=$(fd -e lagda.md --min-depth 2 . src/ | grep -v Stash | sed 's|^src/||;s|/.*||' | sort -u | tr '\n' ' ')
    wip=$(rg -c '^\-\- import' src/All.lagda.md 2>/dev/null || echo 0)
    echo "Modules:    $total"
    echo "WIP:        $wip"
    echo "Namespaces: $namespaces"

# Run all lint checks
lint *checks:
    bin/lint {{checks}}

# List WIP modules
wip:
    @rg '^\-\- import' src/All.lagda.md

# Benchmark
bench *args:
    bin/benchmark {{args}}

# Build HTML documentation
html:
    bin/html-build

# Preview HTML documentation locally (builds first if needed)
html-serve:
    bin/html-serve

# Deploy HTML docs to gh-pages branch
html-deploy:
    bin/html-deploy
