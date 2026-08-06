# Provenance sidecar template

The canonical shape for a `.provenance.md` sidecar (euler.md §Provenance
and verification). Every workflow that produces one starts from the base
fields, then adds only the extra fields its own step list calls for.

## Base fields (every workflow)

```markdown
# Provenance: [target or topic]

- **Date:** [date]
- **Sources consulted:** [count and/or list]
- **Sources accepted:** [count and/or list]
- **Sources rejected:** [dead, unverifiable, or removed]
- **Verification:** [PASS / PASS WITH NOTES / BLOCKED]
- **Plan:** outputs/.plans/<slug>.md
- **Research files:** [files used]
```

## Extra fields for research-only workflows (`/deepresearch`, `/lit`)

Add:

- **Rounds:** [number of research rounds]

## Extra fields for formalization workflows (`/formalize`)

Add, in this order, before **Sources consulted**:

- **Source anchors:** [informal sources with theorem/page anchors]
- **Library files delivered:** [paths]
- **Checker runs:** [commands + outcomes]
- **Obligation inventory:** [none / list with file:line]
- **Unsafe-marker inventory:** [none / list with file:line and justification]

## Extra field, any workflow (when the toolchain block exposes it)

- **Documentation coverage:** [the toolchain block's coverage-check output,
  if one exists — mandatory when the field is present, omitted otherwise]
