# Verifier checklist

Read by `verifier.md` when working each layer of euler's two-layer
verification contract (euler.md §Provenance and verification).

## Source layer

1. **Anchor every factual claim** in the draft to a specific source from the
   research files. Insert inline citations `[1]`, `[2]`, etc. directly after
   each claim. Anchors must be precise: theorem number and page for informal
   sources, `file:line` for library claims, URL for web sources.
2. **Verify every anchor** — confirm each URL resolves and contains the
   claimed content; confirm each `file:line` exists and shows the quoted
   content. Flag dead links and stale line references.
3. **Build the final Sources section** — a numbered list at the end where
   every number matches at least one inline citation in the body.
4. **Remove unsourced claims** — if a factual claim cannot be traced to any
   source in the research files, either find a source for it or remove it.
5. **Verify meaning, not just topic overlap.** A citation is valid only if the
   source actually supports the specific statement, number, or conclusion
   attached to it. A theorem number next to a misquoted statement is a failed
   citation.
6. **Refuse fake certainty.** Do not use words like `verified`, `proved`,
   `checks`, or `complete` unless the draft or research files contain the
   underlying evidence — a recorded checker run or a documented inspection.

### Citation rules

- Every factual claim gets at least one citation: "The proof proceeds by
  induction on the typing derivation [4]."
- Multiple sources for one claim: "Both standard texts give this version [3, 7]."
- No orphan citations — every `[N]` in the body must appear in Sources.
- No orphan sources — every entry in Sources must be cited at least once.
- Hedged or opinion statements do not need citations.
- When multiple research files use different numbering, merge into a single
  unified sequence starting from [1]. Deduplicate sources that appear in
  multiple files.

### Dead or stale anchors

- **Live:** keep as-is.
- **Dead URL / 404:** search for an alternative (archived version, DOI, mirror,
  updated link). If none found, remove the source and all claims that depended
  solely on it.
- **Stale `file:line`:** re-locate the declaration by name with search tooling.
  If it no longer exists, treat the claim as unsourced.
- **Redirects to unrelated content:** treat as dead.

## Kernel layer

For every formal claim in the draft:

1. **Existence and type.** Locate each named declaration with search tooling.
   Quote its actual type from disk and compare it against what the draft
   asserts. Fix the draft to match the disk, or flag the discrepancy — never
   edit your memory of the library to match the draft.
2. **Transcription check.** For every formal statement quoted in the draft,
   diff it against the actual declaration: same binders, same hypotheses, same
   conclusion. A quoted statement that omits a hypothesis is a misquote even
   if the conclusion matches.
3. **Obligation audit.** Grep the delivered files for the toolchain block's
   `sorry-token` list. Every hit is an open obligation. Any draft claim of
   completeness that contradicts a nonzero count is false — downgrade it and
   enumerate the obligations.
4. **Unsafe-marker audit.** Grep for the toolchain block's `unsafe-markers`.
   Every hit in delivered files must be disclosed in the artifact. Claims such
   as "fully checked" or "axiom-free" are false while undisclosed hits exist.
5. **Build check.** Run the toolchain block's `check` (or `check-file` on the
   relevant files) exactly as written, via shell. Record the exact command,
   the outcome, and the date in the artifact. If the check fails, the run is
   evidence of failure — report it; do not retry with modified commands to
   make it pass, and do not weaken the command's flags.
6. **Kernel-checked wording rule.** The words `verified`, `proved`, `checks`,
   `type-checks`, and `complete` may appear in the output only where supported
   by a recorded checker run or obligation audit in this pass or in the
   research files. Otherwise replace with the honest status: `unverified`,
   `blocked`, or `inferred`.
