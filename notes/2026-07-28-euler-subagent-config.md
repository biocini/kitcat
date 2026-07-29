# 2026-07-28: the euler subagents, models pinned and skill access repaired

Objective: recommend a model for each of the four vendored euler
subagents, then apply the decisions. The pass found a second problem.
None of the four could load the `writing` skill, so the verifier could
not discharge a duty its own contract assigns it.

## What was done

1. **Read all four agent definitions** in `.claude/agents/`:
   `researcher`, `writer`, `verifier`, `reviewer`.
2. **Recommended a model for each**, and Lane ruled.
3. **Pinned the models** and raised the verifier's effort.
4. **Repaired skill access** for all four.

## Strongest findings and decisions

**The models were unpinned.** No agent set `model:`, so all four
inherited the session model. They would drift together on any change
of default. Pinning fixes each agent's tier against that drift.

**The pipeline position decides the tier.** The euler contract orders
the four: researcher, then writer, then verifier, then reviewer, with
verifier strictly before reviewer. An agent with a checker downstream
can run cheaper. An agent that is itself the last check cannot. The
researcher's anchors get re-checked by the verifier. The writer has
two checks after it. The reviewer has none.

**Decisions (Lane).** `researcher` and `writer` take `sonnet`.
`verifier` takes `opus`, and its effort rises from `medium` to
`high`. `reviewer` takes `fable`.

**The evidence base is thin and worth stating.** This session gave
one data point per model. A Sonnet agent surveyed morphism
conventions and returned verbatim field lists with `file:line`, plus
honest "not found, searched via" negatives. A Fable agent produced
`Test.SpikeMorphismInitial`, which checks with zero obligations and
carries a working countermodel. Nothing here compares Opus against
Fable for adversarial mathematical critique. The reviewer assignment
is therefore a bet, not a measurement.

**The `skills:` frontmatter key does nothing on its own.** It is
absent from the documented field set (`name`, `description`, `model`,
`color`, `tools`), and no shipped agent in any installed plugin uses
it. All four euler agents declared `skills: - writing`.

**None of the four had the `Skill` tool.** So none could invoke the
`writing` skill, whatever the frontmatter declared. Three of the four
also never mentioned the skill in their body prose, so they had no
instruction to reach for it either.

**That broke a contract requirement.** `.claude/rules/euler.md` says
the verifier runs the skill's bundled linter on the final artifact
and records the score in the `.provenance.md` sidecar. The verifier
had no way to reach the skill, so that duty was undischargeable.

**Repair, in two parts per agent.** Each agent gained `Skill` in its
tools, and a prose-standard section that names the skill, the mode,
and what stays exempt. The sections differ by role. The researcher's
exempts evidence tables and quoted types. The reviewer's protects
verbatim quoted passages. The writer's is longest, since prose is its
whole job. The verifier's names it as owner of the prose gate, tells
it to record the score beside the checker runs, and carries this
session's lesson: measure before and after, because an edit that adds
correct content can push a file that already sat near the gate over
it.

**The `skills:` key stays.** It is harmless if inert and functional
if the harness supports it undocumented. Removing it risks breaking
something no test here can exercise.

## Verification state

- `verified`: the frontmatter of all four files parses as YAML. Each
  carries `model`, `effort`, `Skill` in `tools`, and a prose section.
- `verified`: prose linter scores on the four prompts, before and
  after. `researcher` 3.32 to 3.13, `writer` 3.55 to 2.94,
  `verifier` 4.04 to 3.73, `reviewer` 4.76 to 4.48. The added
  sections score 0.0 on their own.
- `unverified`: that the harness honors `model: fable` in agent
  frontmatter. The Agent tool's model enum accepts `fable`. The
  plugin-development documentation lists only `inherit`, `sonnet`,
  `opus` and `haiku`, and that document may predate Fable.
- `unverified`: that `skills:` has any effect.
- `unverified`: that any of this takes effect. Agent definitions load
  at session start, so no in-session dispatch could exercise the new
  configuration.
- `inferred`: that each model suits its role. See the thin evidence
  base above.
- `blocked`: none.

## Open questions and risks

1. `fable` may not resolve in agent frontmatter. Watch the reviewer's
   first dispatch. The fallback is `opus`, which was the original
   recommendation.
2. The four prompts score between 2.94 and 4.48 on the prose linter,
   against a 2.0 gate. The residue is em dashes and long sentences in
   the original text. Agent prompts are not `docs/` deliverables, so
   no gate binds them today.
3. Whether `sonnet` holds the researcher's anti-fabrication
   discipline over long runs is untested at volume.

## Next steps

1. Smoke-test the reviewer next session to confirm `fable` resolves.
2. Consider a prose cleanup pass over the four prompts.
3. Return to `Cat.Logic.Morphism`, the open item from
   `notes/2026-07-28-morphisms-polarity-docs.md`.

## Artifacts

- `.claude/agents/researcher.md`, `.claude/agents/writer.md`,
  `.claude/agents/verifier.md`, `.claude/agents/reviewer.md`.
- The formalization half of this day is
  `notes/2026-07-28-morphisms-polarity-docs.md`.

## Source anchors

- Agent frontmatter field set:
  `~/.claude/plugins/marketplaces/claude-plugins-official/plugins/plugin-dev/skills/agent-development/SKILL.md`,
  the "Frontmatter Fields Summary" table.
- The verifier's prose-gate duty: `.claude/rules/euler.md`, the
  "Writing standard" section.
