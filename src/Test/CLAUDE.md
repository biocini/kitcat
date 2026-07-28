# Test — scratch and regression witnesses

`Test.*` is the scratch namespace: spikes, probes, and regression
witnesses. It is exempt from the pre-commit gate.

## Spike zero

Test does not accumulate. Distribute its contents proactively
into long-term storage:

- Promote certified content into the owning development's `Gist`
  namespace, with the `Spike` prefix dropped.
- Archive superseded strata under `Bb.*`, frozen green.
- Remove a module only when its content is preserved elsewhere,
  and name where.

The policy keeps `Test/` fresh by convention. Anything found here
sits close to recent work, so a reader who takes guidance from a
`Test/` module does not pick up a stale carrier or a dead design.

Further policies for `Test/` spike artifacts land in this file as
they are adopted.
