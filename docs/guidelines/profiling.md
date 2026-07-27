# Profiling: measuring elaboration time

Conversion dominates typechecking cost in cubical Agda, and reading
the code does not reveal conversion cost. A construction that looks
heavy may be cheap, and a one-line ascription may cost seconds.
**Every performance claim in this library is a measurement**, and a
before/after profile justifies every seal, naming, or
restructuring. Revert an experiment that moves nothing. Do not keep
it on principle.

`docs/guidelines/performance.md` carries the norms this discipline
produced. This document is the measurement convention itself.

## The commands

```sh
just profile <Mod>              # per-definition attribution, cold
just profile <Mod> --total [N]  # median of N cold runs, module Total (N=3)
just profile <Mod> --internal   # decompose the Miscellaneous line
just profile <Mod> --warm       # keep the interface; measures a no-op
```

`<Mod>` is a dot-path (`Cat.Graph.Refl.Lens`) or a file path. The
underlying script is `bin/profile`.

**Cold means: discard the module's own interface, leave its
dependencies built.** The time reported is then the module's own.
`just profile` does this for you. The raw form is

```sh
rm _build/<ver>/agda/src/Some/Module.agdai     # touch does not invalidate
agda --profile=definitions src/Some/Module.lagda.md
```

Note the comment: touching the source does not invalidate the
interface. A "profile" taken without removing the `.agdai` measures
deserialization.

## When to profile

- **Before and after any structural change made for speed.**
  Without both numbers the change is a guess. This is the whole
  point of the convention.
- **On any new module that took noticeable wall-clock to check.**
  Record the cold total in the module's landing note, so the next
  person has a baseline rather than an impression.
- **Before churning a construction on suspicion.** Several
  plausible optimizations in this library measured null or worse:
  naming sub-terms in argument position, generalizing a whisker
  into a combinator, sealing a square whose consumers never
  normalize its interior. Profile first. The reading is frequently
  counterintuitive.
- **When a module's total moves and nothing in it changed.** That
  is a dependency's cost arriving through a signature, and the
  profile says which.

Not every module needs a number. Profiling is for modules with real
elaboration cost and for changes that claim to reduce it, not a
step in every commit.

## Reading the numbers

Three rules govern the reading.

**Attribution goes to the first forcer, not the owner.** The
definition that first forces a conversion gets the bill. An inline
face in a later fill re-bills, to *those lines*, the re-elaboration
of the lines it applies to. The number under a definition may
therefore be work that belongs to its consumer. One slide read 264
ms until the fill's sides got names, then read 74 ms with no change
of its own. Correspondingly, fixing a hotspot can surface a new one
downstream that is the same conserved work under a new account.

**Only the module Total confirms a fix.** Per-definition numbers
rank suspects. They do not settle anything, because attributions
reshuffle freely between runs while totals are stable to about 1%.
Use `--total` and compare medians. `just profile <Mod> --total`
reports the median of three cold runs by default.

**`Miscellaneous` is not import overhead.** The import floor is
just deserialization. Measure it by cold-checking a trivial module
with the same imports. It was ~0.3 s in this library. The rest of
`Miscellaneous` is the module's own signature elaboration, section
application, occurs checks, record positivity, and interface
serialization. `--internal` decomposes it into `Typing.CheckRHS` /
`CheckLHS` / `TypeSig` / `OccursCheck`, `Deserialization`,
`Serialization`, `Parsing`, and the rest. That split usually says
whether a cost sits in bodies, in signatures, or in the interface.

## Recording a result

A measured change states its numbers where the change lands: the
landing note, and the commit message when speed motivated the
change:

> 13,723 → 8,628 ms cold in three confirmed steps (−660 naming the
> glue subtrees, −2,934 the level-1 chains, −1,024 the level-0
> chains with aliases)

Medians of repeated cold runs, attributed per step, with the steps
that measured null named as null. A number without its method is
not a measurement. Say cold or warm, say how many runs, and say
which module the total is for.
