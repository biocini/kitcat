# The documentation restructuring

Opened 2026-07-29. A standing plan, not a session record. It
supersedes four root `TODO.md` items. Those are the guideline
citation sweep, the two `docs/gloss.md` items, and part of the
prose-debt sweep.

## The problem

`docs/` accumulated three kinds of document under one roof, and two of
the three rot silently.

`just mv` sweeps `src/` only. A module rename never reaches `docs/`,
and nothing typechecks a document. So a document that names a module
inherits that module's lifetime without inheriting its maintenance.
The evidence, all found 2026-07-28:

- `docs/gloss.md` cites 22 module paths. Thirteen do not resolve. Six
  name certificates deleted with the `Gloss.*` namespace in `cb96805`.
  The ledger declared itself and that namespace "one maintained
  unit". It never learned the namespace was retired.
- `docs/deductive-systems/` had eleven of twelve files stale against
  the record cut. A hand repair fixed them the same day, with no gate
  behind it.
- Seven of twelve `docs/guidelines/` files carry `src/` citations,
  which `docs/guidelines/CLAUDE.md` bars outright. `module-anatomy.md`
  alone has ten `file:line` anchors into `src/Core/`.

`guidelines/CLAUDE.md` already states the general argument, as the
rationale for its own rule. A document that cites a module "goes
stale when the module moves, gains a new name, splits, or retires. It
goes stale silently." That argument holds for any document, not only
a guideline.

## The standard

Ruled by Lane, 2026-07-28. Four registers, each with a test.

| Register | Holds | Test |
| --- | --- | --- |
| Module prose, in the `.lagda.md` | What this object is | Next to its definition |
| `<namespace>/gloss.md` | Extended commentary on a construction | Spans modules, or explains why the shape is what it is |
| `<namespace>/lemmata.md` | The statements: theorem, location, status, date | A result, with a citation |
| `docs/guidelines/` | Standards, stated abstractly | No live-tree reference of any kind |
| `outputs/.plans/` | Per-run working memory | One workflow, then discardable |

`gloss` and `lemmata` are the classical pairing. The lemma is the
headword. The gloss is the commentary written against it.

`docs/gloss.md` survives thin. It keeps the status-class definitions,
the maintenance rules, an index of the per-namespace ledgers, and the
entries belonging to no namespace.

## Enforcement, which now exists

`just lint citations` (added 2026-07-28, `bin/lint`) fails when a
`gloss.md` or `lemmata.md` names a module that does not resolve under
`src/`. It is opt-in until the split lands, then it joins the
`changed` gate. Without it this restructuring rots the same way.

## The work

### Step 4. Split the ledger

**Gated, partially executed.** `docs/gloss.md`'s duploid entries are
under review. Do not split a moving target until the third-pass audit
settles. Started 2026-07-29 for the slice with no such entry: T25 to
T30 and T32 to T36 moved to `src/Cat/Logic/lemmata.md` and
`src/Cat/Logic/gloss.md`, prompted by a new theorem (T36) that landed
there. T31 stayed in `docs/gloss.md`: its only citation is already
archived, so it belongs in a future `src/Bb/WeakDeductiveSystem/
lemmata.md`, not yet created. T21 to T24 (the faithful-stratum arc)
are untouched, for the same reason: their citations resolve under
`Bb.CatsWithExplicitInterchange`, whose own ledger does not exist yet.
Remaining: T1 to T20 to the `Bb` trees, T31 and T21-24 once their
trees have ledgers, and the gate below for anything touching the
duploid entries.

34 entries go to three destinations. Assign each by where its subject
matter now lives, not by entry number.

- `src/Cat/Logic/lemmata.md` holds the live deductive-system line,
  roughly T21 to T35.
- `src/Bb/<tree>/lemmata.md` holds the archived strata, roughly T1 to
  T20, split by which `Bb` tree holds the cited module. Adding a file to a
  `Bb` tree needs a `CHANGELOG.md` entry in that tree.
- `docs/gloss.md` keeps the entries citing no module. Those are T12,
  T14, T15, T16 and T17: rulings and source identifications, which
  belong to no namespace.
  T12 is cited by name from the root `CLAUDE.md` hard rules, so it
  keeps a stable address here.

Two facts established 2026-07-28. Trust these:

- `Cat.Codep.Op` → `Bb.CatsWithExplicitInterchange.Op`, and
  `Gloss.PathGroupoid` → `Bb.NaiveVirtualGraph.Gist.PathGroupoid`.
  Sole matches.
- `Cat.Type`, `Cat.Codep.Coherence` and `Cat.Monoidal.Coherence` are
  **ambiguous** by basename, matching 24, 5 and 5 files. A basename
  match is not evidence of successorship. Resolve from content at
  `60410b7` or mark `UNRESOLVED`.

Six `Gloss.*` certificates were deleted, not moved, in `cb96805`:
`EightFieldWall`, `InterchangeCircularity`, `PcomConservation`,
`PropPinning`, `TautologicalFilling`, `TriangleFace23`. They are
readable at `60410b7`, the deleting commit's parent. Retiring the 🧪
status class is a restatement, not a downgrade. Those entries had
machine-checked evidence at that commit. Restate each as ✅, naming
the module and the commit where it last checked, and say the
certificate retired with the namespace. Do not silently drop the
evidence claim. Do not assert the module still checks.

The 🧪 class is incoherent regardless. Its definition promises
certificates "tracked, in `All`, frozen at the cited commit", and all
three anchors are false. `All` is retired, the namespace is gone, and
the ledger carries one commit pin in 571 lines.

### Step 5. Triage `docs/deductive-systems/`

Twelve files, about 7,400 words, go into `src/Cat/Logic/gloss.md`
and into module prose. Drop what merely duplicates a definition.

**One pass with step 4**, since both write `src/Cat/Logic/`.

This is the step with real mathematical judgment. Not everything
there is duplication. The winding count spans `framing.md`,
`actions.md` and `towers.md`. The model catalogue spans several `Bb`
trees. That material belongs to no single module, which is what
`gloss.md` is for. A wholesale collapse into module prose loses it.

### Step 6. The guideline sweep

Seven files, not the one the superseded TODO item names:
`definitions-and-proofs.md` (4 citations), `elaboration.md` (1),
`module-anatomy.md` (12), `naming.md` (2), `profiling.md` (3),
`prose-and-comments.md` (1), `records.md` (1).

`guidelines/CLAUDE.md` says how: "Reproduce the example in the
abstract instead: a self-contained fragment, with invented names as
the illustration needs. It must stand on its own for a reader who has
never opened the tree." It also gives the diagnostic. "Where a
convention genuinely has no abstract statement, that is evidence the convention is not yet
understood well enough to write down."

Independent of steps 4 and 5.

## Gates and order

1. Third-pass duploid audit settles. Then step 4 unblocks.
2. Steps 4 and 5 together, one writer, since they share a file.
3. Step 6 runs any time. It is independent.
4. `just lint citations` joins the `changed` gate once no ledger
   dangles.

## Prior art on the shape

`resources/` already solves this problem for vendored sources. Each
entry carries its own README beside the artifact, and
`just resources-verify` gates custody. The per-namespace ledger is
the same arrangement one directory over.
