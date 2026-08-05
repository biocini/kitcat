# Bb — the Blackboard archive

`Bb.*` holds superseded carriers, rejected proposals, and reference
trees, each frozen at the state it reached. It does not follow the
live library. The rules below hold for the whole namespace.

## A README in every tree

Each tree carries `README.md`, one format across the namespace.
Three sections, in this order.

1. The construction. What the object is, in one or two paragraphs.
2. Provenance. Where the tree came from, when it entered `Bb`, and
   why.
3. Relationships. How the tree stands to the other `Bb`
   developments and to the live tree.

Provenance narration belongs in this file. Module prose in the
tree keeps the house rule and describes the mathematics alone.

A tree that arrives with a `TODO.md` gets a conversion, not a
copy. Carry the still-true content into the README, then delete
the `TODO.md`. An archive has no open items, so it keeps no
open-item list. Where the live line still owns those items, the
README names the live file that holds them.

One exception: `Bb.VirtualGraphs` keeps a `TODO.md`. It is the
live consolidation target, not a frozen stratum, so it carries an
open-item list the way any active tree would.

## A CHANGELOG in every tree

Each tree carries `CHANGELOG.md`, newest entry first, in the
lab-notebook register of the root `CHANGELOG.md`. Log every
alteration and every addition to the tree's entries after the tree
lands in `Bb`. An entry gives the date, what changed, and what the
checker said.

Three cases recur.

- An upstream change breaks a frozen module. Repair the module,
  then log the repair. Some trees import live modules, so this
  happens.
- A module joins the tree. Log where it came from, and the new
  module count.
- A document in the tree changes. Log it.

## One index over the namespace

`src/Bb/index.lagda.md` imports every module of every subfolder,
one section per tree. Update it whenever a module joins a `Bb`
namespace. `just check Bb.index` then covers the archive entire.

## Frozen green

Every module under `src/Bb` typechecks. `just check-tree src/Bb`
is the check. A change to an archived module is legitimate under
two conditions. The tree keeps checking, and the tree's
`CHANGELOG.md` records the change. An unlogged change is the one
failure the archive cannot absorb.
