# Guidelines: writing them

These documents state conventions. They are generic over any
particular presentation of the library.

## No live-tree references

A guideline never names a module, a file, or a `file:line` location
in `src/`. Not as a citation, not as an exemplar, not
parenthetically.

Reproduce the example in the abstract instead: a self-contained
fragment, with invented names as the illustration needs. It must
stand on its own for a reader who has never opened the tree. Where
a convention genuinely has no abstract statement, that is evidence
the convention is not yet understood well enough to write down.

The rule does real work, not tidying. A guideline that cites a
module inherits that module's lifetime: it goes stale when the
module moves, gains a new name, splits, or retires. It goes stale
silently. Nothing typechecks a document. Worse, it makes every
restructuring sweep touch the guidelines, which inverts the
dependency. The conventions should outlive the library's
arrangement, not lean on it for maintenance. A rename that forces a
guideline edit is the signal that the guideline overfit one
presentation.

Permitted: namespace *roles* as the root `CLAUDE.md` defines them
(the foundational namespace, the higher-inductive namespace), since
those are part of the conventions rather than of the tree. Pointers
to `notes/` and `docs/` are fine where a dated record carries a
worked application. The guideline must state its rule completely
without the pointer.

## Register

Say what the convention is, not how it came to be, who asked for
it, or what it replaced. A ruling carries its attribution and date.
That is the whole of the history a guideline records.
