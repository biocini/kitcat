# Guidelines — writing them

These documents state conventions. They are generic over any
particular presentation of the library.

## No live-tree references

A guideline never names a module, a file, or a `file:line` location in
`src/`. Not as a citation, not as an exemplar, not parenthetically.

Reproduce the example in the abstract instead: a self-contained
fragment, with whatever names the illustration needs invented for it,
that stands on its own for a reader who has never opened the tree.
Where a convention genuinely has no abstract statement, that is
evidence the convention is not yet understood well enough to write
down.

The rule is load-bearing rather than tidy. A guideline that cites a
module inherits that module's lifetime: it goes stale when the module
moves, is renamed, is split, or retires, and it goes stale silently —
nothing typechecks a document. Worse, it makes every restructuring
sweep touch the guidelines, which inverts the dependency: the
conventions should outlive the arrangement of the library, not be
maintained by it. A rename that forces a guideline edit is the signal
that the guideline was overfitted to one presentation.

Permitted: namespace *roles* as the root `CLAUDE.md` defines them
(the foundational namespace, the higher-inductive namespace), since
those are part of the conventions rather than of the tree. Pointers to
`notes/` and `docs/` are permitted where a dated record carries a
worked application, provided the guideline states its rule completely
without following the pointer.

## Register

Say what the convention is, not how it came to be, who asked for it,
or what it replaced. A ruling carries its attribution and date; that
is the whole of the history a guideline records.
