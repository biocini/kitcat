# reference

Developments vendored outside the library. Nothing here is on the
build path: `just check-tree` and `just lint` are scoped to `src/`, and
the module headers name namespaces (`Lib.*`, `Cat.*`, `Core.*`) that no
longer resolve. Each top-level directory is one development, named for
the formulation it carries; topic structure sits beneath it.

| Directory | Development |
| --- | --- |
| [curried-formulation](curried-formulation/) | Categories in curried form, with the monoidal, codependent, and virtual layers built on it |
| [magmoid-formulation](magmoid-formulation/) | The `Magmoids` record and the vocabulary parameterized over it — neutrality, units, isos, equivalences, functors, naturals |
| [representable-embedding](representable-embedding/) | `Cat.Base` defining a category by embedding each morphism into its post-composition action |
| [ternary-composition](ternary-composition/) | `Cat.Virtual` taking composition as a ternary relation with contractible composite fibers |
| [core-category](core-category/) | The `Lib.Core.*` line: cylinders and Kan composites, the identity and equality interfaces, groupoids, and the category built over them |
| [virt-formulation](virt-formulation/) | `Lib.Virt.*` — the same material factored into per-topic modules |
| [reflexive-graph](reflexive-graph/) | `Lib.Graph.*` — reflexive graphs, lenses, fibrations, and the virtual-graph layer carrying 2-cells |
| [path-groupoid](path-groupoid/) | `Lib.Path.*` and `Lib.Groupoid.*` — path composition, fillers, homotopies, and the erased-cubical groupoid laws |
| [braided-data](braided-data/) | Braided lists as a HIT, and the `Fin` sum symmetries that give a symmetric monoidal structure |
| [library-snapshot](library-snapshot/) | A capture of the pre-reboot tree: `Core`, `Lib`, `Data`, `HData`, `System`, `Draft` |

## Reading the layout

A `Broken/` subdirectory holds files with unfilled holes, a corrupted
module header, or imports that never resolved; they are kept for the
constructions they sketch, not as working code. Filenames are those the
files carried, so several modules of the same name sit side by side
under distinct filenames — `Base.lagda.md` and `Base-Yon.lagda.md` both
declare `module Cat.Base`, three files under `ternary-composition`
declare `module Cat.Virtual`, and `core-category` has
`Category.lagda.md` and `Source.lagda.md` as two revisions of
`Lib.Core.Category`.

`reflexive-graph/Broken/` carries four byte-identical copies of
`Lib.Graph.Virtual.Base` under different names.
