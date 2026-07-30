# Statement audit: `resources/mmmm-classical-notions`

An independent statement audit of the 30 Content digests in the entry for
Mangel, Melliès and Munch-Maccagnoni, *Classical notions of computation
and the Hasegawa-Thielecke theorem (extended version)*, arXiv:2502.13033v4,
POPL 2026 [1]. The audit re-derives every digest from the vendored LaTeX
source. It accepts no prior pass's fidelity verdict, neither the
2026-07-28 audit nor the 2026-07-29 re-review [7].

## 1. Summary verdict

**30/30 CONFIRMED (digest-level), 2026-07-29, by Claude (Opus 5).**

No NOT CONFIRMED finding. Of the 30 confirmed digests, 23 are
near-verbatim renderings and 7 are faithful paraphrases. Section 3 marks
each one and names what each paraphrase compresses or expands. An
accurate paraphrase counts as CONFIRMED, which follows the sibling entry
`munch-maccagnoni-duploids` [4].

The six passages that were hand-edited on 2026-07-29, after the
re-review, all hold against the source. Section 5 records each one
against the line it claims.

Depth is **digest-level**. The audit read every digest against the
passage it cites in `article.tex`, at the line the digest names. Where a
digest turns on a notation, the audit also resolved the source's own
macro definition in the preamble. The paper is native LaTeX, so no page
render, no extraction and no glyph forensics enter this audit.

All 24 Section-map anchors to numbered statement environments in the
statement-depth regions resolve to the `\begin` line of the statement. So
do the 47 anchor citations the digests carry and the 51 further
Section-map anchors. Section 4 records no anchor faults.

Section 6 lists eight accuracy notes outside the tally. Each one is a
precision improvement, not a mathematical error, and none of them changes
a verdict.

### Hash binding

The field binds one hash:

```
@ 8d9edc19055a
```

That prefix pins `mangel-classical-notions.tar.gz`, the frontmatter
`sha256` and the entry's canonical artifact [1]. The prefix length is 12
hex, which matches the length the entry's own prior field already used
[3, l.58-59].

The reasoning. `resources/README.md` names three events that void the
field: a re-fetch, a re-extraction, and a digest addition or revision [2,
l.130-137]. Only the first two are hash-detectable, and here both reduce
to one hash. The canonical format is `latex-source`, the frontmatter
carries no `secondary-artifact` pair, and the greppable `article.tex` is
a plain `tar -xzf` member of the tarball. No correction patch and no OCR
chain stand between the artifact and the lines the digests cite. So a
change to either file changes the tarball hash, and a single binding
makes the voiding mechanical. Section 8 records the extraction check that
establishes this.

## 2. What the audit read

| Artifact | Identity | How the audit used it |
| --- | --- | --- |
| `mangel-classical-notions.tar.gz` | `8d9edc19055a…`, matches frontmatter `sha256` | custody, the `tar` member check |
| `article.tex` | `20275f3b…`, byte-identical to the tarball member | line anchors, every digest comparison |
| `article.bbl` | extracted with the source | the two citation attributions |
| entry `README.md` | `a18ab613…` | the digest text under audit |

The gunzip-decompressed inner form hashes to `d300fb10…`, matching the
frontmatter `sha256-inner`. `article.tex` holds 4906 lines.

`article.tex` is the only file the digests anchor into. It is the
document itself, in the authors' markup, so a digest comparison reads the
same bytes the arXiv build compiled. Two facts about the build shape the
audit:

- The class options at `article.tex:2-3` include `nonacm`, and `l.12`
  sets the `arxiv` boolean from that option. So the vendored source is
  the extended version.
- `l.89-96` includes the `arxiv` comment environment and excludes the
  `popl` one under that boolean. So `\begin{arxiv}` content belongs to
  the extended version alone.

The audit resolved every notation a digest renders against the source's
own macro definition, by name, in the preamble. The expansions the
digests depend on:

| Macro | Line | Expansion |
| --- | --- | --- |
| `\ccomp` | 232 | a dotted ring, the polarity-neutral composition |
| `\pcomp`, `\ncomp` | 230, 231 | `•` and `◦` |
| `\nDownarrow`, `\nUparrow` | 184, 183 | `⇓` and `⇑` |
| `\tensor`, `\parr`, `\1` | 287, 158, 182 | `⊗`, an inverted `&`, `1` |
| `\tensorialand`, `\tensorialor` | 275, 276 | `\varowedge`, `\varovee` |
| `\tensorialtrue`, `\tensorialfalse` | 277, 278 | `true`, `false` |
| `\dupldual`, `\chirdual` | 200, 196 | a star superscript |
| `\adjoint`, `\graphadjoint` | 224, 225 | `⇄` and `⇌` forms |
| `\dirac` | 248 | `1 \|b(x)⟩` |
| `\FH` | 387 | `Hasegawa-Thielecke` |
| `\joyallemma` | 349 | `Joyal's obstruction theorem` |
| `\Acategory`, `\Bcategory`, `\Mcategory`, `\Pcategory`, `\Ncategory` | 251, 252, 256, 258, 257 | `\mathscr` letters |
| `\Pcategoryt`, `\Ncategoryl` | 260, 259 | `\mathscr{P}_t`, `\mathscr{N}_l` |
| `\Dduploid`, `\Eduploid` | 187, 188 | `\mathcal D`, `\mathcal E` |
| `\duploid` | 283 | `dupl_{L,R}` |

## 3. Per-digest findings

### 1. Dialogue chirality (definition `l.1269`): CONFIRMED

`article.tex:1269-1296`. The environment opens `\begin{definition}[\citet{Mellies12,melliesdialogue}]`, so the "after Melliès" credit is the source's own (`l.1269`). The pair of symmetric monoidal categories matches `l.1270-1272`, with `\tensorialand`/`\tensorialtrue` and `\tensorialor`/`\tensorialfalse` in the two slots. The adjunction `L : 𝒜 ⇄ ℬ : R` matches `l.1274`, which uses `\rightleftarrows`. The symmetric monoidal equivalence and its `(−)*` labels match `l.1276-1284`, and the diagram carries `\simeq` at `l.1279`. The currification family, its type and its naturality in `A₁`, `A₂` and `B` match `l.1285-1296`, in both branches of the `\ifbool{arxiv}` split. The coherence clause matches `l.1296`. The reformulation sentence matches `l.1266-1268`, "we start from the symmetric reformulation (up to equivalence) of dialogue categories as dialogue chiralities". The digest's "three things" enumeration is its own structure over the source's one sentence.

### 2. Non-associative category (`l.1526`): CONFIRMED

`article.tex:1526-1547`. Both names, *unital magmoid* and *non-associative category*, match `l.1527`. The reflexive graph and the composition law match `l.1528-1531`. The neutrality equations match `l.1537`, and the "chosen map at object X of the reflexive graph" gloss on `id` matches `l.1539-1540`. `ℳ^op` matches `l.1545-1547`, which reverses the maps and keeps the objects.

The digest writes the composition's codomain as `ℳ(X,Z)`. `l.1531` reads `\mathcal M(X, Y)`. That is the source typo the Vetting section discloses, and `ℳ(X,Z)` is the correct reading: `l.1534` types the composite as `g ∘ f : X → Z`. The digest's `ℳ` renders the source's `\mathcal M`.

### 3. Association, thunkable, linear (`l.1084-1094`, `l.1552-1562`, `l.1065-1068`): CONFIRMED

`article.tex:1065-1094` and `1552-1562`. The path of length 3 and the associativity equation match `l.1552-1557` verbatim. The positional definitions match `l.1084-1094`: thunkable for "every path of length 3 that starts with `f`", linear for "every path of length 3 that ends with `h`". The value-substitution reading matches `l.1065-1068`, "it can be substituted like a value, a notion called algebraic value or thunkable expression".

The three-anchor list earns its keep. §2 states both classes as "every path of the form `(f,g,h)`" at `l.1560-1561`, which does not fix the position on its own. `l.1084-1094` fixes it.

### 4. Polarity (definition `l.1694`): CONFIRMED

`article.tex:1694-1706`. Positive matches `l.1695-1696`, "all maps of `ℳ(X,Y)` are linear" for all `Y`. Negative matches `l.1697-1698`, "all maps of `ℳ(X,Y)` are thunkable" for all `X`. Both may hold at once, and every object of an associative category is such a case, matching `l.1702-1703`. The reversal under `(−)^op` matches `l.1706`. The digest drops the source's `ℳ-` prefix on both words.

### 5. Shifts (`l.1712`): CONFIRMED

`article.tex:1712-1731`. The object assignment, the thunkable epi `ω_X : X → ⇓X` and the lifting property match `l.1713-1715`. The unique linear `f† : ⇓X → Y` with `f = f† ∘ ω_X` matches `l.1716-1717` and the left diagram at `l.1719-1724`, which labels `f†` "lin.". The negative shift `(⇑, δ)` as a positive shift on `ℳ^op` matches `l.1717`. Its `δ_Y : ⇑Y → Y` and its unique thunkable `f† : X → ⇑Y` match the right diagram at `l.1726-1730`, which labels `f†` "thunk.". The digest's `ℳ^op` renders `\mathcal M^{\op}`.

### 6. Contextual isomorphism (`l.1750-1758`): CONFIRMED

`article.tex:1738-1758`. The map `ω̄_X := id_X† : ⇓X → X` matches `l.1738`, as the lift of the identity. Both equations match `l.1743-1745`, and "defining a left and right inverse to the map `ω_X`" matches `l.1747`. The refusal to call `ω_X` an isomorphism matches `l.1750-1752`, "Despite respecting all the usual conditions to be an isomorphism in a usual associative category". The correct notion, an invertible map with both the map and its inverse thunkable as well as linear, matches `l.1753-1755`. The credit to Levy on contextual isomorphisms matches `l.1755-1757`. The closing biconditional matches `l.1757-1758` verbatim.

### 7. The shift on maps (`l.1761-1775`): CONFIRMED

`article.tex:1761-1791`. The extension from objects to maps, the uniqueness of `⇓f ∈ ℳ(⇓X, ⇓Y)` and the commuting condition match `l.1761-1771`. The digest's `⇓f ∘ ω_X = ω_Y ∘ f` reads off the diagram at `l.1766-1771`, which the source draws with a diagonal. The lifting formula `⇓f := (ω_Y ∘ f)†` matches `l.1774-1775` verbatim. Thunkability transport and identity preservation match `l.1778`. The failure to preserve composition matches `l.1779-1780`, "it *does not* preserve composition", with the diagram at `l.1781-1790`.

### 8. Functoriality of the shift, recovered (proposition `l.1795`): CONFIRMED (paraphrase)

`article.tex:1795-1802`. The biconditional, the length-3 path and the equation `ω_{X''} ∘ (f' ∘ f) = (ω_{X''} ∘ f') ∘ f` match `l.1796-1801` verbatim, including the path's three arrow labels.

The paraphrase is the diagram's name. The source writes "The diagram (equation/non-functoriality-of-shift) commutes precisely when". The digest writes "the square comparing `⇓(f' ∘ f)` with `⇓f' ∘ ⇓f`". The two shift-arrows and the composite arrow identify the right diagram, so the referent is exact. The word "square" follows the source's own vocabulary at `l.1792`, which reads the failure as "glueing two commutative triangulated squares do not necessarily produce a commutative triangulated square". Section 6, item 4 records the precision note: the diagram at `l.1781-1790` is drawn as a bare triangle on `⇓X`, `⇓X'` and `⇓X''`.

### 9. Duploid (`l.1819`): CONFIRMED (paraphrase)

`article.tex:1819-1839`. The definition matches `l.1820-1821` verbatim: a non-associative category with a positive and a negative shift, where every object is positive or negative (or both). All six notations match `l.1830-1837` in the source's order. Each gloss is the source's own, including "the subcategory of thunkable maps of `𝒫`" and "the subcategory of linear maps of `𝒩`". The notation split sits at `l.1838-1839`, where the digest points.

The paraphrase is the reading of that split. The digest says the two disciplines are one operation read at the two polarities. `l.1838-1839` bears that out: one `\ccomp`, written `g • f` when the middle object is positive and `g ◦ f` when it is negative. The digest describes the split without naming `•` and `◦` (Section 6, item 5).

### 10. Duploid functor (definition `l.1841`): CONFIRMED

`article.tex:1841-1849`. The object function `F : |𝒟| → |ℰ|` and its polarity preservation match `l.1843-1844`. The family `F_{X,Y} : 𝒟(X,Y) → ℰ(FX,FY)` matches `l.1846`. The four preserved items, compositions, identities, linearity and thunkability, match `l.1848` in that order.

### 11. The 2-category `Dupl` (proposition `l.1850`): CONFIRMED

`article.tex:1850-1852`. The statement matches verbatim, including "thunkable linear natural transformations" as the 2-cells and `\mathcal Dupl` as the name.

### 12. Adjunctions and duploids (theorem `l.1857`): CONFIRMED (paraphrase)

`article.tex:1857-1875`. The environment opens `\begin{theorem}[\citet{munchduploids}]`, so the Munch-Maccagnoni credit is the source's own. The duploid structure on the non-associative category of an adjunction `L ⊣ R` matches `l.1858-1860`. Both equivalences match `l.1860-1863`: `𝒫` with the Kleisli category on `T = R∘L`, and `𝒩` with the co-Kleisli category on `K = L∘R`. The associativity biconditional and its "or equivalently the comonad" clause match `l.1863-1864`. The converse adjunction matches `l.1865-1871`, and `L = ⇑`, `R = ⇓` given by the shift operators matches `l.1872-1873` verbatim. The diagram at `l.1869` puts `L` on the arrow out of `𝒫_t`, so `L` is the left adjoint as the digest says.

The paraphrase is twofold. First, the digest reads `𝒫` and `𝒩` as the duploid's "positive part" and "negative part", and `𝒫_t ⇄ 𝒩_l` as its "thunkable-positive and linear-negative parts". Both glosses restate `l.1833-1836` correctly. Second, `l.1874` reads "whose associated duploid `dupl_{L,R}` is equivalent to `𝒟`". The digest bolds "as a duploid", which the source does not write at that line. The expansion names the right referent, since `l.1841-1852` has just fixed duploid functors and the 2-category `Dupl` as the ambient notion. Section 6, item 6 records the note.

### 13. Central (`l.1942-1944`): CONFIRMED

`article.tex:1920-1946`. The premonoidal setting and the two maps `f : A₁ → A₁'`, `g : A₂ → A₂'` match `l.1920-1921`. All four arrows of the square match the diagram at `l.1929-1939`, and "does not necessarily commute" matches `l.1941`. The definition of *central* matches `l.1942-1944` verbatim, quantified over all maps `g`. The Kleisli observation matches `l.1945-1946`, and `ι` is the identity-on-object functor `𝒜 → Kl[𝒜,T]` at `l.1915-1916`. This diagram is a genuine four-corner square, so the digest's noun is exact here.

### 14. Symmetric monoidal Freyd structure (definition `l.1950`): CONFIRMED

`article.tex:1950-1966`. The alternative name, symmetric premonoidal `[→,Set]`-category, and the credit to Power and Robinson match `l.1951-1953`. All three data match `l.1957-1960`: the symmetric premonoidal `(𝒫, ⊗, 1)`, the symmetric monoidal `(ℳ, ⊗, 1)`, and the identity-on-object functor `ι : ℳ → 𝒫`. The strict transport matches `l.1961-1962`, and the centrality of every `ι(f)` matches `l.1963-1965`.

### 15. Symmetric monoidal duploid (definition `l.1975`, dual at `l.1981-1985`): CONFIRMED

`article.tex:1975-1985`. The positive structure matches `l.1976-1979` verbatim, as a Freyd structure `(𝒫_t, ⊗, 1) → (𝒫, ⊗, 1)` for the inclusion `𝒫_t ↪ 𝒫`. The dual negative structure matches `l.1981-1985`, with the same shape on `(𝒩_l, ⅋, ⊤) → (𝒩, ⅋, ⊤)` for `𝒩_l ↪ 𝒩`. The digest's observation about the unit holds exactly: `l.1983` writes `(𝒟, ⅋, ⊥)` for the structure and `l.1984` writes `⊤` in both slots of the Freyd structure.

### 16. Adjunctions and symmetric monoidal duploids (theorem `l.1988`): CONFIRMED (paraphrase)

`article.tex:1988-1998`. The hypotheses match `l.1989-1992`: an adjunction `L : 𝒜 ⇄ ℬ : R` with `𝒜` symmetric monoidal and the monad `T = R∘L` strong. The conclusion matches `l.1993`. The converse matches `l.1994-1997`, with `𝒫_t` symmetric monoidal and the associated monad on `𝒫_t` strong.

The paraphrase is the cross-reference. `l.1995` cites `\eqref{equation/adjunction-PN}`, which is the labelled equation at `l.1867-1871`, inside the theorem at `l.1857`. The digest expands that to "the adjunction `𝒫_t ⇄ 𝒩_l` of the theorem at l.1857", which is the right referent.

### 17. Thunkable implies central, and the converse fails (proposition `l.2074`, counterexample `l.2081-2090`): CONFIRMED

`article.tex:2074-2090`. The proposition matches `l.2074-2076` verbatim. The reason matches `l.2078-2079` verbatim, "the positive shift `⇓` preserves thunkability, so `⇓f` is also thunkable and thus, central for `⊗⁺`". The counterexample matches `l.2081-2088`: the symmetric monoidal duploid of the finite distribution monad `T : Set → Set`, whose commutativity makes every map central. The thunkability criterion matches `l.2089-2090`, "maps into positive objects are thunkable if and only they are of the form `x ↦ 1|b(x)⟩`". The digest's name for that map, the Dirac distribution at `b(x)`, is the source's own word at `l.1189`. Section 6, item 2 records the dropped coefficient.

### 18. Adjunction between graph morphisms (definition `l.2106`): CONFIRMED (paraphrase)

`article.tex:2106-2130`. Both graph morphisms match `l.2107-2108`, and the notation `F : 𝒟 ⇌ ℰ : G` matches `\graphadjoint` at `l.225`, which uses `\rightleftharpoons`. The isomorphism `φ : ℰ(F−,=) ≅ 𝒟(−,G=)` and its "natural component-wise" qualifier match `l.2110-2115`. Both naturality equations match `l.2117-2118` verbatim, and the quantifier "for every `f ∈ ℰ(FX,Y)` and every morphisms `g` of `ℰ` and `h` of `𝒟`" matches `l.2129-2130`.

The paraphrase is the closing sentence, which the source does not write at this definition. Its first half is exact: `l.2107` says graph morphisms. Its second half, "weaker than an adjunction of functors", restates `l.2013-2016`. There graph morphisms "map objects to objects and morphisms to morphisms while preserving source, target and identities, but not necessarily composition".

### 19. What a graph adjunction preserves (proposition `l.2133`): CONFIRMED

`article.tex:2133-2146`. Item 1 matches `l.2137-2138` verbatim: `F` preserves thunkability, `G` preserves linearity. Item 2 matches `l.2139-2144` verbatim, including `ε_X := φ⁻¹(id_{GX})`, the two sufficient cases (`f` linear, or the domain of `g` negative) and the dual clause for `F` with `η_X = φ(id_{FX})`.

### 20. Duploid as a graph adjunction (proposition `l.2154-2160`): CONFIRMED (paraphrase)

`article.tex:2154-2161`. Three items match. The non-associative category with all objects positive or negative (or both) matches `l.2155-2157`. The left adjoint `⇓` and the right adjoint `⇑` to `Id_𝒟` match `l.2157-2158`. `⇓A` positive with `⇑A` negative for every object `A` matches `l.2158-2160`.

The paraphrase is the split into two sentences. The source runs one "is the same thing as … together with …" sentence. The digest calls the second half "The extra data", which reads the source's "together with" correctly.

### 21. Strong monoidal functor of duploids (definition `l.2615`): CONFIRMED

`article.tex:2615-2634`. The typing `F : (𝒟, ⊗, 1) → (ℰ, ⊗, 1)` matches `l.2619`, and "is a duploid functor from `𝒟` to `ℰ`" matches `l.2622`. The family of thunkable and linear isomorphisms matches `l.2623`, with `m_{X,Y} : FX ⊗ FY → F(X ⊗ Y)` at `l.2626` and `m_1 : 1 → F(1)` at `l.2628`. Independent naturality in each component matches `l.2631`, and the coherence clause matches `l.2632-2633`.

### 22. Monoidal equivalence (definition `l.2640`): CONFIRMED

`article.tex:2640-2647`. The two strong monoidal functors and their symmetric monoidal duploids match `l.2641-2642`. Both families of thunkable and linear isomorphisms match `l.2644-2645`, with the directions `ν_X : F(GX) → X` and `ν'_X : G(FX) → X`. Naturality in `X` and compatibility with the respective `m_{X,Y}` and `m_1` match `l.2645-2646`.

### 23. Dialogue duploid (definition `l.2651`): CONFIRMED

`article.tex:2651-2675`. The two structures `(𝒟, ⊗, 1)` and `(𝒟, ⅋, ⊥)` match `l.2652-2654`. The strong monoidal equivalence and its `(−)*` labels match `l.2655-2659`, whose diagram runs both ways between `(𝒟, ⊗, 1)` and `(𝒟, ⅋, ⊥)^op`. The digest's `≃` renders the source's word "equivalence" at `l.2655`. The family of adjunctions between graph morphisms, named *currification*, matches `l.2661-2663`. The currification `χ_{X,Y,Z} : 𝒟(X ⊗ Y, Z) ≅ 𝒟(X, Y* ⅋ Z)` matches `l.2664` and its component-wise naturality matches `l.2665`. The coherence condition matches `l.2666-2668` verbatim, up to monoidality, symmetry and associativity. The `*`-autonomous remark matches `l.2674-2675` verbatim.

The digest writes `− ⊗ Y ⊣ Y* ⅋ −` where `l.2661` writes `\vdash`. That is the second source typo the Vetting section discloses, and Section 5.1 confirms both the source reading and the entry's convention anchors.

### 24. Dialogue duploids and dialogue chiralities (theorem `l.2681`): CONFIRMED (paraphrase)

`article.tex:2681-2689`. The forward half matches `l.2682-2684` verbatim: every duploid associated to a dialogue chirality `L ⊣ R` carries a dialogue duploid structure. The converse matches `l.2685-2689`, including "equivalent to `𝒟` via strong monoidal duploid functors that also preserve the duality" word for word.

The paraphrase is the same cross-reference expansion as digest 16. `l.2687` cites `\eqref{equation/adjunction-PN}`, and the digest writes `𝒫_t ⇄ 𝒩_l`, which is what that equation displays at `l.1867-1871`.

### 25. The Hasegawa-Thielecke theorem (`l.3044`): CONFIRMED

`article.tex:3044-3060`. The theorem matches `l.3045-3046` verbatim, and the environment header `\begin{theorem}[\FH{}]` carries the source's own name for it (`\FH` at `l.387`). The abstract clause matches `l.442-443`, "(in particular, for any double negation monad on a symmetric monoidal category)". The internal-duality expression of `g ∘ f` matches `l.3051-3060`, including the `φ_D` isomorphism built from `χ⁻¹`, the duality and unitors. The appendix pointer resolves: `l.3048-3050` sends the direct equational proof to `\ref{section/detailedFH}`, and that label sits at `l.4845`, "A direct equational proof of the Hasegawa-Thielecke theorem".

### 26. Syntactic Hasegawa-Thielecke theorem (theorem `l.3080`): CONFIRMED

`article.tex:3080-3083`. The statement matches verbatim, including "syntactically central for `⊗`" and "syntactically thunkable" as the two sides.

### 27. Two monad equivalences (`l.3110-3116` and `l.3123-3128`): CONFIRMED

`article.tex:3107-3128`. The presentation claim holds: both statements sit in an `\fbox` over a one-column `tabular`, with no numbered environment. The first matches `l.3107-3116`, with the duploid `𝒟` associated to an adjunction `L ⊣ R`, the monad `R∘L` idempotent, and every morphism of `𝒟` thunkable. The second matches `l.3118-3128`, with `𝒜` symmetric monoidal, `T = R∘L` strong, `T` commutative, and every morphism of `𝒟` central.

### 28. Hasegawa's corollary (corollary `l.3134-3136`): CONFIRMED

`article.tex:3130-3136`. The statement matches `l.3135` verbatim. The attribution matches `l.3132-3133`, "attributed to Hasegawa in `\citet{melliestabareau}`". The derivation matches `l.3130-3132`: "In the case of a dialogue duploid `𝒟` associated to a dialogue category, this proves as a corollary of `\cref{theorem/fh-syntactic}`". That label is the syntactic theorem at `l.3080`.

### 29. Linearly distributive duploid (definition `l.3154-3163`): CONFIRMED

`article.tex:3154-3163`. The pair of positive and negative symmetric monoidal structures matches `l.3155-3157`. The family `A ⊗ (B ⅋ C) → (A ⊗ B) ⅋ C`, its component-wise naturality and the coherence clause match `l.3157-3160`. The credit resolves: `l.3160` cites `Cockett_1997`, which `article.bbl:308-344` gives as Cockett and Seely, *Weakly distributive categories*, Journal of Pure and Applied Algebra. The associative case matches `l.3161-3162` verbatim. Section 6, item 3 records the second citation the digest omits.

### 30. The `⅋`/linear refinement (`l.3165-3170`): CONFIRMED

`article.tex:3165-3170`. The hedge is the source's own: `l.3166` reads "then suggests the following refinement of the Hasegawa-Thielecke theorem (in the dual)". The thesis pointer matches `l.3165`, `\citet[p.262]{munchthese}`. The conclusion matches `l.3167-3170`, central for `⅋` if and only if linear, in any closed linearly distributive duploid. The closedness isomorphism matches `l.3168-3169` verbatim, including the naturality in `X`, `Y'`, `Z` component-wise. The digest's `⊸` renders `\multimap`. The digest's closing sentence, that this differs from the `⊗`/thunkable theorem, follows from the two statements at `l.3044` and `l.3170`.

## 4. Anchor resolution

No anchor faults, in the Section map or in the digests.

### 4.1 The 24 statement-environment anchors

All 24 resolve to the `\begin` line of the statement they name:

- §1: definition `l.1269`.
- §2: definition `l.1526`.
- §3: definitions `l.1694`, `l.1712`, `l.1819`, `l.1841`, propositions
  `l.1795`, `l.1850`, theorem `l.1857`.
- §4: definitions `l.1950`, `l.1975`, theorem `l.1988`.
- §5: proposition `l.2074`, definition `l.2106`, propositions `l.2133`,
  `l.2154`.
- §8: definitions `l.2615`, `l.2640`, `l.2651`, theorem `l.2681`.
- §11: theorems `l.3044`, `l.3080`, corollary `l.3134`, definition
  `l.3154`.

Every one of the 24 carries a digest, and no digest cites a statement
environment outside this list. So the Load declaration's statement-depth
claim is exact: `rg -n '^\\begin\{(definition|theorem|proposition|corollary|lemma)'`
returns 24 environments inside §2 to §5, §8, §11 and the §1 chirality
definition, which is the region set the declaration names [3, l.32-39].

### 4.2 The outline-depth regions

The same census returns 43 statement environments in the main text, that
is, before `\appendix` at `l.3727`. Of those, 24 sit in the
statement-depth regions and 19 sit in the outline-depth ones: `l.1215`
in §1, `l.2169`, `l.2196`, `l.2206`, `l.2239` and `l.2249` in §6,
`l.2553`, `l.2570` and `l.2587` in §7, `l.2854`, `l.2886`, `l.2917`,
`l.2923`, `l.2978`, `l.2987`, `l.3002`, `l.3014` and `l.3025` in §9 and
§10, and `l.3559` in §13. None of the 19 carries a digest, which is what
outline depth means. §12 holds no statement environment. So the
declaration's outline-depth claim holds region by region.

One of the 19 is worth naming. `l.3014` is `\begin{definition}` for
*syntactically central*, and the Section map cites it as "syntactic
centrality (l.3014)". So a mechanical scan for map anchors that land on a
statement opener returns 25, not 24. The extra one is `l.3014`, and it is
correct that it carries no digest.

### 4.3 The remaining Section-map anchors

The map holds 75 anchors: 16 region ranges, one per row, and 59 inner
anchors. Of the 59, 25 land on statement openers (Section 4.1 and 4.2)
and the other 34 resolve as well, checked line by line:

- Structural: `l.421` opens the abstract and `l.444` closes it.
- Headings: `l.489`, `l.491`, `l.732`, `l.1059`, `l.1198`, `l.1347`,
  `l.1468`, `l.1511`, `l.1678`, `l.1879`, `l.1999`, `l.2163`, `l.2269`,
  `l.2600`, `l.2692`, `l.2952`, `l.3036`, `l.3174`, `l.3539`, `l.3691`,
  `l.3731`, `l.3752`, `l.3880`, `l.3951`, `l.4107`, `l.4280`, `l.4336`,
  `l.4402`, `l.4486`, `l.4757`, `l.4845`. Every one is a `\sectioncaps`
  or `\subsectioncaps` line.
- Unnumbered passages: `l.1552-1562`, `l.1750`, `l.1761`, `l.1942`,
  `l.1981`, `l.2081`, `l.2674`, `l.3110`, `l.3123`, `l.3165`.
- Conditional markers: `l.3172`, `l.3537`, `l.3714`, `l.3722`, `l.3725`,
  `l.3727`.

Every region range is exact at both ends. Each section row ends on the
line before the next `\sectioncaps`, and the appendix row runs from
`l.3731` to the last line, 4906.

### 4.4 The digests' own anchors

The 30 digests carry 47 anchor citations: 35 in the headers and 12 more
in the bodies. All 47 resolve to the passage the digest names. The 12
in-body anchors are `l.1738` and `l.1743-1745` (digest 6), `l.1778-1791`
(digest 7), `l.1830-1837` and `l.1838-1839` (digest 9), `l.1872-1873`
and `l.1874` (digest 12), `l.1945-1946` (digest 13), `l.2674-2675`
(digest 23), and `l.442-443`, `l.3051-3060` and `l.4845` (digest 25).

## 5. The six hand-edited passages

Each of the six passages edited on 2026-07-29 holds against
`article.tex`. The audit read the source at each cited line rather than
the edit.

### 5.1 The second source typo, at `l.2661`

The Vetting sentence claims three things, and all three hold.
`article.tex:2661` reads:

```
together with a family of adjunctions $-\otimes Y\vdash \dupldual{Y}\parr -$ 
```

So the source writes `\vdash`, that is `⊢`. The two convention anchors
both give `\dashv`. `l.1859` reads "adjunction $L\dashv R$", inside the
theorem at `l.1857`. `l.2683` reads "associated to a dialogue chirality
$L\dashv R$", inside the theorem at `l.2681`. The Dialogue duploid digest
gives `− ⊗ Y ⊣ Y* ⅋ −`, the corrected reading, as the sentence says. A
codepoint scan of the entry finds `⊢` (U+22A2) exactly once, in that
Vetting sentence, and `⊣` (U+22A3) seven times.

### 5.2 The `⟑`/`⟇` sentence in the digest preamble

Four of the five claims resolve against the source, and the fifth is a
fact about a package.

- `\tensorialand` and `\tensorialor` are the source's macros.
  `article.tex:275-276` defines them as `\varowedge` and `\varovee`.
- `\varowedge` and `\varovee` come from stmaryrd, which
  `article.tex:110` loads.
- Unicode carries no circled wedge and no circled vee. A scan of
  U+0020 to U+2FFFF finds no assigned name that holds both a circle word
  and a wedge or vee word.
- U+27D1 is `AND WITH DOT` and U+27C7 is `OR WITH DOT INSIDE`, so
  "wedge/vee-with-dot forms" names them correctly. A codepoint scan of
  the entry confirms that `⟑` is U+27D1 and `⟇` is U+27C7, four uses
  each.

The fifth claim, that the two stmaryrd glyphs draw a wedge and a vee
inside a circle, describes the rendered font. This audit reads
`article.tex` and does not compile it, so that clause is source-checked
at the macro level and **unverified** at the glyph level. It is a
statement about stmaryrd, not about the paper.

### 5.3 `ℳ` and `ℳ^op` in the Non-associative category and Shifts digests

Both hold. The source writes `$\mathcal M$` for the non-associative
category at `l.1527`, `l.1541`, `l.1545` and `l.1552`, and
`$\mathcal M^{\op}$` at `l.1545-1547`. The Shifts definition writes
`\mathcal M` at `l.1713` and `\mathcal M^{\op}` at `l.1717`, so the
negative shift is a positive shift on `ℳ^op` exactly as the digest says.
Section 6, item 1 records a second role the same letter plays in §4.

### 5.4 The Section-map tail row

Every one of the four anchors is exact.

- `l.3714` is `\begin{acks}`, and `l.21` renames that section
  "Acknowledgements".
- `l.3722` is `\printbibliography`.
- `l.3725` is `\ifbool{arxiv}{}{\end{document}}`, character for
  character.
- `l.3727` is `\appendix`.

The row's reading of `l.3725` holds. The false branch of the conditional
is `\end{document}`, so a build with the `arxiv` boolean unset stops at
that line. `l.12` sets the boolean from the `nonacm` class option. So
every appendix after `l.3727` is extended-version content, as the row
says. The row's range, `l.3714-3730`, is exact: `l.3713` is blank and
`l.3731` opens the first appendix.

### 5.5 The appendix and §13 Section-map rows

Both renamed rows are the source's own titles, with one macro expanded.
`\joyallemma` expands to `Joyal's obstruction theorem` at
`article.tex:349`.

- `l.3539` reads
  `\sectioncaps{Classical notions of computations: turning around \joyallemma}`.
  So the §13 row quotes the source's title exactly, plural
  "computations" included.
- `l.3731` reads `\sectioncaps{A proof of \joyallemma}`. So the appendix
  row's "Joyal's obstruction theorem" names that appendix by its
  subject.

The theorem itself sits at `l.3559`, `\begin{theorem}[\joyallemma]`,
inside §13.

### 5.6 The Dialogue duploid `≃` and the restored thunkable clause

Both hold.

- Digest 23 writes the duality as `(−)* : (𝒟, ⊗, 1) ≃ (𝒟, ⅋, ⊥)^op`.
  `l.2655` reads "related by a strong monoidal equivalence", and the
  diagram at `l.2656-2659` draws two bent `(−)*` arrows between those two
  objects. So `≃` renders the source's own word. The diagram itself
  carries no `≃` label, unlike the chirality diagram at `l.1279`.
- Digest 17 writes "because `⇓` preserves thunkability, so `⇓f` is also
  thunkable, and thus central for `⊗⁺`". `l.2078-2079` reads "the
  positive shift `⇓` preserves thunkability, so `⇓f` is also thunkable
  and thus, central for `⊗⁺`". The restored clause is the source's, word
  for word.

## 6. Further observations, outside the tally

These change no verdict. Each one is a precision note a future reader
should have, with the source line that settles it.

1. **The letter `ℳ` covers two source symbols.** The digest preamble says
   `ℳ` is a non-associative category, which matches `\mathcal M` in §2
   and §3. The Symmetric monoidal Freyd structure digest also writes
   `(ℳ, ⊗, 1)`, and there the source writes `\Mcategory`, that is
   `\mathscr{M}` (`l.256`, used at `l.1955`). Two distinct source symbols
   land on one entry letter. The mathematics is unaffected, since the
   digest calls that one a symmetric monoidal category, as `l.1958-1959`
   does. A second clause in the preamble would name both roles.

2. **The `1` coefficient in the Dirac form.** `\dirac` at
   `article.tex:248` expands to `1 |b(x)⟩`. The Thunkable-implies-central
   digest writes `x ↦ |b(x)⟩`. The distribution is the same one, and the
   source names it a Dirac distribution at `l.1189`.

3. **A dropped citation in the Linearly distributive duploid digest.**
   `l.3160` cites two works, `Cockett_1997` and
   `Mellies2017micrological`. The digest credits the first, correctly, as
   Cockett and Seely. It does not name the second.

4. **The diagram at `l.1781-1790` is a triangle.** The Functoriality
   digest calls it "the square". The source's own vocabulary at `l.1792`
   supports the word, since the failure is the failure of a glued
   triangulated square. The drawn diagram has three nodes, `⇓X`, `⇓X'`
   and `⇓X''`. "The functoriality diagram" or "the triangle" would send a
   reader to the right picture directly.

5. **The Duploid digest does not name `•` and `◦`.** It describes the
   notation split and points at `l.1838-1839` for the detail. The two
   symbols sit at `l.230-231` and `l.1839`: `g • f` when the middle
   object is positive, `g ◦ f` when it is negative.

6. **"as a duploid" is the entry's expansion.** `l.1874` reads
   "equivalent to `𝒟`" with no qualifier. Section 3, digest 12 gives the
   ground for the expansion.

7. **The Contextual isomorphism digest omits one clause.** `l.1739` says
   `ω̄_X` is both linear and thunkable. That clause is what makes the
   next sentence bite, since `ω_X` is only thunkable, and it is `ω_X`
   whose linearity fails in general.

8. **The Vetting section's own arithmetic is consistent.** Its three
   buckets hold 3, 4 and 23 digests, which sum to the 30 the entry
   carries. This audit covers all 30, so the buckets retire with the new
   field.

## 7. The field text

Paste this into the Vetting section, in place of the present field:

```
Statements verified: 30/30 CONFIRMED (digest-level), 2026-07-29, by
Claude (Opus 5), @ 8d9edc19055a.
```

One prefix, because one file carries the identity. `8d9edc19055a` pins
`mangel-classical-notions.tar.gz`, the frontmatter `sha256` at
`README.md:3`. Section 8 gives the recomputed hash behind the prefix.
The 12-hex length matches the length the entry's own prior field used.

Nothing else in the field changes shape. The date and the agent are this
pass. The count rises from 3/30 to 30/30 for one reason. This audit read every
digest against `article.tex`, the 4 revised ones and the 23 that no audit
had read included.

The entry now supports citing the paper's statements at all 30 digests.
The three paragraphs of the Vetting section that partition the digests
into audited, revised and new buckets describe a state this audit
retires.

## 8. Custody

Three checks, all run in this pass.

- `shasum -a 256 mangel-classical-notions.tar.gz` gives
  `8d9edc19055a23bd32a40d4e613b4462235b1a8497b6ce4310a028bc5a319a6d`,
  matching the frontmatter `sha256` at `README.md:3` character for
  character.
- `gunzip -c mangel-classical-notions.tar.gz | shasum -a 256` gives
  `d300fb10e5c9228f2687fc671aff2406576f3974920f9c717faf792282b06a5b`,
  matching the frontmatter `sha256-inner` at `README.md:10`.
- `tar -xzOf mangel-classical-notions.tar.gz article.tex | shasum -a 256`
  and `shasum -a 256 article.tex` both give `20275f3bec8cbfa3…`. So the
  extracted file on disk is byte-identical to the tarball member, and no
  editorial step sits between the tarball and the lines the digests cite.

`tar -tzvf` lists exactly the four members the Files section names:
`00README.json`, `acmart.cls`, `article.bbl` and `article.tex`, all dated
2025-12-02.

`just resources-verify` reports 16 entries and 18 hashes verified, 0
missing and 0 FATAL. It reports this entry as
`PARTIAL audit (3/30 CONFIRMED)`, which is the standing the Section 7
field text replaces.

The bibliographic record checks out against the arXiv metadata page [5].
The title, the three authors and the two dates match the Citation
section, v4 on 2 December 2025 and v1 on 18 February 2025. So do the DOI
10.1145/3776715 and the three subject classes.

## Sources

1. Éléonore Mangel, Paul-André Melliès and Guillaume Munch-Maccagnoni,
   *Classical notions of computation and the Hasegawa-Thielecke theorem
   (extended version)*, arXiv:2502.13033v4, 2 December 2025, POPL 2026,
   DOI 10.1145/3776715. Vendored at
   `resources/mmmm-classical-notions/mangel-classical-notions.tar.gz`,
   sha256 `8d9edc19055a…`, and extracted at
   `resources/mmmm-classical-notions/article.tex`, sha256 `20275f3b…`.
   Every `l.NNN` in this audit indexes into that `article.tex`.
2. `resources/README.md`, the entry-format authority. The frontmatter
   schema at `l.66-112`. The Vetting contract and the
   `Statements verified:` field at `l.114-145`. The Content digests depth
   standard at `l.174-190`.
3. `resources/mmmm-classical-notions/README.md`, the entry under audit.
   Frontmatter at `l.1-11`. Load declaration at `l.32-39`. Vetting at
   `l.50-87`. Section map at `l.112-172`. Content digests at
   `l.174-390`.
4. `outputs/duploids-entry-audit.md`, the sibling entry's statement
   audit. Its rubric, its paraphrase convention and its section shape are
   the model for this one.
5. arXiv metadata page, <https://arxiv.org/abs/2502.13033>. Retrieved
   2026-07-29. Confirms title, authors, the four version dates, and the
   PACMPL DOI.
6. `resources/mmmm-classical-notions/article.bbl:308-344`, the
   `Cockett_1997` entry: Cockett and Seely, *Weakly distributive
   categories*, Journal of Pure and Applied Algebra.
7. `outputs/.drafts/classical-notions-entry-review-2.md`, the 2026-07-29
   re-review. Read for its coverage arithmetic only. This audit
   re-derived every digest verdict and every census figure from the
   source instead of adopting them.

## Verification Record

Every command ran on 2026-07-29 from
`/Users/lane/kitcat/resources/mmmm-classical-notions`, unless the entry
names another path.

### Identity checks

| Command | Outcome |
| --- | --- |
| `shasum -a 256 mangel-classical-notions.tar.gz article.tex` | PASS. `8d9edc19055a…` matches the frontmatter `sha256`. `article.tex` is `20275f3b…`. |
| `gunzip -c mangel-classical-notions.tar.gz \| shasum -a 256` | `d300fb10…`, matches the frontmatter `sha256-inner`. |
| `tar -tzvf mangel-classical-notions.tar.gz` | Four members, all dated 2025-12-02, matching the Files section. |
| `tar -xzOf mangel-classical-notions.tar.gz article.tex \| shasum -a 256` | `20275f3b…`. The on-disk file equals the tarball member. |
| `wc -l article.tex` | 4906 lines. Fixes the appendix row's end anchor. |
| `just resources-verify` (from `/Users/lane/kitcat`) | 16 entries, 18 hashes verified, 0 missing, 0 FATAL. This entry reported as `PARTIAL audit (3/30 CONFIRMED)`. |

### Source reads

| Command | What it established |
| --- | --- |
| `awk` numbered ranges over `l.1-22`, `l.86-97`, `l.222-228`, `l.244-250` | The class options, the build boolean, the comment environments and the `\graphadjoint`, `\adjoint` and `\dirac` bodies. |
| `awk` numbered ranges over `l.421-450`, `l.1055-1100`, `l.1260-1350` | Digests 1, 3 and 25's abstract clause. |
| `awk` numbered ranges over `l.1511-1580`, `l.1678-1800`, `l.1800-1880` | Digests 2 to 12. |
| `awk` numbered ranges over `l.1879-1930`, `l.1930-1998` | Digests 13 to 16, and the identity-on-object `ι` at `l.1915-1916`. |
| `awk` numbered ranges over `l.1999-2060`, `l.2060-2162` | Digests 17 to 20, and the graph-morphism definition at `l.2013-2016`. |
| `awk` numbered ranges over `l.2600-2695` | Digests 21 to 24, and the `\vdash` at `l.2661`. |
| `awk` numbered ranges over `l.3036-3175` | Digests 25 to 30. |
| `awk` numbered ranges over `l.3010-3020`, `l.3530-3545`, `l.3685-3760`, `l.4900-4906` | The `l.3014` definition, the `\end{arxiv}` and §13 boundary, the whole tail row, and the last line. |
| `rg -n '^\\(sectioncaps\|subsectioncaps\|appendix\|begin\{abstract\}\|begin\{acks\}\|printbibliography)'` | All 31 heading anchors, the abstract opener, and 3 of the 6 conditional markers (`l.3714`, `l.3722`, `l.3727`). The other 3 came from the `awk` reads. |
| `rg -n '^\\begin\{(definition\|theorem\|proposition\|corollary\|lemma)'` | The statement census: 43 in the main text, 24 in the statement-depth regions. |
| `rg -n 'begin\{(remark\|example\|notation\|conjecture\|fact\|claim)\}'` and `rg -n 'newtheorem'` | One `\begin{example}` at `l.2261`. No other theorem-like environment exists. A census that counts it returns 44 main-text environments. |
| `rg -n 'newcommand\{\\…\}'` over the macro names in Section 2 | Every expansion in the Section 2 table. |
| `rg -n 'triangulated'` and `rg -n 'two-squares'` | The source's own diagram vocabulary at `l.1582`, `l.1638`, `l.1667`, `l.1669`, `l.1763`, `l.1792`, `l.3752`, `l.3756`. |
| `rg -n -i 'dirac'` | The `\dirac` macro at `l.248` and the source's own "Dirac distribution" at `l.1189`. |
| `rg -n 'equivalent as\|as duploids\|as a duploid'` | No hit. `l.1874` carries no such qualifier, which is the ground for observation 6. |
| `rg -n 'stmaryrd\|usepackage'` | stmaryrd loaded at `l.110`. |
| `rg -n 'documentclass'`, `rg -n 'newbool\{arxiv\}\|booltrue\|boolfalse\|includecomment\|excludecomment'` | `nonacm` at `l.3`, the boolean at `l.5` and `l.12`, the comment switch at `l.89-96`. |
| `rg -n -A6 'Cockett_1997' article.bbl` | Cockett and Seely, *Weakly distributive categories*. |
| Python codepoint scan of the entry `README.md` | `⟑` is U+27D1 and `⟇` is U+27C7, four uses each. `⊢` appears once, in the Vetting typo sentence. `⇌` once and `⇄` five times, matching the two adjunction macros. |
| Python scan of Unicode names, U+0020 to U+2FFFF | No assigned name holds both a circle word and a wedge or vee word. U+27D1 is `AND WITH DOT`, U+27C7 is `OR WITH DOT INSIDE`. |
| WebFetch of <https://arxiv.org/abs/2502.13033> | Title, three authors, v1 to v4 dates, DOI 10.1145/3776715, three subject classes. All match the Citation section. |

### Anchor audit

- 24 statement-environment anchors in the statement-depth regions: 24
  confirmed, 0 dead, 0 stale.
- 1 further Section-map anchor on a statement opener, `l.3014`, in an
  outline-depth region: confirmed, and correctly without a digest.
- 34 further Section-map inner anchors: 34 confirmed, 0 dead, 0 stale.
- 16 Section-map region ranges: 16 exact at both ends.
- 47 anchor citations inside the digests: 47 confirmed, 0 dead, 0 stale.
- 1 external URL, the arXiv abs page: live, and it carries the claimed
  content.

### Digest audit

- 30 digests read against `article.tex` at their cited anchors.
- 23 CONFIRMED (near-verbatim), 7 CONFIRMED (paraphrase), 0 NOT
  CONFIRMED.
- The 7 paraphrases are digests 8, 9, 12, 16, 18, 20 and 24. Section 3
  names what each one compresses or expands.
- 8 accuracy notes outside the tally, in Section 6. None of them changes
  a verdict, and none of them blocks the field.
- 1 clause recorded as **unverified**: the stmaryrd glyph description in
  the digest preamble (Section 5.2). It is a claim about a font, not
  about the paper, and this audit compiles nothing.

### Kernel layer

Not applicable. This audit makes no claim about any formal artifact. It
runs no proof checker and names no declaration. The audit read and wrote
no module, so `just check` had nothing to run against.

### Prose gate

`python3 .claude/skills/writing/prose-lint.py
outputs/classical-notions-entry-audit.md --max-per100 2.0`. First
delivery draft: 5845 words at 1.23 per 100 words, 0 em dashes, 0
semicolons, exit 0. After tightening: 5844 words at 1.16 per 100 words, 0
em dashes, 0 semicolons, 0 banned words, exit 0.

### Scope

The audit covers the 30 Content digests, the 75 Section-map anchors, the
47 anchor citations inside the digests, and the six passages of Section
5. Four things sit outside it. The Vetting section's account of the
2026-07-28 audit, the Files and Source provenance sections, the "What the
source establishes" section, and the appendix bodies. Section 5.4, 5.5
and Section 8 name the specific claims in those parts that the audit did
check.

The audit did not edit
`resources/mmmm-classical-notions/README.md`. Section 6 and Section 7
carry everything the lead needs to apply the field text and the eight
optional precision notes.
