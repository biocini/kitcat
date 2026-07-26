A small gloss to give attribution for the ideas here and elsewhere in
this devleopment, and because I believe a summary for the origination
of these ideas will be instructive.

The following presentation of the identity type is originally based on
Petrakis's Univalent typoids, augmented with some ideas from Kraus
et. al's work on univalent higher categories formalizable in HoTT.

My original intention following the latter's work on coherent notions
of unit, isomorphism, and so forth was to build upon and extend their
framework to encompass a complete description of higher categorical
data, for various reasons having to do with my specific research
interest. Inspired by the synthetic higher category theory espoused by
Riehl, Verity, and others, I was eventually led to a very simple
formalism, almost didactic, a condition trivially satisfied by the
ordinary identity type, but just slightly stronger — the notion that
in order to define the data of a 1-category, one must specify
2-categorical data witnessing that the composites in the 1-category
have a unique composite up to the ambient notion of isomorphism. This
definition asks us to give a notion homotopies between paths by
providing a hom type for 2-cells whose total space of composites are
contractible, whose center is given by the reflexivity at the
composition of compatible `f`, `g`, namely:
  is-contr (Σ s ∶ x ⟶ y , f ⨾ g => s) (where `_=>_` is a type of 2-cells)

This specific idea formed when I was studying Sterling's notes on
virtual bicategories, which he was kind enough to send when I asked him
about his formalization of Duploids. I began to realize that the
framework I was developing from Kraus not only could fruitfully
interpret Sterling's constructions, but that my additional work was
approaching them from a different perspective and I could directly
adapt from his definitions. During this time I also became interested
in his Reflexive Graph Lenses paper, but I did not appreciate them
fully until I got to a certain point in the development of this budding
virtual graph theory. This module is in part an attempt to flesh out those
connections.

Important to the concept of virtual graph underpinning this library's
depiction of formal categories is the observation that unitality has
subtle implications on 2-cell structure.  As Kraus and Capirotti
shows, unital data in a category can be propositionally specified and
the correct definition of units for higher category is presented and
justified by their semi-simplicial model and semi-segal types. Upon
formalizing this notion in more general bicategorical type structure
(with 1-cells and 2-cell types ranging over their shapes), I observed
the contractibility of composite data (which is trivial when these 2-cells
are in fact the ambient identity type) alongside the existence of canonical
units allows us to conclude that coherent composition necessitates that 2-cells
collapse to a groupoid structure. This happens for an unavoidable reason:
as soon as unital 1-cells exist for each object in a higher category with
the requisite unit laws, `f ⨾ g => s` enjoys an equivalence of types with
the more general `h => s` because every `h` can be described as `h ∙ eqv` or
`eqv ∙ h`, and these are homotopical to `h` up to the higher morphism
structure given by the identity laws.

Given our contractibility condition for the unary identity system of
composites, this circumstance can in retrospect be trivially
anticipated by considering an equivalence of types:
  Γ, x, y, z ⊢ Π f ∶ x ⟶ y , Π g ∶ y ⟶ z, Σ s ∶ x ⟶ z , f ⨾ g => s
             ≃ Π h ∶ x ⟶ z , Σ s ∶ x ⟶ z , h => s

for such 2-cells. This is only inhabitable once we have units, as then
we can trivially construct the right hand of the equivalence from the left,
and the conjectured equivalence follows because we know:
  Γ, x, y, z ⊢ Π f ∶ x ⟶ y , Π g ∶ y ⟶ z, is-contr (Σ s ∶ x ⟶ z , f ⨾ g => s)
             ≃ Π h ∶ x ⟶ z , is-contr (Σ s ∶ x ⟶ z , h => s)

the latter of which is, of course, contractiblity of singletons (so that we
can add that it is equivalent to the native identity type, and is in particular
an encoding of the infinity groupoid structure of the hom-type). Upon studying Sterling's reflexive graph lenses in more detail, I found that his
framework was quite clarifying perspective on the constructions I was engaging in,
and was well disposed to characterize this arrangement of circumstances, so I will
explore that structure in this module

To sum up: after units exist in 1-cell data, in one fell swoop we witness the collapse of
2-cell structure such that the data specifying the coherence of categorical
composition fully saturates the space of 2-cells, and directed morphisms
become no longer possible to express. The core decision underpinning the
perspective of virtual graph theory takes this characterization seriously,
and entails a radical departure where we take the notion of isomorphism in
general as primitive, formalizing all the constructions of our formal system
in reference to the preservation of an ambient notion of isomorphism derived
directly from our categorical data. Because we
specify our definition of unit as a particular kind of isomorphism,
this treatment is sufficient to ensure the classic description of Functors,
Natural transformations, and so on, as we can systematically derive that the
appropriate definitions preserve unitality if and only if they preserve isomorphisms.
I will leave it to those modules to demonstrate such.

For now, we will demonstrate elementary proofs of the synthetic category theory
utilizing the infrastructure of virtual graphs whose development is elsewhere.

