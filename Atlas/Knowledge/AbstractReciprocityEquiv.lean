import Mathlib
import Atlas.Knowledge.AbstractReciprocityTheorem
import Atlas.Knowledge.ClassFieldAxiom
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityHom
import Atlas.Knowledge.IntermediateGaloisTransfer
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.ValuationData

/-!
# abstract reciprocity equivalence

The reciprocity isomorphism of the abstract reciprocity theorem: for a
finite Galois extension `L/K`, the reciprocity homomorphism identifies
the abelianized Galois group with the finite norm quotient — packaged
as an additive equivalence — together with the norm-residue symbol
`(·, L/K)`, its inverse, and their evaluation identities on Galois
elements (#104).

## Main definitions

* `DegreeData.abstractReciprocityEquiv` — the reciprocity isomorphism.
* `DegreeData.normResidueSymbol` — the norm-residue symbol, the
  reciprocity isomorphism's inverse.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
and the ambient group sits in one `{G : Type u}` scope,
universe-polymorphic since the #104 hoist. **The interface departure of
this brick**: where the source derives its unit-cohomology input as
`v.classFieldAxiom_implies_unramifiedUnitCohomology hcf` — through the
Tate-cohomology reading of the axiom the layer deliberately does not
carry (the decision recorded in `Atlas.Knowledge.ClassFieldAxiom`'s
notes) — all five declarations thread
`hAxiom : v.SatisfiesUnramifiedUnitCohomology D` as an explicit
hypothesis alongside `hcf`, and the statement-level occurrences of the
derivation become the binder. Each statement is thereby weaker than the
source's: the discharge of the hypothesis is moved to the local
instantiation, which proves the unit-cohomology facts directly —
`Atlas.Knowledge.localHenselianValuation_satisfiesUnramifiedUnitCohomology`
is that proof. The same convention deliberately commits the remaining
`Main.lean` derivation sites, the naturality tail among them. All five
shed the source's `[T2Space G]` (the continuing cascade) and keep
`[TotallyDisconnectedSpace G]`, which the totally ramified chain
consumes. Everything else ports token-for-token; the file is the
source's `Reciprocity/Main.lean:847`–`:961`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The abstract reciprocity theorem (reciprocity isomorphism): for a
finite Galois extension `L/K`, the reciprocity homomorphism identifies
the abelianized Galois group with the finite norm quotient**
(Yamaguchi 2026, `AbstractClassFieldTheory/Reciprocity/Main.lean:852`). -/
def abstractReciprocityEquiv
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
    Additive (Abelianization L.extensionQuotient) ≃+
      FiniteNormQuotient A K.field L.field L.below := by
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
  exact AddEquiv.ofBijective
    (D.transferNormNaturalityAbelianizedReciprocity
      A v hAxiom K L.field L.below)
    (v.abstractReciprocity_abelianizedReciprocity_bijective
      hcf hAxiom K L)

/-- On a Galois element, the reciprocity isomorphism is the reciprocity
homomorphism of the finite reciprocity equivalence (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:876`). -/
@[simp]
theorem abstractReciprocityEquiv_apply_of
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (q : L.extensionQuotient) :
    letI : Finite
        (K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
    D.abstractReciprocityEquiv A v hcf hAxiom K L
        (Additive.ofMul (Abelianization.of q)) =
      D.finiteReciprocityHom A v hAxiom
        K L.field L.below
        (Additive.ofMul q) := by
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
  exact D.transferNormNaturalityAbelianizedReciprocity_of
    A v hAxiom K L.field L.below
      q

/-- **The norm-residue symbol `(·, L/K)`, defined in this construction
as the inverse of the reciprocity isomorphism** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:900`). -/
def normResidueSymbol
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
    FiniteNormQuotient A K.field L.field L.below ≃+
      Additive (Abelianization L.extensionQuotient) := by
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
  exact (D.abstractReciprocityEquiv A v hcf hAxiom K L).symm

/-- The norm-residue symbol sends the reciprocity class of a Galois
element back to its class in the abelianization (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:919`). -/
@[simp]
theorem normResidueSymbol_finiteReciprocityHom
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (q : L.extensionQuotient) :
    letI : Finite
        (K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
    D.normResidueSymbol A v hcf hAxiom K L
        (D.finiteReciprocityHom A v hAxiom
          K L.field L.below
          (Additive.ofMul q)) =
      Additive.ofMul (Abelianization.of q) := by
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
  rw [← D.abstractReciprocityEquiv_apply_of A v hcf hAxiom K L q]
  exact (D.abstractReciprocityEquiv A v hcf hAxiom K L).symm_apply_apply _

/-- Reciprocity followed by the norm-residue symbol inverse is the
identity on the finite norm quotient (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:943`). -/
@[simp]
theorem abstractReciprocity_normResidueSymbol
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
    ∀ a : FiniteNormQuotient A K.field L.field L.below,
    D.abstractReciprocityEquiv A v hcf hAxiom K L
        (D.normResidueSymbol A v hcf hAxiom K L a) = a := by
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
  intro a
  exact (D.abstractReciprocityEquiv A v hcf hAxiom K L).apply_symm_apply a

end DegreeData

end

end Atlas.Knowledge
