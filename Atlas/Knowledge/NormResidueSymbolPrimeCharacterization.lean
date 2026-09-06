import Mathlib
import Atlas.Knowledge.AbstractReciprocityEquiv
import Atlas.Knowledge.FiniteReciprocityHom

/-!
# prime-norm characterization of the norm-residue symbol

A homomorphism on fixed coefficients is the norm-residue symbol if it annihilates extension
norms and sends the prime norm associated with each Frobenius lift to that lift's class.
The reciprocity isomorphism and its prime-norm formula make this characterization sufficient.

## Main statements

* `DegreeData.normResidueSymbol_eq_of_primeNorms` — recognition by norms and Frobenius lifts.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Degree one in the Frobenius fixed field singles out the original Frobenius lift
([Yamaguchi 2026, `FrobeniusField.lean:698`][Yamaguchi2026]). -/
theorem DegreeData.frobeniusRestriction_of_fixedField_degree_one
    (D : DegreeData G) [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [(L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (s : (D.frobeniusFixedField K L hLK σ).toSubgroup)
    (hs : D.normalizedDegree (D.frobeniusFixedResidueField K L hLK σ) s =
      Multiplicative.ofAdd (1 : ProfiniteInteger)) :
    (QuotientGroup.mk (Subgroup.inclusion (D.frobeniusFixedField_le K L hLK σ) s) :
      K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) =
      D.frobeniusRestriction K L hLK σ := by
  have hclosure : D.frobeniusFixedFieldToClosure K L hLK σ s =
      D.frobeniusInClosure K L hLK σ := by
    apply D.frobeniusFixedField_normalizedDegree_injective K L hLK σ
    rw [D.frobeniusFixedField_normalizedDegree_compatibility, hs,
      D.fixedFieldNormalizedDegree_generator]
  exact congrArg (D.extensionRestriction K.field L hLK) (congrArg Subtype.val hclosure)

/-- Recognition of the symbol from its prime-norm values, using the reciprocity formula
([Yamaguchi 2026, `MainFiniteReciprocity.lean:746`][Yamaguchi2026]). -/
theorem DegreeData.normResidueSymbol_eq_of_primeNorms
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hcf : SatisfiesClassFieldAxiom A) (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    [Finite (K.field.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.field.toSubgroup)]
    (f : ambientFixedAddSubgroup A K.field →+ Additive (Abelianization L.extensionQuotient))
    (hnorm : ∀ y, f (relativeNorm A K.field L.field L.below y) = 0)
    (hprime : ∀ σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L.field L.below,
      let KR := K.toFiniteResidueAbstractField D
      let S : FiniteAbstractField G :=
        ⟨D.frobeniusFixedField KR L.field L.below σ,
          D.frobeniusFixedField_absoluteFinite K L.field L.below σ⟩
      letI : Finite (K.field.toSubgroup ⧸ S.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
        D.frobeniusFixedField_finite KR L.field L.below σ
      f (relativeNorm A K.field S.field
        (D.frobeniusFixedField_le KR L.field L.below σ) (v.chosenPrimeElement S)) =
        Additive.ofMul (Abelianization.of (D.frobeniusRestriction KR L.field L.below σ)))
    (x : ambientFixedAddSubgroup A K.field) :
    D.normResidueSymbol A v hcf hAxiom K L
      (finiteNormClass A K.field L.field L.below x) = f x := by
  letI : Finite L.extensionQuotient := L.finite
  have hk : finiteNormSubgroup A K.field L.field L.below ≤ f.ker := by
    rintro a ⟨y, rfl⟩
    exact hnorm y
  let fN := finiteNormQuotientLift A K.field L.field L.below f hk
  have hcomp : fN.comp (D.abstractReciprocityEquiv A v hcf hAxiom K L).toAddMonoidHom =
      AddMonoidHom.id (Additive (Abelianization L.extensionQuotient)) := by
    apply AddMonoidHom.ext
    intro a
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective a.toMul
    have ha : a = Additive.ofMul (Abelianization.of q) := congrArg Additive.ofMul hq.symm
    rw [ha]
    change fN (D.abstractReciprocityEquiv A v hcf hAxiom K L
      (Additive.ofMul (Abelianization.of q))) = Additive.ofMul (Abelianization.of q)
    rw [D.abstractReciprocityEquiv_apply_of]
    obtain ⟨σ, hσ⟩ := D.frobeniusRestriction_surjective
      (K.toFiniteResidueAbstractField D) L.field L.below q
    let S : FiniteAbstractField G :=
      ⟨D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L.field L.below σ,
        D.frobeniusFixedField_absoluteFinite K L.field L.below σ⟩
    letI : Finite (K.field.toSubgroup ⧸ S.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite (K.toFiniteResidueAbstractField D) L.field L.below σ
    rw [D.finiteReciprocityHom_apply_eq_primeNormClass A v hAxiom K L.field L.below
      (Additive.ofMul q) σ hσ (v.chosenPrimeElement S) (v.chosenPrimeElement_isPrime S)]
    change f (relativeNorm A K.field S.field _ (v.chosenPrimeElement S)) = _
    have hp : f (relativeNorm A K.field S.field _ (v.chosenPrimeElement S)) =
        Additive.ofMul (Abelianization.of
          (D.frobeniusRestriction (K.toFiniteResidueAbstractField D) L.field L.below σ)) :=
      hprime σ
    exact hp.trans (congrArg (fun z => Additive.ofMul (Abelianization.of z)) hσ)
  have hx := DFunLike.congr_fun hcomp
    (D.normResidueSymbol A v hcf hAxiom K L (finiteNormClass A K.field L.field L.below x))
  change fN (D.abstractReciprocityEquiv A v hcf hAxiom K L
    (D.normResidueSymbol A v hcf hAxiom K L (finiteNormClass A K.field L.field L.below x))) =
      D.normResidueSymbol A v hcf hAxiom K L (finiteNormClass A K.field L.field L.below x) at hx
  rw [D.abstractReciprocity_normResidueSymbol] at hx
  exact hx.symm

end

end Atlas.Knowledge
