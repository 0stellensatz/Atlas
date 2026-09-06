import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteFieldUnitMaps
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityCandidate
import Atlas.Knowledge.FiniteReciprocityValue
import Atlas.Knowledge.FrobeniusDescent
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ReciprocityMap
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.ValuationData

/-!
# Finite reciprocity homomorphism

The descent of the prime-norm construction to an additive homomorphism
on the finite Galois group: the product lift comparison, the
lift-independence and additivity of the candidate under semigroup
additivity, the conditional homomorphism, and — discharging the
additivity input from reciprocity multiplicativity — the finite
reciprocity homomorphism with its prime-norm evaluation formula (#104).

## Main definitions

* `DegreeData.finiteReciprocityHom` — the finite reciprocity
  homomorphism.

## Main statements

* `DegreeData.finiteReciprocityHom_product_lift_comparison` — the
  product lift comparison; proved.
* `DegreeData.finiteReciprocityHom_apply_eq_primeNormClass` — the
  prime-norm evaluation formula; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
and the ambient group is `Type u` since the #104 hoist. All eight
declarations shed the source's `[T2Space G]` — on the three
axiom-bearing ones Hausdorff is instance-derivable from their
`[TotallyDisconnectedSpace G]`, while on the other five it was simply
unused, so those statements are strictly more general than the
source's. The product comparison's statement drops the source's
enrichment `letI` re-anchor and the additivity proof its twin — the
`FiniteFieldUnitMaps` transport instance stands in — and the additivity
proof's restriction rewrite closes with an explicit `rfl` the source's
`rw` closed silently. The `FiniteFieldUnitMaps` import is referenced by
no name: it carries the transport instances above. The citations name
this file by bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/` in the source. The
source's `open`s go — the layer keeps everything in one namespace.

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

/-- **The chosen lift of a product and the product of the chosen lifts
compare by the degree comparison** — exactly the remaining
lift-independence obligation in the additivity proof (Yamaguchi 2026,
`MainFiniteReciprocity.lean:519`). -/
theorem finiteReciprocityHom_product_lift_comparison
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (q r : Additive
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)) :
    let KR := K.toFiniteResidueAbstractField D
    let σ₁ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK q.toMul
    let σ₂ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK r.toMul
    let σ₃ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK (q + r).toMul
    σ₃ = σ₁ * σ₂ ∨
      (∃ ι : D.FrobeniusElements KR L hLK,
        σ₁ * σ₂ = σ₃ * ι ∧
        D.frobeniusRestriction KR L hLK ι = 1 ∧
        D.finiteReciprocityValue A v K L hLK ι = 0) ∨
      (∃ ι : D.FrobeniusElements KR L hLK,
        σ₃ = (σ₁ * σ₂) * ι ∧
        D.frobeniusRestriction KR L hLK ι = 1 ∧
        D.finiteReciprocityValue A v K L hLK ι = 0) := by
  dsimp only
  apply D.finiteReciprocityHom_lift_comparison A v K L hLK
  rw [D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift,
    D.frobeniusRestriction_mul,
    D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift,
    D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift]
  rfl

/- Lift-independence of the value under semigroup additivity — the full
three-case argument (Yamaguchi 2026, `MainFiniteReciprocity.lean:555`). -/
private theorem finiteReciprocityValue_eq_of_same_restriction_of_mul
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hmul : ∀ α β : D.FrobeniusElements
        (K.toFiniteResidueAbstractField D) L hLK,
      D.finiteReciprocityValue A v K L hLK (α * β) =
        D.finiteReciprocityValue A v K L hLK α +
          D.finiteReciprocityValue A v K L hLK β)
    (σ τ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hRestriction : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ =
      D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK τ) :
    D.finiteReciprocityValue A v K L hLK σ =
      D.finiteReciprocityValue A v K L hLK τ := by
  rcases D.finiteReciprocityHom_lift_comparison A v K L hLK
      σ τ hRestriction with h | h | h
  · rw [h]
  · rcases h with ⟨ι, hτ, _, hι⟩
    rw [hτ, hmul, hι, add_zero]
  · rcases h with ⟨ι, hσ, _, hι⟩
    rw [hσ, hmul, hι, add_zero]

/- Additivity of the candidate under semigroup additivity
(Yamaguchi 2026, `MainFiniteReciprocity.lean:586`). -/
private theorem finiteReciprocityCandidate_add_of_mul
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hmul : ∀ α β : D.FrobeniusElements
        (K.toFiniteResidueAbstractField D) L hLK,
      D.finiteReciprocityValue A v K L hLK (α * β) =
        D.finiteReciprocityValue A v K L hLK α +
          D.finiteReciprocityValue A v K L hLK β)
    (q r : Additive
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)) :
    D.finiteReciprocityCandidate A v K L hLK (q + r) =
      D.finiteReciprocityCandidate A v K L hLK q +
        D.finiteReciprocityCandidate A v K L hLK r := by
  let KR := K.toFiniteResidueAbstractField D
  let σ₁ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK q.toMul
  let σ₂ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK r.toMul
  let σ₃ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK (q + r).toMul
  change D.finiteReciprocityValue A v K L hLK σ₃ =
    D.finiteReciprocityValue A v K L hLK σ₁ +
      D.finiteReciprocityValue A v K L hLK σ₂
  have hRestriction :
      D.frobeniusRestriction KR L hLK σ₃ =
        D.frobeniusRestriction KR L hLK (σ₁ * σ₂) := by
    dsimp [σ₁, σ₂, σ₃]
    rw [D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift,
      D.frobeniusRestriction_mul,
      D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift,
      D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift]
    rfl
  calc
    D.finiteReciprocityValue A v K L hLK σ₃ =
        D.finiteReciprocityValue A v K L hLK (σ₁ * σ₂) :=
      D.finiteReciprocityValue_eq_of_same_restriction_of_mul
        A v K L hLK hmul σ₃ (σ₁ * σ₂) hRestriction
    _ = D.finiteReciprocityValue A v K L hLK σ₁ +
        D.finiteReciprocityValue A v K L hLK σ₂ := hmul σ₁ σ₂

/- The homomorphism with the semigroup-additivity input isolated
(Yamaguchi 2026, `MainFiniteReciprocity.lean:631`). -/
private def finiteReciprocityHom_of_mul
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hmul : ∀ α β : D.FrobeniusElements
        (K.toFiniteResidueAbstractField D) L hLK,
      D.finiteReciprocityValue A v K L hLK (α * β) =
        D.finiteReciprocityValue A v K L hLK α +
          D.finiteReciprocityValue A v K L hLK β) :
    Additive (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) →+
      FiniteNormQuotient A K.field L hLK where
  toFun := D.finiteReciprocityCandidate A v K L hLK
  map_zero' := D.finiteReciprocityCandidate_zero A v K L hLK
  map_add' := D.finiteReciprocityCandidate_add_of_mul
    A v K L hLK hmul

/- Evaluation of the conditional homomorphism at any Frobenius lift
(Yamaguchi 2026, `MainFiniteReciprocity.lean:653`). -/
private theorem finiteReciprocityHom_of_mul_apply_of_frobeniusLift
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hmul : ∀ α β : D.FrobeniusElements
        (K.toFiniteResidueAbstractField D) L hLK,
      D.finiteReciprocityValue A v K L hLK (α * β) =
        D.finiteReciprocityValue A v K L hLK α +
          D.finiteReciprocityValue A v K L hLK β)
    (q : Additive
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup))
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ = q.toMul) :
    D.finiteReciprocityHom_of_mul A v K L hLK hmul q =
      D.finiteReciprocityValue A v K L hLK σ := by
  change D.finiteReciprocityValue A v K L hLK
      (D.chosenFiniteReciprocityFrobeniusLift
        (K.toFiniteResidueAbstractField D) L hLK q.toMul) =
    D.finiteReciprocityValue A v K L hLK σ
  apply D.finiteReciprocityValue_eq_of_same_restriction_of_mul
    A v K L hLK hmul
  rw [D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift, hσ]

/- Prime-norm formula for the conditional homomorphism
(Yamaguchi 2026, `MainFiniteReciprocity.lean:683`). -/
private theorem finiteReciprocityHom_of_mul_apply_eq_primeNormClass
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hmul : ∀ α β : D.FrobeniusElements
        (K.toFiniteResidueAbstractField D) L hLK,
      D.finiteReciprocityValue A v K L hLK (α * β) =
        D.finiteReciprocityValue A v K L hLK α +
          D.finiteReciprocityValue A v K L hLK β)
    (q : Additive
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup))
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ = q.toMul)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let Sigma : FiniteAbstractField G :=
        { field := D.frobeniusFixedField
            (K.toFiniteResidueAbstractField D) L hLK σ
          finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
      v.IsPrimeElement Sigma π) :
    let KR := K.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite KR L hLK σ
    D.finiteReciprocityHom_of_mul A v K L hLK hmul q =
      finiteNormClass A K.field L hLK
        (relativeNorm A K.field S hSK π) := by
  dsimp only
  rw [D.finiteReciprocityHom_of_mul_apply_of_frobeniusLift
    A v K L hLK hmul q σ hσ]
  exact D.finiteReciprocityValue_eq_primeNormClass_of_isPrime
    A v hAxiom K L hLK σ π hπ

/-- **The finite reciprocity homomorphism**: the prime-norm
construction descends from positive Frobenius lifts to an additive
reciprocity homomorphism on the finite Galois group
(Yamaguchi 2026, `MainFiniteReciprocity.lean:729`). -/
def finiteReciprocityHom
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    Additive (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) →+
      FiniteNormQuotient A K.field L hLK :=
  D.finiteReciprocityHom_of_mul A v K L hLK
    (D.finiteReciprocityValue_mul A v hAxiom K L hLK)

/-- **The prime-norm evaluation formula**, at any Frobenius lift and
any prime of its fixed field (Yamaguchi 2026,
`MainFiniteReciprocity.lean:746`). -/
theorem finiteReciprocityHom_apply_eq_primeNormClass
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (q : Additive
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup))
    (σ : D.FrobeniusElements (K.toFiniteResidueAbstractField D) L hLK)
    (hσ : D.frobeniusRestriction
      (K.toFiniteResidueAbstractField D) L hLK σ = q.toMul)
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField (K.toFiniteResidueAbstractField D) L hLK σ))
    (hπ :
      let Sigma : FiniteAbstractField G :=
        { field := D.frobeniusFixedField
            (K.toFiniteResidueAbstractField D) L hLK σ
          finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
      v.IsPrimeElement Sigma π) :
    let KR := K.toFiniteResidueAbstractField D
    let S := D.frobeniusFixedField KR L hLK σ
    let hSK := D.frobeniusFixedField_le KR L hLK σ
    letI : Finite
        (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
      D.frobeniusFixedField_finite KR L hLK σ
    D.finiteReciprocityHom A v hAxiom K L hLK q =
      finiteNormClass A K.field L hLK
        (relativeNorm A K.field S hSK π) := by
  exact D.finiteReciprocityHom_of_mul_apply_eq_primeNormClass
    A v hAxiom K L hLK
      (D.finiteReciprocityValue_mul A v hAxiom K L hLK)
      q σ hσ π hπ

end DegreeData

end

end Atlas.Knowledge
