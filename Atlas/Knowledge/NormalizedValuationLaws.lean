import Mathlib
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.NormalizedDegree
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.ValuationData

/-!
# laws for normalized valuations

The functoriality of the engine's normalized valuations `v_K`: conjugating
the field and the element leaves the value unchanged, and along a finite
extension the valuation of a norm is the relative residue degree times the
valuation above. The first rests on the conjugation invariance of the
residue degree — conjugation fixes the degree image, hence the residue
quotient — and of the absolute norm; the second on the multiplicativity of
residue degrees and the transitivity of norms along the finite tower through
the base (#104).

## Main definitions

* `FiniteResidueAbstractField.conjugate` / `FiniteAbstractField.conjugate` —
  the conjugate field carries the transported finiteness.

## Main statements

* `DegreeData.fieldImage_conjugate` — conjugation fixes the degree image;
  proved.
* `FiniteResidueAbstractField.residueDegree_conjugate` /
  `FiniteAbstractField.residueDegree_conjugate` — conjugation fixes the
  residue degree; proved.
* `ValuationData.normalizedValuation_conjugate` — `v_{K^σ}(a^σ) = v_K(a)`;
  proved.
* `ValuationData.normalizedValuation_tower` — `v_K ∘ N_{L|K} = f_{L|K}·v_L`
  for a finite extension `L | K`; proved.

## Implementation notes

The source states the tower law with a `let` binding the enriched extension
inside the statement; here the residue degree is spelled out, so consumers
read the coefficient without introducing the binding first. The source also
reproves the field-level residue-degree invariance from scratch; here it is
the residue-finite statement applied to the enriched field, which conjugation
carries to the same subgroup. The proofs are otherwise the source's, with the
layer's `ProfiniteInteger` for its `ZHat` and `Subgroup.subgroupOf` for its
relative subgroup.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **Conjugation fixes the degree image**: `d(G_{K^σ}) = d(G_K)`, the degree
landing in a commutative group (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/ValuationLaws.lean:24`). -/
theorem DegreeData.fieldImage_conjugate [ContinuousMul G]
    (D : DegreeData G) (K : ClosedSubgroup G) (σ : G) :
    D.fieldImage (conjugateClosedSubgroup K σ) = D.fieldImage K := by
  rw [D.fieldImage_eq_map, D.fieldImage_eq_map]
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    let k : K.toSubgroup :=
      ⟨σ * x * σ⁻¹, (conjugateClosedSubgroup_mem K σ x).mp hx⟩
    refine ⟨k.1, k.2, ?_⟩
    simp [k, map_mul, mul_assoc]
  · rintro ⟨k, hk, rfl⟩
    let x : G := σ⁻¹ * k * σ
    have hx : x ∈ conjugateClosedSubgroup K σ := by
      rw [conjugateClosedSubgroup_mem]
      change σ * x * σ⁻¹ ∈ K.toSubgroup
      simpa [x, mul_assoc] using hk
    refine ⟨x, hx, ?_⟩
    simp [x, map_mul, mul_assoc, mul_comm]

variable {D : DegreeData G}

/-- **The conjugate of a residue-finite field**: the transported finiteness
comes from the conjugation invariance of the degree image (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/ValuationLaws.lean:48`). -/
def FiniteResidueAbstractField.conjugate [ContinuousMul G]
    (K : FiniteResidueAbstractField D) (σ : G) :
    FiniteResidueAbstractField D where
  field := conjugateClosedSubgroup K.field σ
  finiteResidueQuotient := by
    unfold DegreeData.residueQuotient
    rw [D.fieldImage_conjugate K.field σ]
    exact K.finiteResidueQuotient

/-- **Conjugation fixes the residue degree at the residue-finite boundary**
(Yamaguchi 2026, `AbstractClassFieldTheory/Degree/ValuationLaws.lean:60`). -/
theorem FiniteResidueAbstractField.residueDegree_conjugate [ContinuousMul G]
    (K : FiniteResidueAbstractField D) (σ : G) :
    (K.conjugate σ).residueDegree = K.residueDegree := by
  letI : Finite (D.residueQuotient K.field) := K.finiteResidueQuotient
  letI : Finite
      (D.residueQuotient (conjugateClosedSubgroup K.field σ)) :=
    (K.conjugate σ).finiteResidueQuotient
  apply PNat.eq
  change Nat.card
      (D.residueQuotient (conjugateClosedSubgroup K.field σ)) =
    Nat.card (D.residueQuotient K.field)
  unfold DegreeData.residueQuotient
  have himage := D.fieldImage_conjugate K.field σ
  apply Nat.card_congr
  exact Subgroup.quotientEquivOfEq
    (congrArg
      (fun H : Subgroup ProfiniteIntegerMul =>
        H.subgroupOf (⊤ : Subgroup ProfiniteIntegerMul))
      himage)

/-- **The conjugate of a field finite over the base**: the transported
finiteness comes from the conjugate coset equivalence (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/ValuationLaws.lean:82`). -/
def FiniteAbstractField.conjugate [ContinuousMul G]
    (K : FiniteAbstractField G) (σ : G) :
    FiniteAbstractField G where
  field := conjugateClosedSubgroup K.field σ
  finite := Finite.of_equiv
    ((baseField G).toSubgroup ⧸
      K.field.toSubgroup.subgroupOf (baseField G).toSubgroup)
    (absoluteConjugateCosetEquiv K.field σ).symm

/-- **Conjugation fixes the residue degree** (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/ValuationLaws.lean:93`). -/
theorem FiniteAbstractField.residueDegree_conjugate [ContinuousMul G]
    (K : FiniteAbstractField G) (D : DegreeData G) (σ : G) :
    (K.conjugate σ).residueDegree D = K.residueDegree D :=
  (K.toFiniteResidueAbstractField D).residueDegree_conjugate σ

namespace ValuationData

variable {A : Rep ℤ G}

/-- **Normalized valuations are conjugation-invariant**:
`v_{K^σ}(a^σ) = v_K(a)`, in the construction's right-action notation
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/ValuationLaws.lean:119`). -/
theorem normalizedValuation_conjugate [ContinuousMul G]
    (v : ValuationData D A) (K : FiniteAbstractField G) (σ : G)
    (a : ambientFixedAddSubgroup A K.field) :
    v.valuationAt (K.conjugate σ)
        (conjugateFixedElement A K.field σ a) =
      v.valuationAt K a := by
  letI : Finite ((baseField G).toSubgroup ⧸
      (conjugateClosedSubgroup K.field σ).toSubgroup.subgroupOf
        (baseField G).toSubgroup) :=
    (K.conjugate σ).finite
  apply Subtype.ext
  apply ProfiniteInteger.nsmul_left_injective (K.residueDegree D).pos.ne'
  calc
    (K.residueDegree D : ℕ) •
        v.dividedAt (K.conjugate σ)
          (conjugateFixedElement A K.field σ a) =
      ((K.conjugate σ).residueDegree D : ℕ) •
        v.dividedAt (K.conjugate σ)
          (conjugateFixedElement A K.field σ a) := by
            rw [K.residueDegree_conjugate D σ]
    _ = v.normCompositeAt (K.conjugate σ)
        (conjugateFixedElement A K.field σ a) :=
      v.residueDegree_nsmul_dividedAt (K.conjugate σ) _
    _ = v.normCompositeAt K a := by
      change v.toAddMonoidHom
          (normToBase A (conjugateClosedSubgroup K.field σ)
            (conjugateFixedElement A K.field σ a)) =
        v.toAddMonoidHom (normToBase A K.field a)
      congr 1
      apply Subtype.ext
      calc
        ((normToBase A (conjugateClosedSubgroup K.field σ)
            (conjugateFixedElement A K.field σ a) :
              ambientFixedAddSubgroup A (baseField G)) : A.V) =
          A.ρ σ⁻¹
            ((normToBase A K.field a :
              ambientFixedAddSubgroup A (baseField G)) : A.V) := by
                simpa [normToBase] using
                  relativeNorm_absoluteConjugate_apply A K.field σ a
        _ = ((normToBase A K.field a :
              ambientFixedAddSubgroup A (baseField G)) : A.V) :=
          (normToBase A K.field a).2 ⟨σ⁻¹, trivial⟩
    _ = (K.residueDegree D : ℕ) • v.dividedAt K a :=
      (v.residueDegree_nsmul_dividedAt K a).symm

/-- **The norm–valuation formula**: `v_K ∘ N_{L|K} = f_{L|K}·v_L` for a
finite extension `L | K` of fields finite over the base (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/ValuationLaws.lean:166`). -/
theorem normalizedValuation_tower (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (a : ambientFixedAddSubgroup A E.field.field) :
    ((E.toFiniteResidueAbstractExtension D).residueDegree : ℕ) •
        ((v.valuationAt E.field a : v.valueGroup) : ProfiniteInteger) =
      ((v.valuationAt E.base
          (relativeNorm A E.base.field E.field.field E.below a) :
        v.valueGroup) : ProfiniteInteger) := by
  let ER := E.toFiniteResidueAbstractExtension D
  apply ProfiniteInteger.nsmul_left_injective (E.base.residueDegree D).pos.ne'
  change (ER.base.residueDegree : ℕ) •
      ((ER.residueDegree : ℕ) • v.dividedAt E.field a) =
    (ER.base.residueDegree : ℕ) •
      v.dividedAt E.base
        (relativeNorm A E.base.field E.field.field E.below a)
  rw [smul_smul, Nat.mul_comm (ER.base.residueDegree : ℕ),
    ER.residueDegree_mul_absoluteResidueDegree D]
  change (E.field.residueDegree D : ℕ) • v.dividedAt E.field a =
    (E.base.residueDegree D : ℕ) •
      v.dividedAt E.base
        (relativeNorm A E.base.field E.field.field E.below a)
  rw [v.residueDegree_nsmul_dividedAt E.field,
    v.residueDegree_nsmul_dividedAt E.base]
  change v.toAddMonoidHom (normToBase A E.field.field a) =
    v.toAddMonoidHom
      (normToBase A E.base.field
        (relativeNorm A E.base.field E.field.field E.below a))
  let T : FiniteTower G := {
    top := E.field.field
    middle := E.base.field
    base := baseField G
    top_le_middle := E.below
    middle_le_base := le_baseField E.base.field
    finiteTopQuotient := E.finiteQuotient
    finiteBaseQuotient := E.base.finite }
  exact congrArg v.toAddMonoidHom
    (by simpa [T, normToBase] using (T.norm_trans_apply A a).symm)

end ValuationData

end

end Atlas.Knowledge
