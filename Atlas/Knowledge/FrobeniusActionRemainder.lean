import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusFixedField
import Atlas.Knowledge.FrobeniusQuotientAction
import Atlas.Knowledge.FrobeniusQuotientDescent
import Atlas.Knowledge.FrobeniusSemigroup
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.TopologicalGeneration
import Atlas.Knowledge.TransferOrbitClosure

/-!
# Frobenius action remainder

The Frobenius exponent, conjugation, quotient-action, and
action-remainder identities that reciprocity-map multiplicativity
consumes: the exponent is additive on the semigroup, a Frobenius element
fixes its own fixed field inside `A_{L̃}`, the remainder `φⁿσ⁻¹` of a
degree-one `φ` has degree zero and multiplies by conjugating the second
factor, the left-action conjugate carries the fixed field to its
conjugate, and on the fixed field of `σ` the remainder acts as the
`n`-th power of `φ` (#104).

## Main definitions

* `DegreeData.frobeniusActionRemainder` — the remainder `φⁿσ⁻¹`.
* `DegreeData.frobeniusActionConjugate` — the left-action conjugate
  `φᵐσφ⁻ᵐ`.

## Main statements

* `DegreeData.frobeniusExponent_mul` — exponent additivity; proved.
* `DegreeData.frobeniusQuotientAction_fixedFieldInclusion` — a Frobenius
  element fixes its fixed field ambiently; proved.
* `DegreeData.conjugate_frobeniusFixedField_actionConjugate` — the
  conjugate's fixed field; proved.
* `DegreeData.frobeniusActionRemainder_mul` — the remainder's
  multiplication law; proved.
* `DegreeData.frobeniusActionRemainder_apply_fixedField` — the remainder
  on the fixed field; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`ZHat` is `ProfiniteInteger` with the power-injectivity under the
layer's name, `extensionSubgroup_frobeniusFixedField` is the layer's
`subgroupOf_frobeniusFixedField`, and the closure unfolds cite the
layer-local `frobeniusClosure` name. Only the last section is
`Type`-valued — its `frobeniusQuotientRepresentation` callee pins — and
the source's other `IntegralRepGroupType` section generalizes to
`Type u` along with the algebra sections. The source's no-op opens go,
and the citations name this file by bare basename — it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/MainMultiplicativity/`
in the source, whose full path pushes the unbreakable citation span past
the line budget. The multiplication law's
mid-proof `simp` is the source's own; the flexible-tactic style warning
it draws is accepted rather than the proof reshaped.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

universe u

namespace Atlas.Knowledge

noncomputable section

section frobeniusAlgebra

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The exponent is additive under multiplication in the Frobenius
semigroup** ([Yamaguchi 2026, `FrobeniusActionRemainder.lean:32`]
[Yamaguchi2026]). -/
@[simp]
theorem frobeniusExponent_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ₁ σ₂ : D.FrobeniusElements K L hLK) :
    D.frobeniusExponent K L hLK (σ₁ * σ₂) =
      D.frobeniusExponent K L hLK σ₁ +
      D.frobeniusExponent K L hLK σ₂ := by
  apply ProfiniteInteger.ofAdd_one_pow_injective
  calc
    (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
        D.frobeniusExponent K L hLK (σ₁ * σ₂) =
      D.extensionNormalizedDegree K L hLK (σ₁ * σ₂).1 :=
        (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
          (σ₁ * σ₂)).symm
    _ = D.extensionNormalizedDegree K L hLK σ₁.1 *
        D.extensionNormalizedDegree K L hLK σ₂.1 := by
      rw [frobeniusMul_coe, map_mul]
    _ = (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
            D.frobeniusExponent K L hLK σ₁ *
        (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
            D.frobeniusExponent K L hLK σ₂ := by
      rw [D.extensionNormalizedDegree_frobenius_eq_pow,
        D.extensionNormalizedDegree_frobenius_eq_pow]
    _ = (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
            (D.frobeniusExponent K L hLK σ₁ +
              D.frobeniusExponent K L hLK σ₂) := by
      rw [pow_add]

end DegreeData

end frobeniusAlgebra

section frobeniusQuotientActions

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **A Frobenius element fixes the elements of its actual fixed field,
viewed inside `A_{L̃}`** ([Yamaguchi 2026, `FrobeniusActionRemainder.lean:77`]
[Yamaguchi2026]). -/
theorem frobeniusQuotientAction_fixedFieldInclusion (D : DegreeData G)
    (A : Rep ℤ G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    D.frobeniusQuotientAction A K.field L hLK σ.1
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) =
      fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
        (D.maximalUnramifiedField L)
        (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a := by
  let k : K.field.toSubgroup := Quotient.out σ.1
  have hσk : σ.1 = QuotientGroup.mk k := (Quotient.out_eq' σ.1).symm
  have hσClosure : σ.1 ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup := by
    exact Subgroup.le_topologicalClosure _
      (Subgroup.subset_closure (by simp))
  have hkFixed : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
    change QuotientGroup.mk k ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup
    rw [← hσk]
    exact hσClosure
  rw [← D.subgroupOf_frobeniusFixedField K L hLK σ] at hkFixed
  obtain ⟨s, hs⟩ := hkFixed
  rw [hσk]
  apply Subtype.ext
  change A.ρ k.1 a.1 = a.1
  let sFixed : (D.frobeniusFixedField K L hLK σ).toSubgroup :=
    ⟨s.1, ⟨s, hs.1, rfl⟩⟩
  have hsval : sFixed.1 = k.1 := hs.2
  rw [← hsval]
  exact a.2 sFixed

end DegreeData

end frobeniusQuotientActions

section actionRemainderAlgebra

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The action remainder `φⁿσ⁻¹`** — the left-`Rep`-action counterpart
of the right-action notation ([Yamaguchi 2026, `FrobeniusActionRemainder.lean:126`]
[Yamaguchi2026]). -/
def frobeniusActionRemainder (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ : D.FrobeniusElements K L hLK) :
    K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK :=
  φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹

/-- For `φ` of Frobenius exponent one, the action remainder has
normalized degree zero ([Yamaguchi 2026, `FrobeniusActionRemainder.lean:136`]
[Yamaguchi2026]). -/
theorem frobeniusActionRemainder_mem_degreeKernel (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    D.frobeniusActionRemainder K L hLK φ σ ∈
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker := by
  change D.extensionNormalizedDegree K L hLK
      (φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹) = 1
  rw [map_mul, map_pow, map_inv,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ, hφ]
  simp

/-- **The conjugate adapted to the left action**, `φᵐσφ⁻ᵐ` with the
exponent carried along ([Yamaguchi 2026, `FrobeniusActionRemainder.lean:153`]
[Yamaguchi2026]). -/
def frobeniusActionConjugate (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ : D.FrobeniusElements K L hLK) (m : ℕ) :
    D.FrobeniusElements K L hLK := by
  let n := D.frobeniusExponent K L hLK σ
  refine ⟨φ.1 ^ m * σ.1 * φ.1⁻¹ ^ m, n,
    D.frobeniusExponent_pos K L hLK σ, ?_⟩
  rw [map_mul, map_mul, map_pow, map_pow, map_inv,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ]
  simp [n, mul_assoc]

/-- The underlying quotient element of the Frobenius action
conjugate. -/
@[simp]
theorem frobeniusActionConjugate_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ : D.FrobeniusElements K L hLK) (m : ℕ) :
    (D.frobeniusActionConjugate K L hLK φ σ m).1 =
      φ.1 ^ m * σ.1 * φ.1⁻¹ ^ m := by
  simp [frobeniusActionConjugate]

/-- Frobenius action conjugation preserves the Frobenius exponent
([Yamaguchi 2026, `FrobeniusActionRemainder.lean:179`]
[Yamaguchi2026]). -/
@[simp]
theorem frobeniusExponent_actionConjugate (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ : D.FrobeniusElements K L hLK) (m : ℕ) :
    D.frobeniusExponent K L hLK
        (D.frobeniusActionConjugate K L hLK φ σ m) =
      D.frobeniusExponent K L hLK σ := by
  apply ProfiniteInteger.ofAdd_one_pow_injective
  calc
    (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
        D.frobeniusExponent K L hLK
          (D.frobeniusActionConjugate K L hLK φ σ m) =
      D.extensionNormalizedDegree K L hLK
        (D.frobeniusActionConjugate K L hLK φ σ m).1 :=
          (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
            (D.frobeniusActionConjugate K L hLK φ σ m)).symm
    _ = (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
          D.frobeniusExponent K L hLK σ := by
      rw [frobeniusActionConjugate_coe, map_mul, map_mul, map_pow, map_pow,
        map_inv,
        D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ]
      simp [mul_assoc]

/-- **The fixed field of the left-action conjugate `φᵐσφ⁻ᵐ` is the
corresponding conjugate of the fixed field of `σ`** — the representative
only expresses the quotient conjugation ambiently ([Yamaguchi 2026, `FrobeniusActionRemainder.lean:207`]
[Yamaguchi2026]). -/
theorem conjugate_frobeniusFixedField_actionConjugate
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ : D.FrobeniusElements K L hLK) (m : ℕ) :
    let q := φ.1 ^ m
    let k : K.field.toSubgroup := Quotient.out q
    conjugateClosedSubgroup
        (D.frobeniusFixedField K L hLK σ) k.1⁻¹ =
      D.frobeniusFixedField K L hLK
        (D.frobeniusActionConjugate K L hLK φ σ m) := by
  dsimp only
  let q := φ.1 ^ m
  let k : K.field.toSubgroup := Quotient.out q
  let σ' := D.frobeniusActionConjugate K L hLK φ σ m
  have hkq :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = q :=
    Quotient.out_eq' q
  have hσ' : σ'.1 = q * σ.1 * q⁻¹ := by
    simp [σ', q, frobeniusActionConjugate_coe]
  ext x
  change x ∈ conjugateClosedSubgroup
      (D.frobeniusFixedField K L hLK σ) k.1⁻¹ ↔
    x ∈ D.frobeniusFixedField K L hLK σ'
  rw [conjugateClosedSubgroup_mem]
  constructor
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let xK : K.field.toSubgroup := ⟨x, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
      have hxval : x = k.1 * t.1 * k.1⁻¹ := by
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by
            simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [hxval]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem k.2 htK) (K.field.toSubgroup.inv_mem k.2)⟩
    have htClosure' : QuotientGroup.mk t ∈
        (closedSubgroupGenerated ({σ.1} : Set
          (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))).toSubgroup := by
      simpa [frobeniusClosure] using htClosure
    have hxClosure' : q * QuotientGroup.mk t * q⁻¹ ∈
        (closedSubgroupGenerated ({σ'.1} : Set
          (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))).toSubgroup := by
      rw [hσ']
      exact (mem_closedSubgroupGenerated_conjugate_iff
        q σ.1 (QuotientGroup.mk t)).mp htClosure'
    have hxClosure : QuotientGroup.mk xK ∈
        (D.frobeniusClosure K L hLK σ').toSubgroup := by
      have hxK : xK = k * t * k⁻¹ := by
        apply Subtype.ext
        dsimp [xK]
        have htxval : t.1 = k.1⁻¹ * x * k.1 := by simpa using htx
        calc
          x = k.1 * (k.1⁻¹ * x * k.1) * k.1⁻¹ := by
            simp [mul_assoc]
          _ = k.1 * t.1 * k.1⁻¹ := by rw [htxval]
      rw [hxK]
      change (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) *
          QuotientGroup.mk t * (QuotientGroup.mk k)⁻¹ ∈ _
      rw [hkq]
      simpa [frobeniusClosure] using hxClosure'
    exact ⟨xK, hxClosure, rfl⟩
  · intro hx
    obtain ⟨t, htClosure, htx⟩ := hx
    let yK : K.field.toSubgroup := ⟨k.1⁻¹ * x * k.1, by
      have htK : t.1 ∈ K.field.toSubgroup := t.2
      rw [← htx]
      exact K.field.toSubgroup.mul_mem
        (K.field.toSubgroup.mul_mem (K.field.toSubgroup.inv_mem k.2) htK) k.2⟩
    have htClosure' : QuotientGroup.mk t ∈
        (closedSubgroupGenerated ({σ'.1} : Set
          (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))).toSubgroup := by
      simpa [frobeniusClosure] using htClosure
    have hyClosure' : QuotientGroup.mk yK ∈
        (closedSubgroupGenerated ({σ.1} : Set
          (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK))).toSubgroup := by
      apply (mem_closedSubgroupGenerated_conjugate_iff
        q σ.1 (QuotientGroup.mk yK)).mpr
      have hyK : k * yK * k⁻¹ = t := by
        apply Subtype.ext
        dsimp [yK]
        simpa [mul_assoc] using htx.symm
      have hyKq : q * QuotientGroup.mk yK * q⁻¹ =
          (QuotientGroup.mk t :
            K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) := by
        rw [← hkq]
        simpa using congrArg
          (fun z : K.field.toSubgroup =>
            (QuotientGroup.mk z :
              K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)) hyK
      rw [hyKq]
      rw [← hσ']
      exact htClosure'
    exact ⟨yK, by simpa [frobeniusClosure] using hyClosure', by simp [yK]⟩

end DegreeData

end actionRemainderAlgebra

section actionRemainderMultiplication

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The left-action translation of `τ₃ = τ₂τ₄`**: conjugation moves to
the second factor and the order reverses ([Yamaguchi 2026, `FrobeniusActionRemainder.lean:320`]
[Yamaguchi2026]). -/
theorem frobeniusActionRemainder_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ₁ σ₂ : D.FrobeniusElements K L hLK) :
    D.frobeniusActionRemainder K L hLK φ (σ₁ * σ₂) =
      D.frobeniusActionRemainder K L hLK φ
          (D.frobeniusActionConjugate K L hLK φ σ₂
            (D.frobeniusExponent K L hLK σ₁)) *
        D.frobeniusActionRemainder K L hLK φ σ₁ := by
  simp [frobeniusActionRemainder, frobeniusExponent_mul,
    frobeniusActionConjugate_coe, frobeniusExponent_actionConjugate,
    frobeniusMul_coe, pow_add, mul_assoc]
  have hp : φ.1 ^ D.frobeniusExponent K L hLK σ₁ *
      φ.1 ^ D.frobeniusExponent K L hLK σ₂ =
      φ.1 ^ D.frobeniusExponent K L hLK σ₂ *
        φ.1 ^ D.frobeniusExponent K L hLK σ₁ := by
    rw [← pow_add, ← pow_add, Nat.add_comm]
  calc
    φ.1 ^ D.frobeniusExponent K L hLK σ₁ *
          (φ.1 ^ D.frobeniusExponent K L hLK σ₂ *
            (σ₂.1⁻¹ * σ₁.1⁻¹)) =
        (φ.1 ^ D.frobeniusExponent K L hLK σ₁ *
          φ.1 ^ D.frobeniusExponent K L hLK σ₂) *
            (σ₂.1⁻¹ * σ₁.1⁻¹) := by rw [mul_assoc]
    _ = (φ.1 ^ D.frobeniusExponent K L hLK σ₂ *
          φ.1 ^ D.frobeniusExponent K L hLK σ₁) *
            (σ₂.1⁻¹ * σ₁.1⁻¹) := by rw [hp]
    _ = φ.1 ^ D.frobeniusExponent K L hLK σ₂ *
          (φ.1 ^ D.frobeniusExponent K L hLK σ₁ *
            (σ₂.1⁻¹ * σ₁.1⁻¹)) := by rw [mul_assoc]

end DegreeData

end actionRemainderMultiplication

section fixedFieldRemainderActions

variable {G : Type} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **On the fixed field of `σ`, the left-action remainder acts exactly
as the `n`-th power of `φ`** ([Yamaguchi 2026, `FrobeniusActionRemainder.lean:368`]
[Yamaguchi2026]). -/
theorem frobeniusActionRemainder_apply_fixedField (D : DegreeData G)
    (A : Rep ℤ G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (a : ambientFixedAddSubgroup A
      (D.frobeniusFixedField K L hLK σ)) :
    D.frobeniusQuotientAction A K.field L hLK
        (D.frobeniusActionRemainder K L hLK φ σ)
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) =
      D.frobeniusQuotientAction A K.field L hLK
        (φ.1 ^ D.frobeniusExponent K L hLK σ)
        (fixedFieldInclusion A (D.frobeniusFixedField K L hLK σ)
          (D.maximalUnramifiedField L)
          (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a) := by
  let aI := fixedFieldInclusion A
    (D.frobeniusFixedField K L hLK σ)
    (D.maximalUnramifiedField L)
    (D.fieldInertia_le_frobeniusFixedField K L hLK σ) a
  let B := D.frobeniusQuotientRepresentation A K.field L hLK
  have hfix : B.ρ σ.1 aI = aI := by
    change D.frobeniusQuotientAction A K.field L hLK σ.1 aI = aI
    exact D.frobeniusQuotientAction_fixedFieldInclusion A K L hLK σ a
  have hinv : B.ρ σ.1⁻¹ aI = aI := by
    calc
      B.ρ σ.1⁻¹ aI = B.ρ σ.1⁻¹ (B.ρ σ.1 aI) := by rw [hfix]
      _ = B.ρ (σ.1⁻¹ * σ.1) aI := by
        rw [map_mul]
        rfl
      _ = aI := by simp
  change B.ρ
      (φ.1 ^ D.frobeniusExponent K L hLK σ * σ.1⁻¹) aI =
    B.ρ (φ.1 ^ D.frobeniusExponent K L hLK σ) aI
  rw [map_mul]
  change B.ρ (φ.1 ^ D.frobeniusExponent K L hLK σ) (B.ρ σ.1⁻¹ aI) =
    B.ρ (φ.1 ^ D.frobeniusExponent K L hLK σ) aI
  rw [hinv]

end DegreeData

end fixedFieldRemainderActions
end

end Atlas.Knowledge
