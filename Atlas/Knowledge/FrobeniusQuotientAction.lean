import Mathlib
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.RelativeNormLaws

/-!
# Frobenius quotient action

The actual action of `G(L̃|K)` on `A_{L̃}`: the normal-extension action of
`G_K` descends through the relative inertia, since the maximal unramified
extension's subgroup is normal there. Conjugation by `G_K` permutes the
cosets of `G(L̃|K̃)`, so the relative norm `N_{L̃|K̃}` is equivariant for
the descended action, and the operator `φ_n = 1 + φ + ⋯ + φ^{n-1}` is its
additive power sum (#104).

## Main definitions

* `DegreeData.frobeniusQuotientAction` — the `G(L̃|K)`-action on `A_{L̃}`.
* `DegreeData.frobeniusPowerSum` — the additive power-sum operator `φ_n`.

## Main statements

* `DegreeData.relativeNorm_frobeniusQuotientAction` — the norm commutes
  with the quotient action, after including into the upper fixed field;
  proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, with
the maximal-unramified identities under their `subgroupOf_` names. The
source pins the acting group to the shared `Rep` universe boundary; this
Mathlib's `Rep` is polymorphic, so the action generalizes to any universe,
as across the arc. The source's simp attribute on the private
coset-permutation rule is dropped — its one use is an explicit rewrite,
and a private lemma still enters the global simp set.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The actual action of `G(L̃|K)` on `A_{L̃}`** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:178`]
[Yamaguchi2026]). -/
def frobeniusQuotientAction (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ambientFixedAddSubgroup A (D.maximalUnramifiedField L) :=
  Quotient.liftOn' q
    (fun k : K.toSubgroup =>
      normalExtensionAction A K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK)
        (D.subgroupOf_maximalUnramifiedField_normal K L hLK) k a)
    (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy
      rw [← D.subgroupOf_maximalUnramifiedField K L hLK] at hxy
      let l : (D.maximalUnramifiedField L).toSubgroup :=
        ⟨x.1⁻¹ * y.1, hxy⟩
      have hy : y = x * Subgroup.inclusion
          (D.maximalUnramifiedField_le_of_le hLK) l := by
        apply Subtype.ext
        simp [l]
      apply Subtype.ext
      change A.ρ x.1 a.1 = A.ρ y.1 a.1
      rw [hy]
      change A.ρ x.1 a.1 = A.ρ (x.1 * l.1) a.1
      rw [map_mul]
      change A.ρ x.1 a.1 = A.ρ x.1 (A.ρ l.1 a.1)
      rw [a.2 l])

/-- The quotient action computes on representatives through the
normal-extension action. -/
@[simp]
theorem frobeniusQuotientAction_mk (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    D.frobeniusQuotientAction A K L hLK (QuotientGroup.mk k) a =
      normalExtensionAction A K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK)
        (D.subgroupOf_maximalUnramifiedField_normal K L hLK) k a :=
  rfl

/- Conjugation by an element of `G_K` preserves the inertia group `I_K`;
the inverse convention makes the coset permutation rewrite `τ·φ` as
`φ·(φ⁻¹τφ)` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:227`]
[Yamaguchi2026]). -/
private def inertiaConjugationEquiv (D : DegreeData G)
    (K : ClosedSubgroup G) (k : K.toSubgroup) :
    (D.maximalUnramifiedField K).toSubgroup ≃
      (D.maximalUnramifiedField K).toSubgroup where
  toFun x := ⟨k.1⁻¹ * x.1 * k.1, ⟨by
    exact K.toSubgroup.mul_mem
      (K.toSubgroup.mul_mem (K.toSubgroup.inv_mem k.2) x.2.1) k.2, by
    change D.degree (k.1⁻¹ * x.1 * k.1) = 1
    have hx : D.degree x.1 = 1 := x.2.2
    rw [map_mul, map_mul, map_inv, hx]
    simp⟩⟩
  invFun x := ⟨k.1 * x.1 * k.1⁻¹, ⟨by
    exact K.toSubgroup.mul_mem
      (K.toSubgroup.mul_mem k.2 x.2.1) (K.toSubgroup.inv_mem k.2), by
    change D.degree (k.1 * x.1 * k.1⁻¹) = 1
    have hx : D.degree x.1 = 1 := x.2.2
    rw [map_mul, map_mul, map_inv, hx]
    simp⟩⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]

/- Conjugation by `G_K` preserves `I_L` when `L | K` is Galois
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:253`]
[Yamaguchi2026]). -/
private theorem conjugate_mem_maximalUnramifiedField (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup) (l : (D.maximalUnramifiedField L).toSubgroup) :
    k.1⁻¹ * l.1 * k.1 ∈ (D.maximalUnramifiedField L).toSubgroup := by
  let lK : K.toSubgroup := ⟨l.1, hLK l.2.1⟩
  have hcK : k⁻¹ * lK * k ∈ L.toSubgroup.subgroupOf K.toSubgroup := by
    simpa [lK] using hLnormal.conj_mem lK l.2.1 k⁻¹
  refine ⟨?_, ?_⟩
  · exact hcK
  · change D.degree (k.1⁻¹ * l.1 * k.1) = 1
    have hlDegree : D.degree l.1 = 1 := l.2.2
    rw [map_mul, map_mul, map_inv, hlDegree]
    simp

/- The coset permutation `τ ↦ φ⁻¹τφ` of `G(L̃|K̃)` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:270`]
[Yamaguchi2026]). -/
private noncomputable def inertiaConjugationCosetEquiv (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup) :
    ((D.maximalUnramifiedField K).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K).toSubgroup) ≃
      ((D.maximalUnramifiedField K).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K).toSubgroup) :=
  Quotient.congr (D.inertiaConjugationEquiv K k) (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    constructor
    · intro hxy
      let l : (D.maximalUnramifiedField L).toSubgroup :=
        ⟨x.1⁻¹ * y.1, hxy⟩
      have hl := D.conjugate_mem_maximalUnramifiedField K L hLK k l
      change (k.1⁻¹ * x.1 * k.1)⁻¹ * (k.1⁻¹ * y.1 * k.1) ∈
        (D.maximalUnramifiedField L).toSubgroup
      simpa [l, mul_assoc] using hl
    · intro hxy
      let l : (D.maximalUnramifiedField L).toSubgroup :=
        ⟨(k.1⁻¹ * x.1 * k.1)⁻¹ * (k.1⁻¹ * y.1 * k.1), hxy⟩
      have hl := D.conjugate_mem_maximalUnramifiedField K L hLK k⁻¹ l
      change x.1⁻¹ * y.1 ∈ (D.maximalUnramifiedField L).toSubgroup
      simpa [l, mul_assoc] using hl)

private theorem inertiaConjugationCosetEquiv_mk (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup) (x : (D.maximalUnramifiedField K).toSubgroup) :
    D.inertiaConjugationCosetEquiv K L hLK k (QuotientGroup.mk x) =
      QuotientGroup.mk (D.inertiaConjugationEquiv K k x) :=
  rfl

/- Conjugation intertwines the coset action with the normalizing action
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:309`]
[Yamaguchi2026]). -/
private theorem relativeCosetAction_inertiaConjugation (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (r : (D.maximalUnramifiedField K).toSubgroup ⧸
      (D.maximalUnramifiedField L).toSubgroup.subgroupOf
        (D.maximalUnramifiedField K).toSubgroup) :
    relativeCosetAction A (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (normalExtensionAction A K (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_le_of_le hLK)
          (D.subgroupOf_maximalUnramifiedField_normal K L hLK) k a) r =
      A.ρ k.1
        (relativeCosetAction A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          a (D.inertiaConjugationCosetEquiv K L hLK k r)) := by
  refine Quotient.inductionOn' r ?_
  intro x
  rw [relativeCosetAction_mk, D.inertiaConjugationCosetEquiv_mk,
    relativeCosetAction_mk, normalExtensionAction_coe]
  calc
    A.ρ x.1 (A.ρ k.1 a.1) = A.ρ (x.1 * k.1) a.1 := by
      rw [map_mul]
      rfl
    _ = A.ρ (k.1 * (k.1⁻¹ * x.1 * k.1)) a.1 := by
      simp [mul_assoc]
    _ = A.ρ k.1 (A.ρ (k.1⁻¹ * x.1 * k.1) a.1) := by
      rw [map_mul]
      rfl

/- The norm `N_{L̃|K̃}` is equivariant for the normalizing `G_K`-action
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:344`]
[Yamaguchi2026]). -/
private theorem relativeNorm_normalizingAction (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [Finite ((D.maximalUnramifiedField K).toSubgroup ⧸
      (D.maximalUnramifiedField L).toSubgroup.subgroupOf
        (D.maximalUnramifiedField K).toSubgroup)]
    (k : K.toSubgroup)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ((relativeNorm A (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      (normalExtensionAction A K (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_le_of_le hLK)
        (D.subgroupOf_maximalUnramifiedField_normal K L hLK) k a) :
      ambientFixedAddSubgroup A (D.maximalUnramifiedField K)) : A.V) =
      A.ρ k.1
        ((relativeNorm A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) a :
          ambientFixedAddSubgroup A (D.maximalUnramifiedField K)) :
          A.V) := by
  let R := (D.maximalUnramifiedField K).toSubgroup ⧸
    (D.maximalUnramifiedField L).toSubgroup.subgroupOf
      (D.maximalUnramifiedField K).toSubgroup
  let e := D.inertiaConjugationCosetEquiv K L hLK k
  letI := Fintype.ofFinite R
  simp only [relativeNorm_apply_coe, relativeNormValue]
  calc
    ∑ r : R, relativeCosetAction A (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (normalExtensionAction A K (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_le_of_le hLK)
          (D.subgroupOf_maximalUnramifiedField_normal K L hLK) k a) r =
      ∑ r : R, A.ρ k.1
        (relativeCosetAction A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          a (e r)) := by
      apply Finset.sum_congr rfl
      intro r _
      exact D.relativeCosetAction_inertiaConjugation A K L hLK k a r
    _ = A.ρ k.1
        (∑ r : R, relativeCosetAction A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          a (e r)) := by
      rw [map_sum]
    _ = A.ρ k.1
        (∑ r : R, relativeCosetAction A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          a r) := by
      rw [e.sum_comp]

/-- **The relative norm commutes with the Frobenius quotient action**,
after including the norm into the upper fixed field ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:397`]
[Yamaguchi2026]). -/
theorem relativeNorm_frobeniusQuotientAction (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [Finite ((D.maximalUnramifiedField K).toSubgroup ⧸
      (D.maximalUnramifiedField L).toSubgroup.subgroupOf
        (D.maximalUnramifiedField K).toSubgroup)]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ((relativeNorm A (D.maximalUnramifiedField K)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      (D.frobeniusQuotientAction A K L hLK q a) :
      ambientFixedAddSubgroup A (D.maximalUnramifiedField K)) : A.V) =
      ((D.frobeniusQuotientAction A K L hLK q
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)
            a)) : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
        A.V) := by
  let k : K.toSubgroup := Quotient.out q
  have hq : q = QuotientGroup.mk k := (Quotient.out_eq' q).symm
  rw [hq]
  exact D.relativeNorm_normalizingAction A K L hLK k a

/-- **The additive power-sum operator** `φ_n = 1 + φ + ⋯ + φ^{n-1}`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:424`]
[Yamaguchi2026]). -/
def frobeniusPowerSum (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ambientFixedAddSubgroup A (D.maximalUnramifiedField L) :=
  ∑ i : Fin n, D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a

/-- The power sum reads as the sum of the actions on coefficients
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:439`]
[Yamaguchi2026]). -/
@[simp]
theorem frobeniusPowerSum_coe (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    ((D.frobeniusPowerSum A K L hLK φ n a :
      ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) : A.V) =
      ∑ i : Fin n,
        (D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a : A.V) := by
  change (ambientFixedAddSubgroup A
      (D.maximalUnramifiedField L)).subtype
    (∑ i : Fin n,
      D.frobeniusQuotientAction A K L hLK (φ ^ i.1) a) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

end DegreeData

end

end Atlas.Knowledge
