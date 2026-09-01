import Mathlib
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusFixedField
import Atlas.Knowledge.InertiaQuotientDegreeKernel
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeIndexCardinal

/-!
# coset decomposition for the Frobenius norm identity

The three coset identifications the Frobenius norm-identity lemma sums
over: projection identifies the actual cosets `G_K/G_Σ` with the cosets of
`Γ` in `G(L̃|K)`; at a degree-one lift `φ`, every coset of `Γ` is uniquely
an inertia element followed by one of the first `d_K(σ)` powers of `φ` —
the procyclic degree isomorphism makes `Γ` meet the degree kernel
trivially, and the index count matches; and composing the two with the
inertia-kernel identification enumerates `G_K/G_Σ` by pairs `(τ, i)` with
representatives in the order `φ^i·τ` (#104).

## Main definitions

* `DegreeData.frobeniusFixedCosetClosureEquiv` — `G_K/G_Σ` as the cosets
  of `Γ`.
* `DegreeData.kernelPowerCosetEquiv` — the kernel-times-powers enumeration
  of the cosets of `Γ`.
* `DegreeData.frobeniusNormIdentityCosetEquiv` — the composite
  enumeration, in the `φ^i·τ` order.

## Implementation notes

The reduction arguments run through `ProfiniteInteger.reduction` under the
`NeZero` instance the layer registers on the Frobenius exponent, with the
span identity `span_natCast_eq_ker_reduction` where the source names the
kernel of its bundled reduction, and the degree image is the layer's
`spanAddSubgroup` form of `frobeniusClosureDegree_range`, as in #132.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/- Quotient projection carries the actual cosets `G_K/G_Σ` to the cosets
of `Γ` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:471`]
[Yamaguchi2026]). -/
private noncomputable def frobeniusFixedCosetToClosureCoset
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (K.field.toSubgroup ⧸
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
          K.field.toSubgroup) →
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) :=
  Quotient.map'
    (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK))
    (by
      intro x y hxy
      rw [QuotientGroup.leftRel_apply] at hxy ⊢
      rw [D.subgroupOf_frobeniusFixedField K L hLK σ] at hxy
      exact hxy)

/- The projection of cosets is bijective ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:490`]
[Yamaguchi2026]). -/
private theorem frobeniusFixedCosetToClosureCoset_bijective
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    Function.Bijective
      (D.frobeniusFixedCosetToClosureCoset K L hLK σ) := by
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    apply Quotient.sound'
    rw [QuotientGroup.leftRel_apply]
    rw [D.subgroupOf_frobeniusFixedField K L hLK σ]
    have hrel := QuotientGroup.leftRel_apply.mp (Quotient.exact' hab)
    exact hrel
  · intro z
    refine Quotient.inductionOn' z ?_
    intro q
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
      (D.extensionInertiaWithin K.field L hLK) q
    refine ⟨QuotientGroup.mk k, ?_⟩
    change QuotientGroup.mk
        ((QuotientGroup.mk'
          (D.extensionInertiaWithin K.field L hLK)) k) =
      QuotientGroup.mk q
    rw [hk]

/-- **The actual cosets `G_K/G_Σ` are the cosets of `Γ` in `G(L̃|K)`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:519`]
[Yamaguchi2026]). -/
noncomputable def frobeniusFixedCosetClosureEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (K.field.toSubgroup ⧸
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
          K.field.toSubgroup) ≃
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) :=
  Equiv.ofBijective
    (D.frobeniusFixedCosetToClosureCoset K L hLK σ)
    (D.frobeniusFixedCosetToClosureCoset_bijective K L hLK σ)

/- The procyclic degree isomorphism makes `Γ` meet the degree kernel
trivially ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:535`]
[Yamaguchi2026]). -/
private theorem frobeniusClosure_inf_degreeKernel (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusClosure K L hLK σ).toSubgroup ⊓
        (D.extensionNormalizedDegreeContinuous
          K L hLK).toMonoidHom.ker =
      ⊥ := by
  ext q
  constructor
  · intro hq
    let a : D.frobeniusClosure K L hLK σ := ⟨q, hq.1⟩
    have hclosure : D.frobeniusClosureDegree K L hLK σ a = 1 := hq.2
    have hfixed : D.fixedFieldNormalizedDegree K L hLK σ a = 1 := by
      apply Multiplicative.ext
      apply ProfiniteInteger.nsmul_left_injective
        (D.frobeniusExponent_pos K L hLK σ).ne'
      change D.frobeniusExponent K L hLK σ •
          (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
        D.frobeniusExponent K L hLK σ •
          (1 : ProfiniteIntegerMul).toAdd
      rw [D.frobeniusExponent_nsmul_fixedFieldNormalizedDegree]
      rw [hclosure]
      simp
    have ha : a = 1 :=
      D.frobeniusFixedField_normalizedDegree_injective K L hLK σ (by
        simpa using hfixed)
    exact congrArg Subtype.val ha
  · intro hq
    have : q = 1 := hq
    subst q
    exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩

/- Candidate enumeration of the cosets of `Γ`: an inertia element followed
by one of the first `d_K(σ)` powers of a degree-one Frobenius
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:571`]
[Yamaguchi2026]). -/
private def kernelPowerCosetMap (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ : D.FrobeniusElements K L hLK) :
    (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker ×
        Fin (D.frobeniusExponent K L hLK σ) →
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) :=
  fun p => QuotientGroup.mk (φ.1 ^ p.2.1 * p.1.1)

/- The enumeration is injective ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:582`]
[Yamaguchi2026]). -/
private theorem kernelPowerCosetMap_injective (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    Function.Injective (D.kernelPowerCosetMap K L hLK φ σ) := by
  rintro ⟨h, i⟩ ⟨h', j⟩ hij
  let n := D.frobeniusExponent K L hLK σ
  let dQ := D.extensionNormalizedDegreeContinuous K L hLK
  have hn : 0 < n := D.frobeniusExponent_pos K L hLK σ
  have hdφ : dQ φ.1 =
      Multiplicative.ofAdd (1 : ProfiniteInteger) := by
    change D.extensionNormalizedDegree K L hLK φ.1 = _
    rw [D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ, hφ]
    simp
  have hrel : (φ.1 ^ i.1 * h.1)⁻¹ * (φ.1 ^ j.1 * h'.1) ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup :=
    QuotientGroup.leftRel_apply.mp (Quotient.exact' hij)
  let γ : D.frobeniusClosure K L hLK σ :=
    ⟨(φ.1 ^ i.1 * h.1)⁻¹ * (φ.1 ^ j.1 * h'.1), hrel⟩
  have hdegreeRange :
      (D.frobeniusClosureDegree K L hLK σ γ).toAdd ∈
        ProfiniteInteger.spanAddSubgroup n := by
    have hmem : D.frobeniusClosureDegree K L hLK σ γ ∈
        (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range :=
      ⟨γ, rfl⟩
    rw [D.frobeniusClosureDegree_range K L hLK σ] at hmem
    exact hmem
  have hred : ProfiniteInteger.reduction n
      (D.frobeniusClosureDegree K L hLK σ γ).toAdd = 0 := by
    have hker :
        (D.frobeniusClosureDegree K L hLK σ γ).toAdd ∈
          RingHom.ker (ProfiniteInteger.reduction n) := by
      rw [← ProfiniteInteger.span_natCast_eq_ker_reduction]
      exact hdegreeRange
    exact hker
  have hredOne :
      ProfiniteInteger.reduction n (1 : ProfiniteInteger) = 1 := rfl
  have hmod : (j.1 : ZMod n) - (i.1 : ZMod n) = 0 := by
    have hdh : dQ h.1 = 1 := h.2
    have hdh' : dQ h'.1 = 1 := h'.2
    have hdegMul :
        dQ ((φ.1 ^ i.1 * h.1)⁻¹ * (φ.1 ^ j.1 * h'.1)) =
          (Multiplicative.ofAdd (1 : ProfiniteInteger) ^ i.1)⁻¹ *
            Multiplicative.ofAdd (1 : ProfiniteInteger) ^ j.1 := by
      rw [map_mul, map_inv, map_mul, map_mul, map_pow, map_pow,
        hdφ, hdh, hdh', mul_one, mul_one]
    have hdegAdd := congrArg Multiplicative.toAdd hdegMul
    change (D.frobeniusClosureDegree K L hLK σ γ).toAdd =
      -(i.1 • (1 : ProfiniteInteger)) + j.1 • (1 : ProfiniteInteger)
      at hdegAdd
    rw [hdegAdd] at hred
    rw [map_add, map_neg, map_nsmul, map_nsmul, hredOne] at hred
    simpa [sub_eq_add_neg, add_comm] using hred
  have hijCast : (i.1 : ZMod n) = (j.1 : ZMod n) := by
    exact (sub_eq_zero.mp hmod).symm
  have hijVal : i.1 = j.1 := by
    have hv := congrArg ZMod.val hijCast
    simpa [ZMod.val_natCast_of_lt i.2, ZMod.val_natCast_of_lt j.2]
      using hv
  have hijFin : i = j := Fin.ext hijVal
  subst j
  have hkernel : h.1⁻¹ * h'.1 ∈ dQ.toMonoidHom.ker := by
    have hdh : dQ h.1 = 1 := h.2
    have hdh' : dQ h'.1 = 1 := h'.2
    change dQ (h.1⁻¹ * h'.1) = 1
    rw [map_mul, map_inv, hdh, hdh', inv_one, one_mul]
  have hgamma : h.1⁻¹ * h'.1 ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup := by
    simpa [mul_assoc] using hrel
  have hone : h.1⁻¹ * h'.1 = 1 := by
    have hm : h.1⁻¹ * h'.1 ∈ (⊥ : Subgroup
        (K.field.toSubgroup ⧸
          D.extensionInertiaWithin K.field L hLK)) := by
      rw [← D.frobeniusClosure_inf_degreeKernel K L hLK σ]
      exact ⟨hgamma, hkernel⟩
    exact hm
  have hh : h = h' := by
    apply Subtype.ext
    exact inv_mul_eq_one.mp hone
  subst h'
  rfl

/- The enumeration is bijective, by the index count ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:664`]
[Yamaguchi2026]). -/
private theorem kernelPowerCosetMap_bijective (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    Function.Bijective (D.kernelPowerCosetMap K L hLK φ σ) := by
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let dQ := D.extensionNormalizedDegreeContinuous K L hLK
  let H : Subgroup Q := dQ.toMonoidHom.ker
  let Γ : Subgroup Q := (D.frobeniusClosure K L hLK σ).toSubgroup
  let n := D.frobeniusExponent K L hLK σ
  let j := D.extensionDegreeKernelRestriction K L hLK
  letI : Finite H :=
    Finite.of_injective j
      (D.extensionDegreeKernelRestriction_injective K L hLK)
  letI : Finite (Q ⧸ Γ) := by
    simpa [Q, Γ] using D.frobeniusFixedField_finiteIndex K L hLK σ
  have hΓmap : Γ.map dQ.toMonoidHom =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range := by
    ext z
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q.1, q.2, rfl⟩
  have htopmap : (⊤ : Subgroup Q).map dQ.toMonoidHom = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨q, hq⟩ :=
      D.extensionNormalizedDegreeContinuous_surjective K L hLK z
    exact ⟨q, trivial, hq⟩
  have himage : (Γ.map dQ.toMonoidHom).relIndex
      ((⊤ : Subgroup Q).map dQ.toMonoidHom) = n := by
    rw [hΓmap, htopmap, Subgroup.relIndex_top_right,
      D.frobeniusClosureDegree_range K L hLK σ,
      AddSubgroup.index_toSubgroup,
      ProfiniteInteger.index_span_natCast]
  have hkernel : (Γ ⊓ dQ.toMonoidHom.ker).relIndex
      ((⊤ : Subgroup Q) ⊓ dQ.toMonoidHom.ker) = Nat.card H := by
    rw [show Γ ⊓ dQ.toMonoidHom.ker = ⊥ by
      simpa [Γ, dQ, Q] using
        D.frobeniusClosure_inf_degreeKernel K L hLK σ]
    rw [top_inf_eq]
    change (⊥ : Subgroup Q).relIndex H = Nat.card H
    rw [Subgroup.relIndex_bot_left]
  have hindex : Γ.index = n * Nat.card H := by
    rw [← Subgroup.relIndex_top_right]
    rw [relIndex_eq_map_relIndex_mul_inf_ker_relIndex
      dQ.toMonoidHom le_top, himage, hkernel]
  have hcard :
      Nat.card (H × Fin n) = Nat.card (Q ⧸ Γ) := by
    calc
      Nat.card (H × Fin n) =
          Nat.card H * Nat.card (Fin n) := Nat.card_prod _ _
      _ = Nat.card H * n := by
        have hfin : Nat.card (Fin n) = n := by
          calc
            Nat.card (Fin n) = Fintype.card (Fin n) :=
              Nat.card_eq_fintype_card
            _ = n := Fintype.card_fin n
        rw [hfin]
      _ = n * Nat.card H := Nat.mul_comm _ _
      _ = Γ.index := hindex.symm
      _ = Nat.card (Q ⧸ Γ) := Subgroup.index_eq_card Γ
  apply (Nat.bijective_iff_injective_and_card
    (D.kernelPowerCosetMap K L hLK φ σ)).2
  exact ⟨D.kernelPowerCosetMap_injective K L hLK φ σ hφ,
    by simpa [H, n, Q, Γ, dQ] using hcard⟩

/-- **The kernel-times-powers enumeration of the cosets of `Γ`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:740`]
[Yamaguchi2026]). -/
noncomputable def kernelPowerCosetEquiv (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker ×
        Fin (D.frobeniusExponent K L hLK σ) ≃
      ((K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) ⧸
        (D.frobeniusClosure K L hLK σ).toSubgroup) :=
  Equiv.ofBijective (D.kernelPowerCosetMap K L hLK φ σ)
    (D.kernelPowerCosetMap_bijective K L hLK φ σ hφ)

/- Explicit version of the decomposition, with representatives in the
order `φ^i·τ` occurring in `φ_n ∘ N` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:759`]
[Yamaguchi2026]). -/
private noncomputable def frobeniusNormIdentityCosetMap
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ : D.FrobeniusElements K L hLK) :
    ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K.field).toSubgroup) ×
        Fin (D.frobeniusExponent K L hLK σ) →
      (K.field.toSubgroup ⧸
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
          K.field.toSubgroup) :=
  fun p =>
    let kφ : K.field.toSubgroup := Quotient.out (φ.1 ^ p.2.1)
    let kI : (D.maximalUnramifiedField K.field).toSubgroup :=
      Quotient.out p.1
    QuotientGroup.mk (kφ * (⟨kI.1, kI.2.1⟩ : K.field.toSubgroup))

/- The explicit decomposition commutes with the projections
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:778`]
[Yamaguchi2026]). -/
private theorem frobeniusNormIdentityCosetMap_commutes (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ σ : D.FrobeniusElements K L hLK)
    (p : ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K.field).toSubgroup) ×
      Fin (D.frobeniusExponent K L hLK σ)) :
    D.frobeniusFixedCosetToClosureCoset K L hLK σ
        (D.frobeniusNormIdentityCosetMap K L hLK φ σ p) =
      D.kernelPowerCosetMap K L hLK φ σ
        (D.inertiaQuotientDegreeKernelEquiv K L hLK p.1, p.2) := by
  let kφ : K.field.toSubgroup := Quotient.out (φ.1 ^ p.2.1)
  let kI : (D.maximalUnramifiedField K.field).toSubgroup :=
    Quotient.out p.1
  let kIK : K.field.toSubgroup := ⟨kI.1, kI.2.1⟩
  have hkφ : (QuotientGroup.mk'
      (D.extensionInertiaWithin K.field L hLK)) kφ = φ.1 ^ p.2.1 :=
    Quotient.out_eq' (φ.1 ^ p.2.1)
  have hkI :
      (D.inertiaQuotientDegreeKernelEquiv K L hLK p.1).1 =
        (QuotientGroup.mk'
          (D.extensionInertiaWithin K.field L hLK)) kIK := by
    calc
      (D.inertiaQuotientDegreeKernelEquiv K L hLK p.1).1 =
          (D.inertiaQuotientDegreeKernelEquiv K L hLK
            (QuotientGroup.mk kI)).1 := by
        exact congrArg
          (fun r => (D.inertiaQuotientDegreeKernelEquiv K L hLK r).1)
          (Quotient.out_eq' p.1).symm
      _ = _ := rfl
  change QuotientGroup.mk
      ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK))
        (kφ * kIK)) =
    QuotientGroup.mk
      (φ.1 ^ p.2.1 *
        (D.inertiaQuotientDegreeKernelEquiv K L hLK p.1).1)
  rw [map_mul, hkφ, hkI]

/- The explicit decomposition is bijective ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:819`]
[Yamaguchi2026]). -/
private theorem frobeniusNormIdentityCosetMap_bijective (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    Function.Bijective
      (D.frobeniusNormIdentityCosetMap K L hLK φ σ) := by
  let eI := D.inertiaQuotientDegreeKernelEquiv K L hLK
  let eP := D.kernelPowerCosetEquiv K L hLK φ σ hφ
  let eSigma := D.frobeniusFixedCosetClosureEquiv K L hLK σ
  have hinj :
      Function.Injective
        (D.frobeniusNormIdentityCosetMap K L hLK φ σ) := by
    intro p q hpq
    apply (Equiv.prodCongr eI (Equiv.refl _)).injective
    apply eP.injective
    calc
      eP (eI p.1, p.2) =
          eSigma (D.frobeniusNormIdentityCosetMap K L hLK φ σ p) :=
        (D.frobeniusNormIdentityCosetMap_commutes K L hLK φ σ p).symm
      _ = eSigma (D.frobeniusNormIdentityCosetMap K L hLK φ σ q) :=
        congrArg eSigma hpq
      _ = eP (eI q.1, q.2) :=
        D.frobeniusNormIdentityCosetMap_commutes K L hLK φ σ q
  have hsurj :
      Function.Surjective
        (D.frobeniusNormIdentityCosetMap K L hLK φ σ) := by
    intro q
    obtain ⟨p, hp⟩ := eP.surjective (eSigma q)
    obtain ⟨r, hr⟩ := (Equiv.prodCongr eI (Equiv.refl _)).surjective p
    refine ⟨r, ?_⟩
    apply eSigma.injective
    calc
      eSigma (D.frobeniusNormIdentityCosetMap K L hLK φ σ r) =
          eP (eI r.1, r.2) :=
        D.frobeniusNormIdentityCosetMap_commutes K L hLK φ σ r
      _ = eP p := by
        apply congrArg eP
        exact hr
      _ = eSigma q := hp
  exact ⟨hinj, hsurj⟩

/-- **The composite enumeration of `G_K/G_Σ` by pairs, in the `φ^i·τ`
order** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/CoreFrobeniusNorm.lean:862`]
[Yamaguchi2026]). -/
noncomputable def frobeniusNormIdentityCosetEquiv (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ σ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K.field).toSubgroup) ×
        Fin (D.frobeniusExponent K L hLK σ) ≃
      (K.field.toSubgroup ⧸
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
          K.field.toSubgroup) :=
  Equiv.ofBijective (D.frobeniusNormIdentityCosetMap K L hLK φ σ)
    (D.frobeniusNormIdentityCosetMap_bijective K L hLK φ σ hφ)

end DegreeData

end

end Atlas.Knowledge
