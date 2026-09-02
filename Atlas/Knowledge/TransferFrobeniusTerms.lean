import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.DoubleCosetOrbitGeometry
import Atlas.Knowledge.FiniteReciprocityNaturalityNorm
import Atlas.Knowledge.FiniteResidueAbstractExtension
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusFixedField
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.RelativeNormDoubleCoset
import Atlas.Knowledge.TopologicalGeneration
import Atlas.Knowledge.TransferNormFrobeniusGeometry
import Atlas.Knowledge.TransferOrbitClosure

/-!
# Transfer Frobenius terms

The Frobenius factors of the transfer formula: each transfer double
coset contributes the element `τ⁻¹σ^{f(τ)}τ` of the intermediate copy,
pulled back to a genuine positive Frobenius lift over `K'`; the lift's
closed subgroup, fixed subgroup, and quotient fiber are identified with
the corresponding norm-side data, and the relative norm is the double
sum over norm double cosets at the chosen representatives (#104).

## Main definitions

* `DegreeData.transferNormNaturalityFrobeniusIntermediateEquiv` — the
  two realizations of `G(L̃|K')` identified.
* `DegreeData.transferNormNaturalityFrobeniusTransferTerm` — the
  transfer term.
* `DegreeData.transferNormNaturalityFrobeniusTransferTermPreimage` —
  its pullback.
* `DegreeData.transferNormNaturalityTransferFrobeniusLift` — the
  transfer Frobenius lift.

## Main statements

* `DegreeData.transferNormNaturality_profiniteInteger_positive_nat_of_nsmul_eq_nat`
  — the divisibility fact behind positivity; proved.
* `DegreeData.transferNormNaturalityFrobeniusTransferTermPreimage_degree`
  — each pullback has positive integral degree; proved.
* `DegreeData.transferNormNaturalityTransferFrobeniusLift_towerMap` —
  the lift maps to the transfer term; proved.
* `DegreeData.transferNormNaturalityTransferFrobeniusLift_closure_map`
  — closed subgroups correspond; proved.
* `DegreeData.transferNormNaturalityTransferFrobeniusLift_mem_fixedSubgroup_iff_stabilizer`
  — fixed subgroup as stabilizer; proved.
* `DegreeData.transferNormNaturalityTransferFrobeniusLift_fixedSubgroup_map`
  — the literal subgroup equality; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
with `Subgroup.mem_subgroupOf` for the source's membership rule and the
layer's `subgroupOf_frobeniusFixedField` for its fixed-field form. The
whole file stays at `Type u` — nothing here pins the orbit-norm
section, so it generalizes the source's universe device. The
divisibility fact is restated over the layer's `ProfiniteInteger` — its
name swaps the source's `zHat` accordingly — and its proof becomes a
direct computation with `ProfiniteInteger.reduction`, the source's
bundled multiplication-by-`f` homomorphism having no layer counterpart;
`ProfiniteInteger.nsmul_left_injective` closes it. The stabilizer-iff
call site drops its two containments and sheds the dead local it fed,
the layer's form being containment-free, and the dead-binder sweep runs
to the lint's fixpoint: eight declarations shed
`[IsTopologicalGroup G]` and eight `[T2Space G]`, all simply unused. The source's
`Internal` namespace is flattened — the layer keeps everything in one
namespace — and four of its five private helpers turn public: the file
split puts their consumers in the next brick, and `private` does not
cross files; the orbit-representative sum stays private. The citations
name this file by bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/` in the source. The
source's namespace `open`s go, while `open MulAction` stays for the
orbit vocabulary.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

open MulAction

section transferFrobeniusGeometry

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The chosen representative of a norm orbit: the inverse of the
corresponding transfer orbit's representative
([Yamaguchi 2026, `MainTransferFrobenius.lean:35`][Yamaguchi2026]). -/
noncomputable def chosenTransferNormNaturalityNormOrbitRepresentative
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (qN : Quotient (orbitRel
      (E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
      (E.base.field.toSubgroup ⧸
          (D.frobeniusFixedField E.base L (hL.trans E.below) σ).toSubgroup.subgroupOf
              E.base.field.toSubgroup))) :
    E.base.field.toSubgroup ⧸
        (D.frobeniusFixedField E.base L (hL.trans E.below) σ).toSubgroup.subgroupOf
            E.base.field.toSubgroup :=
  let qT := (D.transferNormNaturalityTransferNormOrbitEquiv
    E L hL σ).symm qN
  QuotientGroup.mk (Quotient.out qT.out.out)⁻¹

/-- The chosen representative represents its orbit
([Yamaguchi 2026, `MainTransferFrobenius.lean:56`][Yamaguchi2026]). -/
theorem chosenTransferNormNaturalityNormOrbitRepresentative_spec
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below)) :
    Function.LeftInverse Quotient.mk''
      (chosenTransferNormNaturalityNormOrbitRepresentative
        D E L hL σ) := by
  intro qN
  let orbitEquiv := D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ
  let qT := orbitEquiv.symm qN
  change Quotient.mk'' (QuotientGroup.mk (Quotient.out qT.out.out)⁻¹) = qN
  rw [← D.transferNormNaturalityTransferNormOrbitEquiv_apply
    E L hL σ qT]
  exact orbitEquiv.apply_symm_apply qN

end transferFrobeniusGeometry

section transferOrbitNorms

variable {G : Type u} [Group G] [TopologicalSpace G]

/- The relative norm as the double sum over norm double cosets and
stabilizer cosets, at the chosen representatives
([Yamaguchi 2026, `MainTransferFrobenius.lean:93`][Yamaguchi2026]). -/
private theorem transferNormNaturalityNorm_eq_sum_transferOrbitRepresentatives
    (D : DegreeData G) (A : Rep ℤ G)
    [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    [hLfinite : Finite (E.base.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf E.base.field.toSubgroup)]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (π : ambientFixedAddSubgroup A
      (D.frobeniusFixedField E.base L (hL.trans E.below) σ)) :
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
    let M := E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup
    let Ω := Quotient (orbitRel M
      (E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup))
    let φ : Ω → E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup :=
      chosenTransferNormNaturalityNormOrbitRepresentative
        D E L hL σ
    letI : Finite (E.base.field.toSubgroup ⧸
        S.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
      D.frobeniusFixedField_finite E.base L (hL.trans E.below) σ
    letI : Fintype Ω := Fintype.ofFinite _
    letI (q : Ω) : Fintype (M ⧸ stabilizer M (φ q)) := by
      letI : Finite (orbit M (φ q)) :=
        Finite.of_injective Subtype.val Subtype.val_injective
      letI := Fintype.ofFinite (orbit M (φ q))
      exact Fintype.ofEquiv (orbit M (φ q))
        (orbitEquivQuotientStabilizer M (φ q))
    ((relativeNorm A E.base.field S hSK π :
      ambientFixedAddSubgroup A E.base.field) : A.V) =
      ∑ q : Ω, ∑ r : M ⧸ stabilizer M (φ q),
        relativeCosetAction A E.base.field S hSK π (r.out • φ q) := by
  dsimp only
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let M := E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup
  let Ω := Quotient (orbitRel M
    (E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup))
  let φ : Ω → E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup :=
    chosenTransferNormNaturalityNormOrbitRepresentative
      D E L hL σ
  letI : Finite (E.base.field.toSubgroup ⧸
      S.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
    D.frobeniusFixedField_finite E.base L (hL.trans E.below) σ
  letI : Fintype Ω := Fintype.ofFinite _
  letI (q : Ω) : Fintype (M ⧸ stabilizer M (φ q)) := by
    letI : Finite (orbit M (φ q)) :=
      Finite.of_injective Subtype.val Subtype.val_injective
    letI := Fintype.ofFinite (orbit M (φ q))
    exact Fintype.ofEquiv (orbit M (φ q))
      (orbitEquivQuotientStabilizer M (φ q))
  rw [relativeNorm_eq_sum_chosenOrbit_of_fintype A E.base.field S hSK M
    (chosenTransferNormNaturalityNormOrbitRepresentative_spec
      D E L hL σ) π]
  apply Fintype.sum_congr
  intro q
  apply Fintype.sum_congr
  intro r
  rw [chosenOrbitClassEquiv_symm_apply]

end transferOrbitNorms

section transferFrobeniusFibers

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The canonical identification of the two realizations of
`G(L̃|K')`**
([Yamaguchi 2026, `MainTransferFrobenius.lean:168`][Yamaguchi2026]). -/
noncomputable def transferNormNaturalityFrobeniusIntermediateEquiv
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal] :
    (E.field.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L hL) ≃*
      D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL :=
  MulEquiv.ofBijective
    (D.finiteReciprocityNaturalityFrobeniusTowerMap
      E.base.field E.field.field L L
      (hL.trans E.below) hL E.below le_rfl).rangeRestrict
    ⟨fun _ _ h => D.transferNormNaturalityFrobeniusTowerMap_injective
        E L hL (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

/-- The identification evaluates by inclusion on representatives
([Yamaguchi 2026, `MainTransferFrobenius.lean:191`][Yamaguchi2026]). -/
@[simp]
theorem transferNormNaturalityFrobeniusIntermediateEquiv_mk
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (k' : E.field.field.toSubgroup) :
    (D.transferNormNaturalityFrobeniusIntermediateEquiv
      E L hL (QuotientGroup.mk k')).1 =
      QuotientGroup.mk (Subgroup.inclusion E.below k') := rfl

/-- **A divisibility fact in `ℤ̂`** recognizing every transfer term as a
positive Frobenius element over `K'`
([Yamaguchi 2026, `MainTransferFrobenius.lean:205`][Yamaguchi2026]). -/
theorem transferNormNaturality_profiniteInteger_positive_nat_of_nsmul_eq_nat
    (f N : ℕ) (hf : 0 < f) (hN : 0 < N) (z : ProfiniteInteger)
    (h : f • z = N • (1 : ProfiniteInteger)) :
    ∃ n : ℕ, 0 < n ∧ z = n • (1 : ProfiniteInteger) := by
  letI : NeZero f := ⟨hf.ne'⟩
  have hmod : (N : ZMod f) = 0 := by
    have hz : ProfiniteInteger.reduction f (f • z) = 0 := by
      rw [map_nsmul]
      simp [nsmul_eq_mul]
    rw [h, map_nsmul, map_one] at hz
    simpa [nsmul_eq_mul] using hz
  have hdiv : f ∣ N := (ZMod.natCast_eq_zero_iff N f).1 hmod
  let n := N / f
  have hN_eq : N = f * n := (Nat.mul_div_cancel' hdiv).symm
  have hn : 0 < n := Nat.div_pos (Nat.le_of_dvd hN hdiv) hf
  refine ⟨n, hn, ?_⟩
  apply ProfiniteInteger.nsmul_left_injective hf.ne'
  change f • z = f • (n • (1 : ProfiniteInteger))
  rw [h, smul_smul, ← hN_eq]

/-- **The element `τ⁻¹σ^{f(τ)}τ` of `H` attached to one double coset in
the transfer formula on `G(L̃|K)`**
([Yamaguchi 2026, `MainTransferFrobenius.lean:235`][Yamaguchi2026]). -/
noncomputable def transferNormNaturalityFrobeniusTransferTerm
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL := by
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  exact ⟨q.out.out⁻¹ * σ.1 ^ Function.minimalPeriod (σ.1 • ·) q.out *
      q.out.out,
    QuotientGroup.out_conj_pow_minimalPeriod_mem H σ.1 q.out⟩

/-- **The transfer term pulled back from `H` to `G(L̃|K')`**
([Yamaguchi 2026, `MainTransferFrobenius.lean:256`][Yamaguchi2026]). -/
noncomputable def transferNormNaturalityFrobeniusTransferTermPreimage
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    E.field.field.toSubgroup ⧸ D.extensionInertiaWithin E.field.field L hL :=
  (D.transferNormNaturalityFrobeniusIntermediateEquiv E L hL).symm
    (D.transferNormNaturalityFrobeniusTransferTerm E L hL σ q)

/-- **The pullback of each double-coset term has strictly positive
integral normalized degree**
([Yamaguchi 2026, `MainTransferFrobenius.lean:275`][Yamaguchi2026]). -/
theorem transferNormNaturalityFrobeniusTransferTermPreimage_degree
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    ∃ n : ℕ, 0 < n ∧
      D.extensionNormalizedDegree E.field L hL
        (D.transferNormNaturalityFrobeniusTransferTermPreimage
          E L hL σ q) =
          (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^ n := by
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  letI : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  letI := H.fintypeQuotientOfFiniteIndex
  let m := Function.minimalPeriod (σ.1 • ·) q.out
  let N := m * D.frobeniusExponent E.base L (hL.trans E.below) σ
  let u := D.transferNormNaturalityFrobeniusTransferTermPreimage
    E L hL σ q
  let f := (E.residueDegree : ℕ)
  letI : Finite (orbit (Subgroup.zpowers σ.1) q.out) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hf : 0 < f := E.residueDegree.property
  have hm : 0 < m := by
    have hm0 : Function.minimalPeriod (σ.1 • ·) q.out ≠ 0 :=
      NeZero.ne _
    simpa [m] using Nat.pos_of_ne_zero hm0
  have hN : 0 < N := Nat.mul_pos hm
    (D.frobeniusExponent_pos E.base L (hL.trans E.below) σ)
  have hu :
      D.finiteReciprocityNaturalityFrobeniusTowerMap
          E.base.field E.field.field L L
          (hL.trans E.below) hL E.below le_rfl u =
        (D.transferNormNaturalityFrobeniusTransferTerm
          E L hL σ q).1 := by
    exact congrArg Subtype.val
      ((D.transferNormNaturalityFrobeniusIntermediateEquiv
        E L hL).apply_symm_apply
          (D.transferNormNaturalityFrobeniusTransferTerm
            E L hL σ q))
  have hconj :
      D.extensionNormalizedDegree E.base L (hL.trans E.below)
          (D.transferNormNaturalityFrobeniusTransferTerm
            E L hL σ q).1 =
        D.extensionNormalizedDegree E.base L (hL.trans E.below)
          (σ.1 ^ m) := by
    change D.extensionNormalizedDegree E.base L (hL.trans E.below)
        (q.out.out⁻¹ * σ.1 ^ m * q.out.out) = _
    rw [map_mul, map_mul, map_inv]
    simp [mul_comm]
  have hdegree : f •
      (D.extensionNormalizedDegree E.field L hL u).toAdd =
        N • (1 : ProfiniteInteger) := by
    calc
      f • (D.extensionNormalizedDegree E.field L hL u).toAdd =
          (D.extensionNormalizedDegree E.base L (hL.trans E.below)
            (D.finiteReciprocityNaturalityFrobeniusTowerMap
              E.base.field E.field.field L L
              (hL.trans E.below) hL E.below le_rfl u)).toAdd := by
        symm
        exact D.finiteReciprocityNaturalityFrobeniusTowerMap_degree
          E L L (hL.trans E.below) hL le_rfl u
      _ = (D.extensionNormalizedDegree E.base L (hL.trans E.below)
          (σ.1 ^ m)).toAdd := by rw [hu, hconj]
      _ = N • (1 : ProfiniteInteger) := by
        rw [map_pow,
          D.extensionNormalizedDegree_frobenius_eq_pow
            E.base L (hL.trans E.below) σ]
        change m •
            (D.frobeniusExponent E.base L (hL.trans E.below) σ •
              (1 : ProfiniteInteger)) = N • (1 : ProfiniteInteger)
        rw [smul_smul]
  obtain ⟨n, hn, hnEq⟩ :=
    transferNormNaturality_profiniteInteger_positive_nat_of_nsmul_eq_nat f N hf hN
      (D.extensionNormalizedDegree E.field L hL u).toAdd hdegree
  refine ⟨n, hn, ?_⟩
  apply Multiplicative.ext
  exact hnEq

/-- **The Frobenius lift over `K'` represented by one term of the
transfer product**
([Yamaguchi 2026, `MainTransferFrobenius.lean:363`][Yamaguchi2026]). -/
noncomputable def transferNormNaturalityTransferFrobeniusLift
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    D.FrobeniusElements E.field L hL :=
  ⟨D.transferNormNaturalityFrobeniusTransferTermPreimage
      E L hL σ q,
    D.transferNormNaturalityFrobeniusTransferTermPreimage_degree
      E L hL σ q⟩

/-- The transfer lift coerces to the pulled-back term
([Yamaguchi 2026, `MainTransferFrobenius.lean:387`][Yamaguchi2026]). -/
@[simp]
theorem transferNormNaturalityTransferFrobeniusLift_coe
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    (D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q).1 =
      D.transferNormNaturalityFrobeniusTransferTermPreimage
        E L hL σ q := rfl

/-- **The transfer lift maps to the transfer term under the tower map**
([Yamaguchi 2026, `MainTransferFrobenius.lean:407`][Yamaguchi2026]). -/
theorem transferNormNaturalityTransferFrobeniusLift_towerMap
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L
        (hL.trans E.below) hL E.below le_rfl
        (D.transferNormNaturalityTransferFrobeniusLift
          E L hL σ q).1 =
      (D.transferNormNaturalityFrobeniusTransferTerm
        E L hL σ q).1 := by
  exact congrArg Subtype.val
    ((D.transferNormNaturalityFrobeniusIntermediateEquiv
      E L hL).apply_symm_apply
        (D.transferNormNaturalityFrobeniusTransferTerm
          E L hL σ q))

/-- **The closed subgroup generated by a transfer lift maps onto the
closed subgroup generated by its transfer term**
([Yamaguchi 2026, `MainTransferFrobenius.lean:435`][Yamaguchi2026]). -/
theorem transferNormNaturalityTransferFrobeniusLift_closure_map
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let f := D.finiteReciprocityNaturalityFrobeniusTowerMap
      E.base.field E.field.field L L
      (hL.trans E.below) hL E.below le_rfl
    (D.frobeniusClosure E.field L hL β).toSubgroup.map f =
      (closedSubgroupGenerated
        ({(D.transferNormNaturalityFrobeniusTransferTerm
          E L hL σ q).1} : Set
            (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
              (hL.trans E.below))) : Subgroup
                (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
                  (hL.trans E.below))) := by
  dsimp only
  let β := D.transferNormNaturalityTransferFrobeniusLift
    E L hL σ q
  let Γβ := D.frobeniusClosure E.field L hL β
  let f := D.finiteReciprocityNaturalityFrobeniusTowerMap
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl
  let fc := D.finiteReciprocityNaturalityFrobeniusTowerMapContinuous
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl
  let P := E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
    (hL.trans E.below)
  let u := (D.transferNormNaturalityFrobeniusTransferTerm
    E L hL σ q).1
  have hβu : f β.1 = u :=
    D.transferNormNaturalityTransferFrobeniusLift_towerMap
      E L hL σ q
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    change x ∈ Γβ.toSubgroup at hx
    have hx' : x ∈
        (closedSubgroupGenerated
          ({(D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q).1} : Set
        (E.field.field.toSubgroup ⧸
          D.extensionInertiaWithin E.field.field L hL))).toSubgroup := by
      simpa only [Γβ, DegreeData.frobeniusClosure, Set.range_unique] using hx
    have hmap := map_mem_closedSubgroupGenerated_singleton
      fc (D.transferNormNaturalityTransferFrobeniusLift E L hL σ q).1 hx'
    change f x ∈
      (closedSubgroupGenerated ({f β.1} : Set P) : Subgroup P) at hmap
    rw [hβu] at hmap
    exact hmap
  · have hK'compact : CompactSpace E.field.field.toSubgroup :=
      isCompact_iff_compactSpace.mp E.field.field.isClosed'.isCompact
    letI : CompactSpace E.field.field.toSubgroup := hK'compact
    letI : IsClosed
        (D.extensionInertiaWithin E.field.field L hL :
          Set E.field.field.toSubgroup) :=
      D.extensionInertiaWithin_isClosed E.field L hL
    letI : IsClosed (D.extensionInertiaWithin E.base.field L
        (hL.trans E.below) : Set E.base.field.toSubgroup) :=
      D.extensionInertiaWithin_isClosed E.base L (hL.trans E.below)
    have hmapClosed : IsClosed
        ((Γβ.toSubgroup.map f : Subgroup P) : Set P) := by
      have hrange : ((Γβ.toSubgroup.map f : Subgroup P) : Set P) =
          Set.range (fun x : Γβ => f x.1) := by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨⟨x, hx⟩, rfl⟩
        · rintro ⟨x, rfl⟩
          exact ⟨x.1, x.2, rfl⟩
      rw [hrange]
      have hclosed :=
        ((isCompact_univ (X := Γβ)).image
          (fc.continuous.comp continuous_subtype_val)).isClosed
      change IsClosed
        ((fun x : Γβ => fc.toMonoidHom x.1) '' Set.univ) at hclosed
      have hclosed' :
          IsClosed (Set.range (fun x : Γβ => fc.toMonoidHom x.1)) := by
        simpa only [Set.image_univ] using hclosed
      have hfc : fc.toMonoidHom = f := by
        rfl
      rw [hfc] at hclosed'
      exact hclosed'
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst y
      have hβmem : β.1 ∈ Γβ.toSubgroup := by
        have hgen : β.1 ∈
            (closedSubgroupGenerated ({β.1} : Set _) : Subgroup _) :=
          Subgroup.le_topologicalClosure _
            (Subgroup.subset_closure (by simp))
        simpa [Γβ, β, DegreeData.frobeniusClosure] using hgen
      exact ⟨β.1, hβmem, hβu⟩
    · exact hmapClosed

/-- **For a transfer orbit represented by `t`, membership in the fixed
subgroup of its Frobenius lift over `K'` is stabilization of the norm
coset `t⁻¹G_Σ`** — the intersection `G_K' ∩ t⁻¹G_Σt`
([Yamaguchi 2026, `MainTransferFrobenius.lean:545`][Yamaguchi2026]). -/
theorem transferNormNaturalityTransferFrobeniusLift_mem_fixedSubgroup_iff_stabilizer
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)))
    (k' : E.field.field.toSubgroup) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let kM : E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup :=
      ⟨Subgroup.inclusion E.below k', k'.2⟩
    k' ∈ (D.frobeniusFixedField E.field L hL β).toSubgroup.subgroupOf E.field.field.toSubgroup ↔
      kM ∈ MulAction.stabilizer
        (E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
        (QuotientGroup.mk tK⁻¹ :
          E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup) := by
  dsimp only
  let P := E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
    (hL.trans E.below)
  let P' := E.field.field.toSubgroup ⧸
    D.extensionInertiaWithin E.field.field L hL
  let f : P' →* P := D.finiteReciprocityNaturalityFrobeniusTowerMap
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  letI : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  have hHclosed : IsClosed (H : Set P) :=
    D.transferNormNaturalityFrobeniusIntermediate_isClosed E L hL
  let β := D.transferNormNaturalityTransferFrobeniusLift
    E L hL σ q
  let Γβ := D.frobeniusClosure E.field L hL β
  let Γ := D.frobeniusClosure E.base L (hL.trans E.below) σ
  let m := Function.minimalPeriod (σ.1 • ·) q.out
  let t : P := q.out.out
  let tK : E.base.field.toSubgroup := Quotient.out t
  let u : P :=
    (D.transferNormNaturalityFrobeniusTransferTerm E L hL σ q).1
  let Cu : Subgroup P :=
    (closedSubgroupGenerated ({u} : Set P) : Subgroup P)
  let Cpow : Subgroup P :=
    (closedSubgroupGenerated ({σ.1 ^ m} : Set P) : Subgroup P)
  let c : P →ₜ* P :=
    { toMonoidHom := (MulAut.conj t).toMonoidHom
      continuous_toFun := IsTopologicalGroup.continuous_conj t }
  let ci : P →ₜ* P :=
    { toMonoidHom := (MulAut.conj t⁻¹).toMonoidHom
      continuous_toFun := IsTopologicalGroup.continuous_conj t⁻¹ }
  have hc_apply (y : P) : c y = t * y * t⁻¹ := rfl
  have hci_apply (y : P) : ci y = t⁻¹ * y * t := by
    change t⁻¹ * y * (t⁻¹)⁻¹ = t⁻¹ * y * t
    rw [inv_inv]
  have hclosureMap : Γβ.toSubgroup.map f = Cu := by
    simpa [Γβ, Cu, u, β, f] using
      D.transferNormNaturalityTransferFrobeniusLift_closure_map
        E L hL σ q
  have hpow : Cpow = Γ.toSubgroup ⊓ MulAction.stabilizer P q.out := by
    simpa [Cpow, Γ, DegreeData.frobeniusClosure, m] using
      closedSubgroupGenerated_pow_eq_inf_stabilizer
        H hHclosed σ.1 q.out
  have hcu : c u = σ.1 ^ m := by
    change t * (t⁻¹ * σ.1 ^ m * t) * t⁻¹ = σ.1 ^ m
    simp [mul_assoc]
  have hcig : ci (σ.1 ^ m) = u := by
    rw [hci_apply]
    rfl
  have hVeq : MulAction.stabilizer P q.out =
      H.map (MulAut.conj t).toMonoidHom := by
    have hx : q.out = t • (QuotientGroup.mk 1 : P ⧸ H) := by
      symm
      change QuotientGroup.mk (t * 1) = q.out
      rw [mul_one]
      exact Quotient.out_eq' q.out
    rw [hx, stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_quotient]
  have hclosure_iff (x : P') :
      x ∈ Γβ.toSubgroup ↔ c (f x) ∈ Γ.toSubgroup := by
    constructor
    · intro hx
      have hfx : f x ∈ Cu := by
        rw [← hclosureMap]
        exact ⟨x, hx, rfl⟩
      have hcx := map_mem_closedSubgroupGenerated_singleton c u hfx
      rw [hcu] at hcx
      change c (f x) ∈ Cpow at hcx
      rw [hpow] at hcx
      exact hcx.1
    · intro hx
      have hfxH : f x ∈ H := ⟨x, rfl⟩
      have hcfxV : c (f x) ∈ MulAction.stabilizer P q.out := by
        rw [hVeq]
        exact ⟨f x, hfxH, rfl⟩
      have hcfx : c (f x) ∈ Cpow := by
        rw [hpow]
        exact ⟨hx, hcfxV⟩
      have hcix := map_mem_closedSubgroupGenerated_singleton
        ci (σ.1 ^ m) hcfx
      rw [hcig] at hcix
      have hif : ci (c (f x)) = f x := by
        rw [hci_apply, hc_apply]
        simp [mul_assoc]
      rw [hif] at hcix
      have hmap : f x ∈ Γβ.toSubgroup.map f := by
        rw [hclosureMap]
        exact hcix
      exact (Subgroup.mem_map_iff_mem
        (D.transferNormNaturalityFrobeniusTowerMap_injective
          E L hL)).mp hmap
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let kM : E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup :=
    ⟨Subgroup.inclusion E.below k', k'.2⟩
  rw [D.subgroupOf_frobeniusFixedField E.field L hL β]
  change QuotientGroup.mk k' ∈ Γβ.toSubgroup ↔ _
  rw [hclosure_iff]
  rw [mem_relativeNormDoubleCoset_stabilizer_iff
    E.base.field E.field.field S tK⁻¹ kM]
  let zK : E.base.field.toSubgroup :=
    tK * Subgroup.inclusion E.below k' * tK⁻¹
  have htz : c (f (QuotientGroup.mk k')) = QuotientGroup.mk zK := by
    change t * QuotientGroup.mk (Subgroup.inclusion E.below k') * t⁻¹ =
      QuotientGroup.mk zK
    have htK : (QuotientGroup.mk tK : P) = t := Quotient.out_eq' t
    rw [← htK]
    rfl
  rw [htz]
  rw [← D.mem_frobeniusFixedSubgroupWithin_iff E.base L
    (hL.trans E.below) σ zK]
  rw [← D.subgroupOf_frobeniusFixedField E.base L
    (hL.trans E.below) σ]
  rw [Subgroup.mem_subgroupOf]
  change zK.1 ∈ S.toSubgroup ↔ _
  simp [zK, kM, tK, mul_assoc]

/-- **The fixed-subgroup calculation as a literal subgroup equality**,
identifying the stabilizer-coset fiber with the norm fiber
([Yamaguchi 2026, `MainTransferFrobenius.lean:695`][Yamaguchi2026]). -/
theorem transferNormNaturalityTransferFrobeniusLift_fixedSubgroup_map
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    let e := transferNormNaturalityIntermediateAbsoluteEquiv
      E.base.field E.field.field E.below
    ((D.frobeniusFixedField E.field L hL β).toSubgroup.subgroupOf
        E.field.field.toSubgroup).map e.toMonoidHom =
      MulAction.stabilizer
        (E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
        (QuotientGroup.mk tK⁻¹ :
          E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup) := by
  dsimp only
  let e := transferNormNaturalityIntermediateAbsoluteEquiv
    E.base.field E.field.field E.below
  ext kM
  obtain ⟨k', rfl⟩ := e.surjective kM
  change e k' ∈ Subgroup.map e.toMonoidHom _ ↔ _
  have hmem : e k' ∈ Subgroup.map e.toMonoidHom
      ((D.frobeniusFixedField E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q)).toSubgroup.subgroupOf E.field.field.toSubgroup) ↔
      k' ∈ (D.frobeniusFixedField E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q)).toSubgroup.subgroupOf E.field.field.toSubgroup :=
    Subgroup.mem_map_iff_mem e.injective
  rw [hmem]
  exact D.transferNormNaturalityTransferFrobeniusLift_mem_fixedSubgroup_iff_stabilizer
    E L hL σ q k'

end DegreeData

/-- The quotient by a transfer factor's fixed subgroup as the
stabilizer-coset fiber of its norm double coset
([Yamaguchi 2026, `MainTransferFrobenius.lean:756`][Yamaguchi2026]). -/
noncomputable def chosenTransferNormNaturalityTransferNormFiberEquiv
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL))) :
    let β := D.transferNormNaturalityTransferFrobeniusLift
      E L hL σ q
    let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
    let tK : E.base.field.toSubgroup := Quotient.out q.out.out
    E.field.field.toSubgroup ⧸ (D.frobeniusFixedField E.field L hL β).toSubgroup.subgroupOf
        E.field.field.toSubgroup ≃
      (E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup) ⧸
        MulAction.stabilizer
          (E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
          (QuotientGroup.mk tK⁻¹ :
            E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup) := by
  dsimp only
  let e := transferNormNaturalityIntermediateAbsoluteEquiv
    E.base.field E.field.field E.below
  let Sβsubgroup := (D.frobeniusFixedField E.field L hL
      (D.transferNormNaturalityTransferFrobeniusLift E L hL σ q)).toSubgroup.subgroupOf
          E.field.field.toSubgroup
  have hEq := D.transferNormNaturalityTransferFrobeniusLift_fixedSubgroup_map
    E L hL σ q
  exact (leftCosetEquivOfMulEquiv e Sβsubgroup).trans
    (Subgroup.quotientEquivOfEq hEq)

/-- The fiber equivalence evaluates by the absolute identification
([Yamaguchi 2026, `MainTransferFrobenius.lean:797`][Yamaguchi2026]). -/
@[simp]
theorem chosenTransferNormNaturalityTransferNormFiberEquiv_mk
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (q : Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)))
    (k' : E.field.field.toSubgroup) :
    chosenTransferNormNaturalityTransferNormFiberEquiv
        D E L hL σ q (QuotientGroup.mk k') =
      QuotientGroup.mk
        (transferNormNaturalityIntermediateAbsoluteEquiv
          E.base.field E.field.field E.below k') := by
  unfold chosenTransferNormNaturalityTransferNormFiberEquiv
  rfl

end transferFrobeniusFibers

end

end Atlas.Knowledge
