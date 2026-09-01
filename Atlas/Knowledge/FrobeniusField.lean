import Mathlib
import Atlas.Knowledge.FiniteResidueAbstractExtension
import Atlas.Knowledge.FrobeniusFixedField
import Atlas.Knowledge.NormalizedDegree

/-!
# Frobenius field

The passage from the group-dual `Γ` of the Frobenius fixed-field theorem to
the actual abstract field `Σ`: its absolute Galois subgroup is the inverse
image of `Γ` under `G_K → G_K/I_L`, embedded back into the ambient group as
a closed subgroup. The finiteness, index estimate, and residue-degree
formula transport from `Γ`; the intersection `G_Σ ∩ I_K = I_L` is the
subgroup form of `Σ̃ = L̃`; and restriction identifies `G_Σ/I_Σ` with `Γ`,
carrying the intrinsic normalized degree of `Σ` to the one constructed on
`Γ` — so under the identification the Frobenius of `Σ` is the originally
chosen lift (#104).

## Main definitions

* `DegreeData.frobeniusFixedField` — the field `Σ` fixed by a Frobenius
  lift, as a closed subgroup of the ambient group.
* `DegreeData.frobeniusFixedFiniteExtension` /
  `DegreeData.frobeniusFixedResidueField` — `Σ | K` bundled finite, and
  `Σ` with its finite residue quotient.
* `DegreeData.frobeniusFixedFieldQuotientEquiv` — the identification
  `G_Σ/I_Σ ≃* Γ`.

## Main statements

* `DegreeData.frobeniusFixedField_finite` — `Σ | K` is finite; proved.
* `DegreeData.frobeniusFixedField_index_le_extensionIndex_of_exponent_eq_one`
  — for a degree-one lift, `[Σ : K] ≤ [L : K]`; proved.
* `DegreeData.frobeniusFixedSubgroupWithin_inf_fieldInertiaWithin` /
  `DegreeData.frobeniusFixedField_fieldInertia` — `G_Σ ∩ I_K = I_L`, and
  its ambient form `I_Σ = I_L`; proved.
* `DegreeData.frobeniusFixedResidueField_residueDegree` —
  `f_Σ = d_K(σ)·f_K`; proved.
* `DegreeData.frobeniusFixedFieldQuotientEquiv_degree` — the
  identification carries `d_Σ` to the fixed-field normalized degree;
  proved.
* `DegreeData.frobeniusFixedField_frobenius_eq_inClosure` — under the
  identification the Frobenius of `Σ` is the chosen lift; proved.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The subgroup `G_Σ ≤ G_K`**: the inverse image of `Γ = closure ⟨σ⟩`
under `G_K → G_K/I_L` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:23`]
[Yamaguchi2026]). -/
def frobeniusFixedSubgroupWithin (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : Subgroup K.field.toSubgroup :=
  (D.frobeniusClosure K L hLK σ).toSubgroup.comap
    (QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK))

/-- Membership in the internal Frobenius-fixed subgroup is membership of
the restriction in the closure. -/
@[simp]
theorem mem_frobeniusFixedSubgroupWithin_iff (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) (k : K.field.toSubgroup) :
    k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ↔
      QuotientGroup.mk k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup :=
  Iff.rfl

/-- The Frobenius-fixed subgroup is closed in the base subgroup
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:46`]
[Yamaguchi2026]). -/
theorem frobeniusFixedSubgroupWithin_isClosed (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    IsClosed
      (D.frobeniusFixedSubgroupWithin K L hLK σ :
        Set K.field.toSubgroup) := by
  change IsClosed
    ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) ⁻¹'
      ((D.frobeniusClosure K L hLK σ).toSubgroup : Set
        (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)))
  exact (D.frobeniusClosure K L hLK σ).isClosed'.preimage
    continuous_quotient_mk'

/-- **The abstract field `Σ` fixed by the chosen Frobenius lift**: the
inverse image of `Γ`, regarded as a closed subgroup of the ambient group
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:64`]
[Yamaguchi2026]). -/
def frobeniusFixedField (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) : ClosedSubgroup G where
  toSubgroup :=
    (D.frobeniusFixedSubgroupWithin K L hLK σ).map
      K.field.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      (Subtype.val ''
        (D.frobeniusFixedSubgroupWithin K L hLK σ :
          Set K.field.toSubgroup))
    exact K.field.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _
      (D.frobeniusFixedSubgroupWithin_isClosed K L hLK σ)

/-- An element lies in the Frobenius fixed field exactly when it comes from
the Frobenius-fixed subgroup. -/
@[simp]
theorem mem_frobeniusFixedField_iff (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) (g : G) :
    g ∈ D.frobeniusFixedField K L hLK σ ↔
      ∃ k : K.field.toSubgroup,
        k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ ∧ k.1 = g := by
  rfl

/-- **The field `Σ` extends `K`**: `G_Σ ≤ G_K` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:93`]
[Yamaguchi2026]). -/
theorem frobeniusFixedField_le (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusFixedField K L hLK σ).toSubgroup ≤
      K.field.toSubgroup := by
  rintro g ⟨k, _, rfl⟩
  exact k.2

/-- **Inside `G_K`, the subgroup of the field `Σ` is the defining inverse
image** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:104`]
[Yamaguchi2026]). -/
theorem extensionSubgroup_frobeniusFixedField (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
        K.field.toSubgroup =
      D.frobeniusFixedSubgroupWithin K L hLK σ := by
  ext k
  change
    (k.1 ∈ D.frobeniusFixedField K L hLK σ) ↔
      k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ
  rw [D.mem_frobeniusFixedField_iff K L hLK σ]
  constructor
  · rintro ⟨t, ht, htk⟩
    have : t = k := by
      apply Subtype.ext
      exact htk
    simpa [this] using ht
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- **The subgroup `I_L = G_L̃` lies in `G_Σ`**, internally
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:128`]
[Yamaguchi2026]). -/
theorem extensionInertiaWithin_le_frobeniusFixedSubgroupWithin
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.extensionInertiaWithin K.field L hLK ≤
      D.frobeniusFixedSubgroupWithin K L hLK σ := by
  intro k hk
  change QuotientGroup.mk k ∈
    (D.frobeniusClosure K L hLK σ).toSubgroup
  rw [(QuotientGroup.eq_one_iff k).2 hk]
  exact Subgroup.one_mem _

/-- The ambient form of `I_L ≤ G_Σ` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:143`]
[Yamaguchi2026]). -/
theorem fieldInertia_le_frobeniusFixedField (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.fieldInertia L).toSubgroup ≤
      (D.frobeniusFixedField K L hLK σ).toSubgroup := by
  intro g hg
  let k : K.field.toSubgroup := ⟨g, hLK hg.1⟩
  have hkE : k ∈ L.toSubgroup.subgroupOf K.field.toSubgroup := hg.1
  have hkI : k ∈ D.fieldInertiaWithin K.field := hg.2
  exact ⟨k,
    D.extensionInertiaWithin_le_frobeniusFixedSubgroupWithin
      K L hLK σ ⟨hkE, hkI⟩,
    rfl⟩

/-- **The extension `Σ | K` is finite** — the fixed-field finiteness on the
actual field side ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:161`]
[Yamaguchi2026]). -/
theorem frobeniusFixedField_finite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK) :
    Finite
      (K.field.toSubgroup ⧸
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
          K.field.toSubgroup) := by
  let N := D.extensionInertiaWithin K.field L hLK
  let Q := K.field.toSubgroup ⧸ N
  let Γ : Subgroup Q :=
    (D.frobeniusClosure K L hLK σ).toSubgroup
  let S : Subgroup K.field.toSubgroup :=
    D.frobeniusFixedSubgroupWithin K L hLK σ
  letI : Finite (Q ⧸ Γ) := by
    simpa [Q, Γ, N] using
      D.frobeniusFixedField_finiteIndex K L hLK σ
  have hΓ : Γ.index ≠ 0 := Γ.index_ne_zero_of_finite
  have hS : S.index ≠ 0 := by
    rw [show S = Γ.comap (QuotientGroup.mk' N) by rfl]
    rw [Subgroup.index_comap_of_surjective Γ
      (QuotientGroup.mk'_surjective N)]
    exact hΓ
  apply Nat.finite_of_card_ne_zero
  change
    ((D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
      K.field.toSubgroup).index ≠ 0
  rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ]
  exact hS

/-- **The Frobenius fixed field bundled with its finite extension data**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:195`]
[Yamaguchi2026]). -/
def frobeniusFixedFiniteExtension (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK) :
    FiniteAbstractExtension G where
  field := D.frobeniusFixedField K L hLK σ
  base := K.field
  below := D.frobeniusFixedField_le K L hLK σ
  finiteQuotient := D.frobeniusFixedField_finite K L hLK σ

/-- **For a degree-one lift, `[Σ : K] ≤ [L : K]`** — the index estimate on
the actual-field side ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:210`]
[Yamaguchi2026]). -/
theorem frobeniusFixedField_index_le_extensionIndex_of_exponent_eq_one
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK)
    (hσ : D.frobeniusExponent K L hLK σ = 1) :
    ((D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
        K.field.toSubgroup).index ≤
      (L.toSubgroup.subgroupOf K.field.toSubgroup).index := by
  let N := D.extensionInertiaWithin K.field L hLK
  let Q := K.field.toSubgroup ⧸ N
  let Γ : Subgroup Q :=
    (D.frobeniusClosure K L hLK σ).toSubgroup
  let S : Subgroup K.field.toSubgroup :=
    D.frobeniusFixedSubgroupWithin K L hLK σ
  rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ]
  change S.index ≤ (L.toSubgroup.subgroupOf K.field.toSubgroup).index
  rw [show S = Γ.comap (QuotientGroup.mk' N) by rfl]
  rw [Subgroup.index_comap_of_surjective Γ
    (QuotientGroup.mk'_surjective N)]
  exact D.frobeniusClosure_index_le_extensionIndex_of_exponent_eq_one
    K L hLK σ hσ

/-- **`G_Σ ∩ I_K = I_L`** — the procyclic degree isomorphism pulled back
along `G_K → G_K/I_L`, the subgroup form of `Σ̃ = L̃` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:240`]
[Yamaguchi2026]). -/
theorem frobeniusFixedSubgroupWithin_inf_fieldInertiaWithin
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusFixedSubgroupWithin K L hLK σ ⊓
        D.fieldInertiaWithin K.field =
      D.extensionInertiaWithin K.field L hLK := by
  apply le_antisymm
  · intro k hk
    let a : D.frobeniusClosure K L hLK σ :=
      ⟨QuotientGroup.mk k, hk.1⟩
    have hda : D.fixedFieldNormalizedDegree K L hLK σ a = 1 := by
      apply Multiplicative.ext
      apply ProfiniteInteger.nsmul_left_injective
        (D.frobeniusExponent_pos K L hLK σ).ne'
      change D.frobeniusExponent K L hLK σ •
          (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
        D.frobeniusExponent K L hLK σ • (1 : ProfiniteIntegerMul).toAdd
      rw [D.frobeniusExponent_nsmul_fixedFieldNormalizedDegree]
      change (D.normalizedDegree K k).toAdd =
        D.frobeniusExponent K L hLK σ • (1 : ProfiniteIntegerMul).toAdd
      have hdk : D.normalizedDegree K k = 1 := by
        change k ∈ (D.normalizedDegree K).toMonoidHom.ker
        rw [D.normalizedDegree_ker K]
        exact hk.2
      rw [hdk]
      simp
    have ha : a = 1 := by
      apply D.frobeniusFixedField_normalizedDegree_injective K L hLK σ
      simpa using hda
    apply (QuotientGroup.eq_one_iff k).mp
    exact congrArg Subtype.val ha
  · intro k hk
    exact
      ⟨D.extensionInertiaWithin_le_frobeniusFixedSubgroupWithin
          K L hLK σ hk,
        hk.2⟩

/-- **`I_Σ = I_L`** — the ambient version: the maximal unramified
extensions of `Σ` and `L` have the same absolute Galois subgroup
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:284`]
[Yamaguchi2026]). -/
theorem frobeniusFixedField_fieldInertia (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.fieldInertia (D.frobeniusFixedField K L hLK σ) =
      D.fieldInertia L := by
  ext g
  constructor
  · intro hg
    obtain ⟨k, hkS, hkg⟩ := hg.1
    have hgdeg : D.degree g = 1 := hg.2
    have hkI : k ∈ D.fieldInertiaWithin K.field := by
      change D.degree k.1 = 1
      exact (congrArg D.degree hkg).trans hgdeg
    have hkN : k ∈ D.extensionInertiaWithin K.field L hLK := by
      rw [← D.frobeniusFixedSubgroupWithin_inf_fieldInertiaWithin
        K L hLK σ]
      exact ⟨hkS, hkI⟩
    exact ⟨hkg ▸ hkN.1, hg.2⟩
  · intro hg
    let k : K.field.toSubgroup := ⟨g, hLK hg.1⟩
    have hgdeg : D.degree g = 1 := hg.2
    have hkE : k ∈ L.toSubgroup.subgroupOf K.field.toSubgroup := hg.1
    have hkI : k ∈ D.fieldInertiaWithin K.field := hgdeg
    have hkS : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ :=
      D.extensionInertiaWithin_le_frobeniusFixedSubgroupWithin
        K L hLK σ ⟨hkE, hkI⟩
    exact ⟨⟨k, hkS, rfl⟩, hg.2⟩

/-- **The normalized-degree image of `G_Σ` is the image computed on `Γ`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:318`]
[Yamaguchi2026]). -/
theorem frobeniusFixedSubgroupWithin_normalizedDegree_image
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusFixedSubgroupWithin K L hLK σ).map
        (D.normalizedDegree K).toMonoidHom =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range := by
  ext z
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨QuotientGroup.mk k, hk⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
      (D.extensionInertiaWithin K.field L hLK) a.1
    have hkS : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
      change (QuotientGroup.mk'
          (D.extensionInertiaWithin K.field L hLK)) k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup
      exact hk.symm ▸ a.2
    refine ⟨k, hkS, ?_⟩
    calc
      D.normalizedDegree K k =
          D.extensionNormalizedDegree K L hLK
            ((QuotientGroup.mk'
              (D.extensionInertiaWithin K.field L hLK)) k) :=
        (D.extensionNormalizedDegree_mk K L hLK k).symm
      _ = D.extensionNormalizedDegree K L hLK a.1 :=
        congrArg (D.extensionNormalizedDegree K L hLK) hk

/- The mapped relative index of `G_Σ` in `G_K` is the Frobenius exponent
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:347`]
[Yamaguchi2026]). -/
private theorem frobeniusFixedField_mappedRelIndex (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
        D.degree.toMonoidHom).relIndex
      (K.field.toSubgroup.map D.degree.toMonoidHom) =
      D.frobeniusExponent K L hLK σ := by
  let S : Subgroup K.field.toSubgroup :=
    D.frobeniusFixedSubgroupWithin K L hLK σ
  let dK : K.field.toSubgroup →* ProfiniteIntegerMul :=
    (D.normalizedDegree K).toMonoidHom
  let scale : ProfiniteIntegerMul →* ProfiniteIntegerMul :=
    (profiniteIntegerPowNat (K.residueDegree : ℕ)).toMonoidHom
  have hraw : (D.restrictedDegree K.field).toMonoidHom =
      scale.comp dK := by
    apply MonoidHom.ext
    intro k
    apply Multiplicative.ext
    exact (D.residueDegree_nsmul_normalizedDegree K k).symm
  have hSigmaImage :
      (D.frobeniusFixedField K L hLK σ).toSubgroup.map
          D.degree.toMonoidHom =
        S.map (D.restrictedDegree K.field).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨k, hk, hkg⟩ := hg
      refine ⟨k, hk, ?_⟩
      exact congrArg D.degree hkg
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.1, ⟨k, hk, rfl⟩, rfl⟩
  have hKimage :
      K.field.toSubgroup.map D.degree.toMonoidHom =
        (⊤ : Subgroup K.field.toSubgroup).map
          (D.restrictedDegree K.field).toMonoidHom := by
    ext z
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, trivial, rfl⟩
    · rintro ⟨k, _, rfl⟩
      exact ⟨k.1, k.2, rfl⟩
  have hscale : Function.Injective scale := by
    intro x y hxy
    apply Multiplicative.ext
    apply ProfiniteInteger.nsmul_left_injective K.residueDegree.pos.ne'
    exact congrArg Multiplicative.toAdd hxy
  have htop : (⊤ : Subgroup K.field.toSubgroup).map dK = ⊤ := by
    apply top_unique
    intro z _
    obtain ⟨k, hk⟩ := D.normalizedDegree_surjective K z
    exact ⟨k, trivial, hk⟩
  rw [hSigmaImage, hKimage, hraw]
  rw [← Subgroup.map_map, ← Subgroup.map_map]
  rw [Subgroup.relIndex_map_map_of_injective _ _ hscale]
  rw [show S.map dK =
      (D.frobeniusClosureDegree K L hLK σ).toMonoidHom.range by
        simpa [S, dK] using
          D.frobeniusFixedSubgroupWithin_normalizedDegree_image
            K L hLK σ]
  rw [htop, Subgroup.relIndex_top_right,
    D.frobeniusClosureDegree_range K L hLK σ,
    AddSubgroup.index_toSubgroup,
    ProfiniteInteger.index_span_natCast]

/-- **The fixed-field residue-degree formula on the finite extension**:
`f_{Σ|K} = d_K(σ)` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:416`]
[Yamaguchi2026]). -/
theorem frobeniusFixedField_residueDegreeOverBase (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite (K.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK) :
    ((D.frobeniusFixedFiniteExtension K L hLK σ).residueDegree D : ℕ) =
      D.frobeniusExponent K L hLK σ := by
  let E := D.frobeniusFixedFiniteExtension K L hLK σ
  rw [← E.mapped_relIndex_eq_residueDegree D]
  simpa [E, frobeniusFixedFiniteExtension] using
    D.frobeniusFixedField_mappedRelIndex K L hLK σ

/-- The relative residue quotient of `Σ` over `K` is finite: positivity of
the mapped relative index gives the finite-index witness ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:433`]
[Yamaguchi2026]). -/
theorem frobeniusFixedField_relativeResidueQuotientFinite
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    Finite
      (↥(K.field.toSubgroup.map D.degree.toMonoidHom) ⧸
        ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
            D.degree.toMonoidHom).subgroupOf
          (K.field.toSubgroup.map D.degree.toMonoidHom)) := by
  apply (Subgroup.index_ne_zero_iff_finite).mp
  change ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
      D.degree.toMonoidHom).relIndex
        (K.field.toSubgroup.map D.degree.toMonoidHom) ≠ 0
  rw [D.frobeniusFixedField_mappedRelIndex K L hLK σ]
  exact (D.frobeniusExponent_pos K L hLK σ).ne'

/-- **The Frobenius fixed field with its finite residue quotient**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:454`]
[Yamaguchi2026]). -/
noncomputable def frobeniusFixedResidueField (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    FiniteResidueAbstractField D := by
  letI := D.frobeniusFixedField_relativeResidueQuotientFinite K L hLK σ
  exact FiniteResidueAbstractField.ofRelativeInclusion D
    (D.frobeniusFixedField K L hLK σ) K
    (D.frobeniusFixedField_le K L hLK σ)

/-- **The absolute residue-degree formula** `f_Σ = d_K(σ)·f_K`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:468`]
[Yamaguchi2026]). -/
theorem frobeniusFixedResidueField_residueDegree (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    ((D.frobeniusFixedResidueField K L hLK σ).residueDegree : ℕ) =
      D.frobeniusExponent K L hLK σ * (K.residueDegree : ℕ) := by
  let Sigma := D.frobeniusFixedResidueField K L hLK σ
  let E : AbstractExtension G := {
    field := D.frobeniusFixedField K L hLK σ
    base := K.field
    below := D.frobeniusFixedField_le K L hLK σ
  }
  letI := D.frobeniusFixedField_relativeResidueQuotientFinite K L hLK σ
  have hrelative :
      E.relativeResidueDegreeCardinal D =
        (D.frobeniusExponent K L hLK σ : Cardinal) := by
    rw [AbstractExtension.relativeResidueDegreeCardinal]
    change Cardinal.mk
        (↥(K.field.toSubgroup.map D.degree.toMonoidHom) ⧸
          ((D.frobeniusFixedField K L hLK σ).toSubgroup.map
              D.degree.toMonoidHom).subgroupOf
            (K.field.toSubgroup.map D.degree.toMonoidHom)) = _
    rw [← Nat.cast_card]
    exact_mod_cast D.frobeniusFixedField_mappedRelIndex K L hLK σ
  have hcard :=
    E.relativeResidueDegreeCardinal_mul_residueDegreeCardinal D
  change E.relativeResidueDegreeCardinal D *
      D.residueDegreeCardinal K.field =
    D.residueDegreeCardinal Sigma.field at hcard
  rw [hrelative, K.residueDegreeCardinal_eq_coe,
    Sigma.residueDegreeCardinal_eq_coe] at hcard
  exact_mod_cast hcard.symm

/-- **Restriction from the actual group `G_Σ` to the group-dual `Γ`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:504`]
[Yamaguchi2026]). -/
def frobeniusFixedFieldToClosure (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusFixedField K L hLK σ).toSubgroup →*
      D.frobeniusClosure K L hLK σ where
  toFun s := by
    let k : K.field.toSubgroup :=
      Subgroup.inclusion (D.frobeniusFixedField_le K L hLK σ) s
    refine ⟨QuotientGroup.mk k, ?_⟩
    have hk : k ∈
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
          K.field.toSubgroup := s.2
    rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ] at hk
    exact hk
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' := by
    intro a b
    apply Subtype.ext
    rfl

/-- The restriction to the closure evaluates by the underlying inclusion. -/
@[simp]
theorem frobeniusFixedFieldToClosure_apply (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (s : (D.frobeniusFixedField K L hLK σ).toSubgroup) :
    (D.frobeniusFixedFieldToClosure K L hLK σ s).1 =
      QuotientGroup.mk
        (Subgroup.inclusion
          (D.frobeniusFixedField_le K L hLK σ) s) :=
  rfl

/-- **Every element of the closure lifts from the fixed field**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:544`]
[Yamaguchi2026]). -/
theorem frobeniusFixedFieldToClosure_surjective (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    Function.Surjective (D.frobeniusFixedFieldToClosure K L hLK σ) := by
  intro a
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective
    (D.extensionInertiaWithin K.field L hLK) a.1
  have hkS : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
    change (QuotientGroup.mk'
        (D.extensionInertiaWithin K.field L hLK)) k ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup
    exact hk.symm ▸ a.2
  let s : (D.frobeniusFixedField K L hLK σ).toSubgroup :=
    ⟨k.1, ⟨k, hkS, rfl⟩⟩
  refine ⟨s, ?_⟩
  apply Subtype.ext
  exact hk

/-- **The kernel of `G_Σ → Γ` is `I_Σ`** — by the procyclic degree
isomorphism, equally `I_L` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:566`]
[Yamaguchi2026]). -/
theorem frobeniusFixedFieldToClosure_ker (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.frobeniusFixedFieldToClosure K L hLK σ).ker =
      D.fieldInertiaWithin (D.frobeniusFixedField K L hLK σ) := by
  ext s
  let k : K.field.toSubgroup :=
    Subgroup.inclusion (D.frobeniusFixedField_le K L hLK σ) s
  have hkS : k ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
    have hk : k ∈
        (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
          K.field.toSubgroup := s.2
    rw [D.extensionSubgroup_frobeniusFixedField K L hLK σ] at hk
    exact hk
  constructor
  · intro hs
    have hq : QuotientGroup.mk k = 1 :=
      congrArg Subtype.val hs
    have hkN : k ∈ D.extensionInertiaWithin K.field L hLK :=
      (QuotientGroup.eq_one_iff k).mp hq
    exact hkN.2
  · intro hs
    have hkI : k ∈ D.fieldInertiaWithin K.field := hs
    have hkN : k ∈ D.extensionInertiaWithin K.field L hLK := by
      rw [← D.frobeniusFixedSubgroupWithin_inf_fieldInertiaWithin
        K L hLK σ]
      exact ⟨hkS, hkI⟩
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff k).mpr hkN

/-- **The canonical identification `G_Σ/I_Σ ≃* Γ`** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:602`]
[Yamaguchi2026]). -/
def frobeniusFixedFieldQuotientEquiv (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    ((D.frobeniusFixedField K L hLK σ).toSubgroup ⧸
        D.fieldInertiaWithin (D.frobeniusFixedField K L hLK σ)) ≃*
      D.frobeniusClosure K L hLK σ :=
  (QuotientGroup.quotientMulEquivOfEq
      (D.frobeniusFixedFieldToClosure_ker K L hLK σ).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (D.frobeniusFixedFieldToClosure K L hLK σ)
      (D.frobeniusFixedFieldToClosure_surjective K L hLK σ))

/-- The identification evaluates on representatives by restriction. -/
@[simp]
theorem frobeniusFixedFieldQuotientEquiv_mk (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (s : (D.frobeniusFixedField K L hLK σ).toSubgroup) :
    D.frobeniusFixedFieldQuotientEquiv K L hLK σ
        (QuotientGroup.mk s) =
      D.frobeniusFixedFieldToClosure K L hLK σ s := by
  rfl

/-- **The degree constructed on `Γ` is the intrinsic normalized degree of
`Σ`** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:635`]
[Yamaguchi2026]). -/
theorem frobeniusFixedField_normalizedDegree_compatibility
    (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (s : (D.frobeniusFixedField K L hLK σ).toSubgroup) :
    D.fixedFieldNormalizedDegree K L hLK σ
        (D.frobeniusFixedFieldToClosure K L hLK σ s) =
      D.normalizedDegree (D.frobeniusFixedResidueField K L hLK σ) s := by
  let Sigma := D.frobeniusFixedResidueField K L hLK σ
  let a : D.frobeniusClosure K L hLK σ :=
    D.frobeniusFixedFieldToClosure K L hLK σ s
  let k : K.field.toSubgroup :=
    Subgroup.inclusion (D.frobeniusFixedField_le K L hLK σ) s
  let n := D.frobeniusExponent K L hLK σ
  apply Multiplicative.ext
  apply ProfiniteInteger.nsmul_left_injective Sigma.residueDegree.pos.ne'
  change (Sigma.residueDegree : ℕ) •
      (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
    (Sigma.residueDegree : ℕ) • (D.normalizedDegree Sigma s).toAdd
  calc
    (Sigma.residueDegree : ℕ) •
        (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd =
      (K.residueDegree : ℕ) •
        (n • (D.fixedFieldNormalizedDegree K L hLK σ a).toAdd) := by
          rw [show (Sigma.residueDegree : ℕ) =
              n * (K.residueDegree : ℕ) by
            simpa [Sigma, n] using
              D.frobeniusFixedResidueField_residueDegree K L hLK σ]
          rw [smul_smul, Nat.mul_comm]
    _ = (K.residueDegree : ℕ) •
        (D.frobeniusClosureDegree K L hLK σ a).toAdd := by
          rw [D.frobeniusExponent_nsmul_fixedFieldNormalizedDegree]
    _ = (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd := by
          rfl
    _ = (D.degree s.1).toAdd := by
          exact D.residueDegree_nsmul_normalizedDegree K k
    _ = (Sigma.residueDegree : ℕ) •
        (D.normalizedDegree Sigma s).toAdd := by
          exact (D.residueDegree_nsmul_normalizedDegree Sigma s).symm

/-- **The identification carries `d_Σ` to the fixed-field normalized
degree** — the quotient-level compatibility ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:678`]
[Yamaguchi2026]). -/
theorem frobeniusFixedFieldQuotientEquiv_degree (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : (D.frobeniusFixedField K L hLK σ).toSubgroup ⧸
      D.fieldInertiaWithin (D.frobeniusFixedField K L hLK σ)) :
    D.fixedFieldNormalizedDegree K L hLK σ
        (D.frobeniusFixedFieldQuotientEquiv K L hLK σ q) =
      D.maximalUnramifiedDegreeEquiv
        (D.frobeniusFixedResidueField K L hLK σ) q := by
  refine Quotient.inductionOn' q ?_
  intro s
  exact D.frobeniusFixedField_normalizedDegree_compatibility
    K L hLK σ s

/-- **Under the identification with `Γ`, the Frobenius of `Σ` is the
originally chosen lift** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusField.lean:698`]
[Yamaguchi2026]). -/
theorem frobeniusFixedField_frobenius_eq_inClosure (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusFixedFieldQuotientEquiv K L hLK σ
        (D.frobenius (D.frobeniusFixedResidueField K L hLK σ)) =
      D.frobeniusInClosure K L hLK σ := by
  apply D.frobeniusFixedField_normalizedDegree_injective K L hLK σ
  rw [D.frobeniusFixedFieldQuotientEquiv_degree]
  rw [D.maximalUnramifiedDegreeEquiv_frobenius]
  rw [D.fixedFieldNormalizedDegree_generator]

end DegreeData

end

end Atlas.Knowledge
