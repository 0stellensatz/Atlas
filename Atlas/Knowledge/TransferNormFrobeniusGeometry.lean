import Mathlib
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.DoubleCosetOrbitGeometry
import Atlas.Knowledge.FiniteReciprocityNaturalityNorm
import Atlas.Knowledge.FiniteResidueAbstractExtension
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusFixedField
import Atlas.Knowledge.FrobeniusNormCosetDecomposition
import Atlas.Knowledge.TopologicalGeneration

/-!
# Transfer–norm Frobenius geometry

The Frobenius-side subgroup and orbit equivalences of transfer–norm
naturality: the copy `H` of `G(L̃|K')` inside `G(L̃|K)` with its
projection, index, and closedness, and the canonical identification of
the transfer-orbit index set `⟨σ⟩\\G(L̃|K)/H` with the norm
double-coset index set `G_K'\\G_K/G_Σ` (#104).

## Main definitions

* `transferNormNaturalityIntermediateAbsoluteEquiv` — `G_K'` as its
  literal copy.
* `DegreeData.transferNormNaturalityFrobeniusIntermediateSubgroup` —
  the subgroup `H`.
* `DegreeData.transferNormNaturalityIntermediateToFrobeniusSubgroup` —
  the projection onto `H`.
* `DegreeData.transferNormNaturalityTransferNormOrbitEquiv` — the
  transfer–norm index identification.

## Main statements

* `transferNormNaturality_intermediateExtension_normal` — normality
  restricts along extensions of the base; proved.
* `DegreeData.transferNormNaturalityFrobeniusTowerMap_injective` — the
  tower map is injective over a fixed top field; proved.
* `DegreeData.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map`
  — `H` as the image of `G_K'`; proved.
* `DegreeData.transferNormNaturalityIntermediateToFrobeniusSubgroup_surjective`
  — the projection is surjective; proved.
* `DegreeData.frobeniusFixedCosetClosureEquiv_equivariant` — the coset
  equivalence is equivariant; proved.
* `DegreeData.transferNormNaturalityExtensionRestriction_surjective` —
  restriction is surjective; proved.
* `DegreeData.transferNormNaturalityExtensionRestriction_ker_le_intermediate`
  — the restriction kernel lies in `H`; proved.
* `DegreeData.transferNormNaturalityFrobeniusIntermediateFiniteIndex` —
  `H` has finite index; proved.
* `DegreeData.transferNormNaturalityFrobeniusIntermediate_isClosed` —
  `H` is closed; proved.
* `DegreeData.transferNormNaturalityTransferNormOrbitEquiv_apply` — the
  equivalence on the chosen representative; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
with `Subgroup.mem_subgroupOf` for the source's membership rule, and
the whole file stays at the source's `Type u`. The
normality-restriction theorem sheds the source's containment `hLK'`,
which only the `extensionSubgroup` spelling consumed, so its argument
list is one shorter, and the dead-binder sweep runs to the lint's
fixpoint: eight declarations shed `[IsTopologicalGroup G]` and four
shed `[T2Space G]`, all simply unused. Four converter-widened lines are
re-wrapped. The citations name this file by bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/` in the source. The
source's namespace `open`s go — the layer keeps everything in one
namespace — while `open MulAction` stays for the orbit vocabulary.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

open MulAction

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The absolute group of an intermediate field, identified with its
literal copy inside the absolute group of the base field**
(Yamaguchi 2026, `MainTransferFrobeniusGeometry.lean:32`). -/
noncomputable def transferNormNaturalityIntermediateAbsoluteEquiv
    (K K' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup) :
    K'.toSubgroup ≃* K'.toSubgroup.subgroupOf K.toSubgroup :=
  MulEquiv.ofBijective
    ((Subgroup.inclusion hK'K).codRestrict
      (K'.toSubgroup.subgroupOf K.toSubgroup) (fun k' => k'.2))
    ⟨fun _ _ h => Subtype.ext (congrArg (fun z => z.1.1) h), by
      rintro ⟨k, hk'⟩
      let k' : K'.toSubgroup := ⟨k.1, hk'⟩
      exact ⟨k', Subtype.ext rfl⟩⟩

/-- The equivalence evaluates by the underlying inclusion
(Yamaguchi 2026, `MainTransferFrobeniusGeometry.lean:46`). -/
@[simp]
theorem transferNormNaturalityIntermediateAbsoluteEquiv_apply
    (K K' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (k' : K'.toSubgroup) :
    ((transferNormNaturalityIntermediateAbsoluteEquiv K K' hK'K k').1 : G) = k'.1 :=
  rfl

/-- **Normality of `L | K` restricts along every extension `K' | K`**
(Yamaguchi 2026, `MainTransferFrobeniusGeometry.lean:54`). -/
theorem transferNormNaturality_intermediateExtension_normal
    (K K' L : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    (L.toSubgroup.subgroupOf K'.toSubgroup).Normal := by
  have hcomap : L.toSubgroup.subgroupOf K'.toSubgroup =
      (L.toSubgroup.subgroupOf K.toSubgroup).comap
        (Subgroup.inclusion hK'K) := by
    ext k'
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf]
    rfl
  rw [hcomap]
  exact hLnormal.comap (Subgroup.inclusion hK'K)

namespace DegreeData

/-- **The tower map on the infinite Frobenius quotients is injective
when the top field is unchanged** (Yamaguchi 2026,
`MainTransferFrobeniusGeometry.lean:74`). -/
theorem transferNormNaturalityFrobeniusTowerMap_injective
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal] :
    Function.Injective
      (D.finiteReciprocityNaturalityFrobeniusTowerMap
        E.base.field E.field.field L L
        (hL.trans E.below) hL E.below le_rfl) := by
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro k'
  refine QuotientGroup.induction_on y ?_
  intro l' h
  apply QuotientGroup.eq.mpr
  have hmem :
      (Subgroup.inclusion E.below k')⁻¹ * Subgroup.inclusion E.below l' ∈
        D.extensionInertiaWithin E.base.field L (hL.trans E.below) :=
    QuotientGroup.eq.mp h
  constructor
  · apply (Subgroup.mem_subgroupOf).2
    have hG := (Subgroup.mem_subgroupOf).1 hmem.1
    simpa using hG
  · have hI := hmem.2
    change D.degree (((Subgroup.inclusion E.below k')⁻¹ *
      Subgroup.inclusion E.below l' : E.base.field.toSubgroup) : G) = 1 at hI
    change D.degree ((k'⁻¹ * l' : E.field.field.toSubgroup) : G) = 1
    exact hI

/-- **The copy of `G(L̃|K')` inside `G(L̃|K)`** — the subgroup `H` of
the classical double-coset proof of transfer–norm naturality
(Yamaguchi 2026, `MainTransferFrobeniusGeometry.lean:111`). -/
def transferNormNaturalityFrobeniusIntermediateSubgroup
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal] :
    Subgroup (E.base.field.toSubgroup ⧸
      D.extensionInertiaWithin E.base.field L (hL.trans E.below)) :=
  (D.finiteReciprocityNaturalityFrobeniusTowerMap
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl).range

/-- **`H` is the image of `G_K'` under the quotient projection**
(Yamaguchi 2026, `MainTransferFrobeniusGeometry.lean:126`). -/
theorem transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal] :
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL =
      (E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup).map
        (QuotientGroup.mk'
          (D.extensionInertiaWithin E.base.field L
            (hL.trans E.below))) := by
  ext q
  constructor
  · rintro ⟨x, rfl⟩
    refine QuotientGroup.induction_on x ?_
    intro k'
    refine ⟨Subgroup.inclusion E.below k', ?_, rfl⟩
    exact k'.2
  · rintro ⟨k, hk', rfl⟩
    let k' : E.field.field.toSubgroup := ⟨k.1, hk'⟩
    refine ⟨QuotientGroup.mk k', ?_⟩
    change QuotientGroup.mk (Subgroup.inclusion E.below k') =
      QuotientGroup.mk k
    rfl

/-- **The projection of the literal absolute subgroup of `K'` onto its
copy `H`** (Yamaguchi 2026, `MainTransferFrobeniusGeometry.lean:154`). -/
noncomputable def transferNormNaturalityIntermediateToFrobeniusSubgroup
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal] :
    E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup →*
      D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL := by
  refine ((QuotientGroup.mk'
    (D.extensionInertiaWithin E.base.field L (hL.trans E.below))).comp
      (E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup).subtype).codRestrict
        (D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL) ?_
  intro m
  change QuotientGroup.mk m.1 ∈
    D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  rw [D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    E L hL]
  exact ⟨m.1, m.2, rfl⟩

/-- **The projection onto `H` is surjective**
(Yamaguchi 2026, `MainTransferFrobeniusGeometry.lean:175`). -/
theorem transferNormNaturalityIntermediateToFrobeniusSubgroup_surjective
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal] :
    Function.Surjective
      (D.transferNormNaturalityIntermediateToFrobeniusSubgroup
        E L hL) := by
  intro h
  have hh : h.1 ∈
      (E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup).map
      (QuotientGroup.mk'
        (D.extensionInertiaWithin E.base.field L (hL.trans E.below))) := by
    rw [← D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
      E L hL]
    exact h.2
  obtain ⟨m, hm, hval⟩ := hh
  refine ⟨⟨m, hm⟩, ?_⟩
  apply Subtype.ext
  unfold transferNormNaturalityIntermediateToFrobeniusSubgroup
  simpa only [MonoidHom.codRestrict_apply, MonoidHom.comp_apply,
    Subgroup.subtype_apply] using hval

/-- The projection evaluates by the quotient class
(Yamaguchi 2026, `MainTransferFrobeniusGeometry.lean:202`). -/
@[simp]
theorem transferNormNaturalityIntermediateToFrobeniusSubgroup_apply
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (m : E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup) :
    (D.transferNormNaturalityIntermediateToFrobeniusSubgroup
      E L hL m).1 =
        (QuotientGroup.mk m.1 : E.base.field.toSubgroup ⧸
          D.extensionInertiaWithin E.base.field L (hL.trans E.below)) := by
  rfl

/-- **The canonical coset equivalence `G_K/G_Σ ≃ G(L̃|K)/Γ` intertwines
the two copies of the `K'`-action** (Yamaguchi 2026,
`MainTransferFrobeniusGeometry.lean:218`). -/
theorem frobeniusFixedCosetClosureEquiv_equivariant
    (D : DegreeData G) [IsTopologicalGroup G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (m : E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
    (x : E.base.field.toSubgroup ⧸
        (D.frobeniusFixedField E.base L (hL.trans E.below) σ).toSubgroup.subgroupOf
        E.base.field.toSubgroup) :
    D.frobeniusFixedCosetClosureEquiv E.base L (hL.trans E.below) σ (m • x) =
      (D.transferNormNaturalityIntermediateToFrobeniusSubgroup
        E L hL m) •
        D.frobeniusFixedCosetClosureEquiv E.base L
          (hL.trans E.below) σ x := by
  refine Quotient.inductionOn' x ?_
  intro k
  change QuotientGroup.mk (QuotientGroup.mk (m.1 * k)) =
    QuotientGroup.mk
      ((D.transferNormNaturalityIntermediateToFrobeniusSubgroup
        E L hL m).1 * QuotientGroup.mk k)
  rw [D.transferNormNaturalityIntermediateToFrobeniusSubgroup_apply]
  rfl

/-- **Restriction from the infinite Frobenius quotient onto the finite
Galois quotient is surjective** (Yamaguchi 2026,
`MainTransferFrobeniusGeometry.lean:246`). -/
theorem transferNormNaturalityExtensionRestriction_surjective
    (D : DegreeData G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    Function.Surjective (D.extensionRestriction K L hLK) := by
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k
  exact ⟨QuotientGroup.mk k, rfl⟩

/-- **The kernel of restriction to `G(L|K)` lies in `H`**
(Yamaguchi 2026, `MainTransferFrobeniusGeometry.lean:259`). -/
theorem transferNormNaturalityExtensionRestriction_ker_le_intermediate
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal] :
    (D.extensionRestriction E.base.field L (hL.trans E.below)).ker ≤
      D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL := by
  rw [D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    E L hL]
  intro q hq
  revert hq
  refine QuotientGroup.induction_on q ?_
  intro k hk
  change D.extensionRestriction E.base.field L (hL.trans E.below)
      (QuotientGroup.mk k) = 1 at hk
  rw [D.extensionRestriction_mk] at hk
  have hkL : k ∈
      L.toSubgroup.subgroupOf E.base.field.toSubgroup := by
    exact QuotientGroup.eq_one_iff k |>.1 hk
  have hkK' : k ∈
      E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup := by
    apply (Subgroup.mem_subgroupOf).2
    exact hL ((Subgroup.mem_subgroupOf).1 hkL)
  exact ⟨k, hkK', rfl⟩

/-- **`H` has finite index in `G(L̃|K)`**, with no normality assumption
on `K' | K` (Yamaguchi 2026, `MainTransferFrobeniusGeometry.lean:290`). -/
theorem transferNormNaturalityFrobeniusIntermediateFiniteIndex
    (D : DegreeData G)
    (R : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ R.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf R.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf R.field.field.toSubgroup).Normal] :
    (D.transferNormNaturalityFrobeniusIntermediateSubgroup R L hL).FiniteIndex := by
  rw [D.transferNormNaturalityFrobeniusIntermediateSubgroup_eq_map
    R L hL]
  let I := D.extensionInertiaWithin R.base.field L (hL.trans R.below)
  let M := R.field.field.toSubgroup.subgroupOf R.base.field.toSubgroup
  have hIM : I ≤ M := by
    intro k hk
    apply (Subgroup.mem_subgroupOf).2
    exact hL ((Subgroup.mem_subgroupOf).1 hk.1)
  let p := QuotientGroup.mk' I
  have hker : p.ker ≤ M := by
    simpa [p] using hIM
  letI : M.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  rw [Subgroup.finiteIndex_iff,
    M.index_map_eq (QuotientGroup.mk'_surjective I) hker]
  exact Subgroup.FiniteIndex.index_ne_zero

/-- **`H` is closed in `G(L̃|K)`** (Yamaguchi 2026,
`MainTransferFrobeniusGeometry.lean:318`). -/
theorem transferNormNaturalityFrobeniusIntermediate_isClosed
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal] :
    IsClosed (D.transferNormNaturalityFrobeniusIntermediateSubgroup
      E L hL : Set
        (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
          (hL.trans E.below))) := by
  letI : CompactSpace E.field.field.toSubgroup :=
    isCompact_iff_compactSpace.mp E.field.field.isClosed'.isCompact
  letI : IsClosed
      (D.extensionInertiaWithin E.field.field L hL :
        Set E.field.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed E.field L hL
  letI : IsClosed (D.extensionInertiaWithin E.base.field L
      (hL.trans E.below) : Set E.base.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed E.base L (hL.trans E.below)
  let f := D.finiteReciprocityNaturalityFrobeniusTowerMapContinuous
    E.base.field E.field.field L L
    (hL.trans E.below) hL E.below le_rfl
  change IsClosed (Set.range f)
  have hrange : Set.range f = Set.range f.toContinuousMap := by
    ext y
    constructor <;> rintro ⟨x, rfl⟩ <;> exact ⟨x, rfl⟩
  rw [hrange]
  simpa only [Set.image_univ] using
    (isCompact_univ.image f.continuous).isClosed

/-- **The transfer-orbit index set `⟨σ⟩\\G(L̃|K)/H` is canonically the
norm double-coset index set `G_K'\\G_K/G_Σ`** — inversion of double
cosets, passage from the powers of `σ` to their closure `Γ`, and the
canonical identification `G_K/G_Σ ≃ G(L̃|K)/Γ` (Yamaguchi 2026,
`MainTransferFrobeniusGeometry.lean:354`). -/
noncomputable def transferNormNaturalityTransferNormOrbitEquiv
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below)) :
    Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸
          D.transferNormNaturalityFrobeniusIntermediateSubgroup
            E L hL)) ≃
      Quotient (orbitRel
        (E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
        (E.base.field.toSubgroup ⧸
            (D.frobeniusFixedField E.base L (hL.trans E.below) σ).toSubgroup.subgroupOf
              E.base.field.toSubgroup)) := by
  let P := E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
    (hL.trans E.below)
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup E L hL
  let M := E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup
  let Γ := D.frobeniusClosure E.base L (hL.trans E.below) σ
  let S := D.frobeniusFixedField E.base L (hL.trans E.below) σ
  let hSK := D.frobeniusFixedField_le E.base L (hL.trans E.below) σ
  let f : M →* H := D.transferNormNaturalityIntermediateToFrobeniusSubgroup
    E L hL
  let e := D.frobeniusFixedCosetClosureEquiv
    E.base L (hL.trans E.below) σ
  letI : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  have hHclosed : IsClosed (H : Set P) :=
    D.transferNormNaturalityFrobeniusIntermediate_isClosed E L hL
  have hΓ :
      (closedSubgroupGenerated ({σ.1} : Set P)).toSubgroup = Γ.toSubgroup := by
    simp [Γ, DegreeData.frobeniusClosure]
  let eΓ : P ⧸ (closedSubgroupGenerated ({σ.1} : Set P)).toSubgroup ≃
      P ⧸ Γ.toSubgroup := Subgroup.quotientEquivOfEq hΓ
  have heΓ (h : H)
      (x : P ⧸ (closedSubgroupGenerated ({σ.1} : Set P)).toSubgroup) :
      eΓ (h • x) = h • eΓ x := by
    refine Quotient.inductionOn' x ?_
    intro p
    rfl
  let eΓorbit := orbitQuotientEquivOfSurjectiveEquivariant
    (MonoidHom.id H) Function.surjective_id eΓ heΓ
  have hf : Function.Surjective f :=
    D.transferNormNaturalityIntermediateToFrobeniusSubgroup_surjective
      E L hL
  have he (m : M)
      (x : E.base.field.toSubgroup ⧸ S.toSubgroup.subgroupOf E.base.field.toSubgroup) :
      e (m • x) = f m • e x := by
    exact D.frobeniusFixedCosetClosureEquiv_equivariant
      E L hL σ m x
  let eAction := orbitQuotientEquivOfSurjectiveEquivariant f hf e he
  exact (orbitQuotientSwapEquiv (Subgroup.zpowers σ.1) H).trans
    ((orbitQuotientClosedCyclicEquiv H hHclosed σ.1).trans
      (eΓorbit.trans eAction.symm))

/-- The orbit equivalence sends the representative `k` to the norm
orbit of `k⁻¹` (Yamaguchi 2026,
`MainTransferFrobeniusGeometry.lean:416`). -/
@[simp]
theorem transferNormNaturalityTransferNormOrbitEquiv_mk
    (D : DegreeData G) [IsTopologicalGroup G] [CompactSpace G]
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below))
    (k : E.base.field.toSubgroup) :
    D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ
        (Quotient.mk'' (QuotientGroup.mk
          (QuotientGroup.mk k : E.base.field.toSubgroup ⧸
            D.extensionInertiaWithin E.base.field L (hL.trans E.below)) :
          (E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
            (hL.trans E.below)) ⧸
              D.transferNormNaturalityFrobeniusIntermediateSubgroup
                E L hL)) =
      Quotient.mk'' (QuotientGroup.mk k⁻¹ :
        E.base.field.toSubgroup ⧸
            (D.frobeniusFixedField E.base L (hL.trans E.below) σ).toSubgroup.subgroupOf
              E.base.field.toSubgroup) := by
  unfold transferNormNaturalityTransferNormOrbitEquiv
  simp only [Equiv.trans_apply, orbitQuotientSwapEquiv_mk,
    orbitQuotientClosedCyclicEquiv_mk,
    orbitQuotientEquivOfSurjectiveEquivariant_mk,
    orbitQuotientEquivOfSurjectiveEquivariant_symm_mk,
    Subgroup.quotientEquivOfEq_mk]
  apply congrArg Quotient.mk''
  exact (D.frobeniusFixedCosetClosureEquiv E.base L
    (hL.trans E.below) σ).symm_apply_apply (QuotientGroup.mk k⁻¹)

/-- **On the chosen transfer representative `t`, the equivalence is the
norm orbit of `t⁻¹`** (Yamaguchi 2026,
`MainTransferFrobeniusGeometry.lean:450`). -/
theorem transferNormNaturalityTransferNormOrbitEquiv_apply
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
    D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ q =
      Quotient.mk'' (QuotientGroup.mk (Quotient.out q.out.out)⁻¹ :
        E.base.field.toSubgroup ⧸
            (D.frobeniusFixedField E.base L (hL.trans E.below) σ).toSubgroup.subgroupOf
              E.base.field.toSubgroup) := by
  let orbitEquiv := D.transferNormNaturalityTransferNormOrbitEquiv E L hL σ
  calc
    orbitEquiv q = orbitEquiv (Quotient.mk'' q.out) :=
      congrArg orbitEquiv (Quotient.out_eq' q).symm
    _ = orbitEquiv (Quotient.mk'' (QuotientGroup.mk q.out.out)) :=
      congrArg orbitEquiv (congrArg Quotient.mk'' (Quotient.out_eq' q.out).symm)
    _ = orbitEquiv (Quotient.mk'' (QuotientGroup.mk
        (QuotientGroup.mk (Quotient.out q.out.out)))) :=
      congrArg orbitEquiv (congrArg Quotient.mk''
        (congrArg QuotientGroup.mk (Quotient.out_eq' q.out.out).symm))
    _ = _ := D.transferNormNaturalityTransferNormOrbitEquiv_mk
      E L hL σ (Quotient.out q.out.out)

end DegreeData

end

end Atlas.Knowledge
