import Mathlib
import Atlas.Knowledge.AbstractExtension
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbelianSubextension
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.NormalizedDegree
import Atlas.Knowledge.ProfiniteInteger

/-!
# unramified extension of a degree

The canonical unramified extension of a given degree `f` of a
finite-residue abstract field `K` in a class formation with degree
datum (#104): the closed subgroup of `G_K` on which the normalized
degree `d_K`, reduced modulo `f`, vanishes, packaged as a finite Galois
subextension — its relative quotient is the reduction's image `ℤ/f`, so
it is abelian of degree `f`, and it contains inertia, so it is
unramified of residue degree `f`. The unramified factor of the
existence theorem's Lubin–Tate route, whose norm subgroup is measured
by the valuation datum in `Atlas.Knowledge.UnramifiedNormContainment`.

## Main definitions

* `DegreeData.unramifiedDegreeHom`,
  `DegreeData.unramifiedDegreeKernelWithin` — the normalized degree
  reduced modulo `f`, and its kernel.
* `DegreeData.unramifiedExtensionOfDegree` — the closed subgroup the
  kernel represents.
* `DegreeData.finiteUnramifiedExtension`,
  `DegreeData.finiteUnramifiedAbelianExtension` — the extension
  packaged as a finite Galois, then finite abelian, subextension.

## Main statements

* `DegreeData.unramifiedDegreeHom_surjective` — the reduced degree is
  onto `ℤ/f`; proved.
* `DegreeData.unramifiedExtensionOfDegree_isUnramified` — the extension
  is unramified; proved.
* `DegreeData.finiteUnramifiedExtension_degree`,
  `DegreeData.finiteUnramifiedExtension_residueDegree` — its degree and
  residue degree are `f`; proved.

## Implementation notes

The reduction modulo `f` is the layer's
`Atlas.Knowledge.ProfiniteInteger.reduction` composed inline with
`Multiplicative.ofAdd` in `unramifiedDegreeHom`, whose continuity is
the layer's `continuous_reduction`, where the source composes a named
`zHatReductionMul`; the positivity of `f` is carried as `NeZero f`
throughout, as the valuation datum's own fields carry their moduli,
where the source passes `0 < f`. The relative subgroup is the layer's
`Subgroup.subgroupOf` spelling, so the source's `extensionSubgroup_…`
names read `subgroupOf_…` here and `mem_extensionSubgroup_iff` becomes
Mathlib's `Subgroup.mem_subgroupOf`; the abstract extension is
Mathlib-style `AbstractExtension.mk` as in the source. The file is the
source's
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean`
`:30`–`:312`, the first of its two halves; the second, the continuity
of the valuation for the norm topology, is the continuity-fork material
the arc strips. Everything else ports token-for-token.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Reduction modulo `f` after the normalized degree `d_K` of the base
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:30`]
[Yamaguchi2026]). -/
def unramifiedDegreeHom (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (f : ℕ) [NeZero f] :
    K.field.toSubgroup →ₜ* Multiplicative (ZMod f) where
  toFun k := Multiplicative.ofAdd (ProfiniteInteger.reduction f (D.normalizedDegree K k).toAdd)
  map_one' := by simp
  map_mul' := by
    intro x y
    simp [map_mul, toAdd_mul, map_add, ofAdd_add]
  continuous_toFun :=
    continuous_ofAdd.comp ((ProfiniteInteger.continuous_reduction f).comp
      (continuous_toAdd.comp (D.normalizedDegree K).continuous))

/-- The subgroup of `G_K` fixing the degree-`f` unramified extension
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:36`]
[Yamaguchi2026]). -/
def unramifiedDegreeKernelWithin (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (f : ℕ) [NeZero f] :
    Subgroup K.field.toSubgroup :=
  (unramifiedDegreeHom D K f).toMonoidHom.ker

/-- The defining kernel equation for the reduction subgroup, by
definition ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:42`]
[Yamaguchi2026]). -/
theorem unramifiedDegreeKernelWithin_eq_ker (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (f : ℕ) [NeZero f] :
    unramifiedDegreeKernelWithin D K f =
      (unramifiedDegreeHom D K f).toMonoidHom.ker := by
  rfl

/-- The kernel of normalized degree modulo a positive integer is closed
inside the finite-residue field subgroup ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:52`]
[Yamaguchi2026]). -/
theorem unramifiedDegreeKernelWithin_isClosed (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (f : ℕ) [NeZero f] :
    IsClosed (unramifiedDegreeKernelWithin D K f :
      Set K.field.toSubgroup) := by
  change IsClosed
    ((unramifiedDegreeHom D K f) ⁻¹' ({1} :
      Set (Multiplicative (ZMod f))))
  exact isClosed_singleton.preimage
    (unramifiedDegreeHom D K f).continuous_toFun

/-- **The actual fixed field of the reduction-modulo-`f` kernel of
`d_K`** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:64`]
[Yamaguchi2026]). -/
def unramifiedExtensionOfDegree (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D)
    (f : ℕ) [NeZero f] : ClosedSubgroup G where
  toSubgroup :=
    (unramifiedDegreeKernelWithin D K f).map K.field.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      (Subtype.val ''
        (unramifiedDegreeKernelWithin D K f : Set K.field.toSubgroup))
    exact K.field.isClosed'.isClosedEmbedding_subtypeVal.isClosedMap _
      (unramifiedDegreeKernelWithin_isClosed D K f)

/-- Membership in the unramified extension of degree `f` is membership
of a representative in the reduction kernel ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:81`]
[Yamaguchi2026]). -/
@[simp]
theorem mem_unramifiedExtensionOfDegree_iff (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) [NeZero f] (g : G) :
    g ∈ unramifiedExtensionOfDegree D K f ↔
      ∃ k : K.field.toSubgroup,
        k ∈ unramifiedDegreeKernelWithin D K f ∧ k.1 = g :=
  Iff.rfl

/-- The unramified extension of degree `f` lies over the base `K`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:90`]
[Yamaguchi2026]). -/
theorem unramifiedExtensionOfDegree_le (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) [NeZero f] :
    (unramifiedExtensionOfDegree D K f).toSubgroup ≤
      K.field.toSubgroup := by
  rintro g ⟨k, _, rfl⟩
  exact k.2

/-- The relative subgroup of the unramified extension of degree `f` is
the reduction kernel ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:102`]
[Yamaguchi2026]). -/
theorem subgroupOf_unramifiedExtensionOfDegree (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) [NeZero f] :
    (unramifiedExtensionOfDegree D K f).toSubgroup.subgroupOf K.field.toSubgroup =
      unramifiedDegreeKernelWithin D K f := by
  ext k
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro hk
    obtain ⟨t, ht, hts⟩ := hk
    have htk : t = k := by
      apply Subtype.ext
      exact hts
    simpa [htk] using ht
  · intro hk
    exact ⟨k, hk, rfl⟩

/-- The reduced normalized degree is surjective ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:120`]
[Yamaguchi2026]). -/
theorem unramifiedDegreeHom_surjective (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (f : ℕ) [NeZero f] :
    Function.Surjective (unramifiedDegreeHom D K f) := by
  intro z
  obtain ⟨w, hw⟩ := ProfiniteInteger.reduction_surjective f z.toAdd
  obtain ⟨k, hk⟩ :=
    D.normalizedDegree_surjective K (Multiplicative.ofAdd w)
  refine ⟨k, ?_⟩
  apply Multiplicative.ext
  change ProfiniteInteger.reduction f (D.normalizedDegree K k).toAdd = z.toAdd
  rw [hk]
  exact hw

/-- The extension subgroup of the canonical unramified degree-`f`
extension is normal ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:137`]
[Yamaguchi2026]). -/
instance unramifiedExtensionOfDegree_normal (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) [NeZero f] :
    ((unramifiedExtensionOfDegree D K f).toSubgroup.subgroupOf K.field.toSubgroup).Normal := by
  rw [subgroupOf_unramifiedExtensionOfDegree D K f]
  change (unramifiedDegreeHom D K f).toMonoidHom.ker.Normal
  infer_instance

/-- **The reduction kernel packages an actual finite Galois extension
of `K`** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:147`]
[Yamaguchi2026]). -/
def finiteUnramifiedExtension (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D)
    (f : ℕ) [NeZero f] : FiniteGaloisSubextension K.field where
  field := unramifiedExtensionOfDegree D K f
  below := unramifiedExtensionOfDegree_le D K f
  normal := inferInstance
  finite := by
    rw [subgroupOf_unramifiedExtensionOfDegree D K f]
    letI : Finite (Multiplicative (ZMod f)) := by
      change Finite (ZMod f)
      infer_instance
    let q := (unramifiedDegreeHom D K f).toMonoidHom
    exact Finite.of_injective
      (QuotientGroup.quotientKerEquivOfSurjective q
        (unramifiedDegreeHom_surjective D K f))
      (QuotientGroup.quotientKerEquivOfSurjective q
        (unramifiedDegreeHom_surjective D K f)).injective

/-- The extension subgroup carried by the bundled finite unramified
extension is the reduction kernel that constructed it ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:168`]
[Yamaguchi2026]). -/
theorem subgroupOf_finiteUnramifiedExtension
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (f : ℕ) [NeZero f] :
    (D.finiteUnramifiedExtension K f).field.toSubgroup.subgroupOf K.field.toSubgroup =
      unramifiedDegreeKernelWithin D K f := by
  simpa only [finiteUnramifiedExtension] using
    subgroupOf_unramifiedExtensionOfDegree D K f

/-- **The finite unramified extension is abelian**: its Galois quotient
is the cyclic quotient detected by the normalized degree modulo `f`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:179`]
[Yamaguchi2026]). -/
def finiteUnramifiedAbelianExtension (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D)
    (f : ℕ) [NeZero f] : FiniteAbelianSubextension K.field where
  toFiniteGaloisExtension := finiteUnramifiedExtension D K f
  commutative := by
    letI :
        ((D.finiteUnramifiedExtension K f).field.toSubgroup.subgroupOf
          K.field.toSubgroup).Normal :=
      (D.finiteUnramifiedExtension K f).normal
    change IsMulCommutative
      (K.field.toSubgroup ⧸
        (D.finiteUnramifiedExtension K f).field.toSubgroup.subgroupOf K.field.toSubgroup)
    let q := (unramifiedDegreeHom D K f).toMonoidHom
    have hsub :
        (D.finiteUnramifiedExtension K f).field.toSubgroup.subgroupOf K.field.toSubgroup =
          q.ker := by
      rw [D.subgroupOf_finiteUnramifiedExtension K f,
        D.unramifiedDegreeKernelWithin_eq_ker K f]
    let e :
        (K.field.toSubgroup ⧸
            (D.finiteUnramifiedExtension K f).field.toSubgroup.subgroupOf
              K.field.toSubgroup) ≃*
          Multiplicative (ZMod f) :=
      (QuotientGroup.quotientMulEquivOfEq hsub).trans
        (QuotientGroup.quotientKerEquivOfSurjective q
          (unramifiedDegreeHom_surjective D K f))
    exact
      { is_comm.comm := fun x y => by
          apply e.injective
          rw [map_mul, map_mul, mul_comm] }

/-- Forgetting commutativity from the abelian package recovers the
canonical finite unramified Galois extension ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:219`]
[Yamaguchi2026]). -/
@[simp]
theorem finiteUnramifiedAbelianExtension_toFiniteGaloisExtension
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D)
    (f : ℕ) [NeZero f] :
    (D.finiteUnramifiedAbelianExtension K f).toFiniteGaloisExtension =
      D.finiteUnramifiedExtension K f := by
  rfl

/-- The reduction kernel contains inertia, so its fixed field is
unramified ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:228`]
[Yamaguchi2026]). -/
theorem unramifiedExtensionOfDegree_isUnramified (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) [NeZero f] :
    (AbstractExtension.mk (unramifiedExtensionOfDegree D K f) K.field
      (unramifiedExtensionOfDegree_le D K f)).IsUnramified D := by
  rw [(AbstractExtension.mk
    (unramifiedExtensionOfDegree D K f) K.field
    (unramifiedExtensionOfDegree_le D K f)).isUnramified_iff_inertia_le D]
  rintro g ⟨hgK, hgI⟩
  let k : K.field.toSubgroup := ⟨g, hgK⟩
  have hkI : k ∈ D.fieldInertiaWithin K.field := hgI
  have hkDegree : D.normalizedDegree K k = 1 := by
    have hkKer : k ∈ (D.normalizedDegree K).toMonoidHom.ker := by
      rw [D.normalizedDegree_ker K]
      exact hkI
    exact hkKer
  have hkReduction :
      k ∈ unramifiedDegreeKernelWithin D K f := by
    change unramifiedDegreeHom D K f k = 1
    change Multiplicative.ofAdd (ProfiniteInteger.reduction f (D.normalizedDegree K k).toAdd) = 1
    rw [hkDegree]
    simp
  exact ⟨k, hkReduction, rfl⟩

/-- **The finite extension cut out by reduction modulo `f` has degree
`f`** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:253`]
[Yamaguchi2026]). -/
theorem finiteUnramifiedExtension_degree (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) [NeZero f] :
    (((finiteUnramifiedExtension D K f).toFiniteAbstractExtension.degree : ℕ)) = f := by
  letI : Fintype (ZMod f) := ZMod.fintype f
  let q := (unramifiedDegreeHom D K f).toMonoidHom
  rw [← (finiteUnramifiedExtension D K f).toFiniteAbstractExtension.subgroup_index_eq_degree]
  change ((D.finiteUnramifiedExtension K f).field.toSubgroup.subgroupOf
    K.field.toSubgroup).index = f
  rw [D.subgroupOf_finiteUnramifiedExtension K f]
  rw [D.unramifiedDegreeKernelWithin_eq_ker K f]
  rw [Subgroup.index_ker]
  rw [MonoidHom.range_eq_top_of_surjective q
    (unramifiedDegreeHom_surjective D K f)]
  calc
    Nat.card (↑(⊤ : Subgroup (Multiplicative (ZMod f)))) =
        Nat.card (Multiplicative (ZMod f)) :=
      Nat.card_congr
        { toFun := fun x ↦ x.1
          invFun := fun x ↦ ⟨x, Subgroup.mem_top x⟩
          left_inv := fun x ↦ Subtype.ext rfl
          right_inv := fun _ ↦ rfl }
    _ = Nat.card (ZMod f) :=
      Nat.card_congr
        { toFun := Multiplicative.toAdd
          invFun := Multiplicative.ofAdd
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl }
    _ = f := Nat.card_zmod f

/-- Thus the positive relative residue degree is `f` as well
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ValuationContinuity.lean:286`]
[Yamaguchi2026]). -/
theorem finiteUnramifiedExtension_residueDegree (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D)
    (f : ℕ) [NeZero f] :
    (((finiteUnramifiedExtension D K f).toFiniteAbstractExtension.residueDegree D : ℕ)) = f := by
  let E := (finiteUnramifiedExtension D K f).toFiniteAbstractExtension
  have hE : E.IsUnramified D := by
    simpa [E, finiteUnramifiedExtension,
      FiniteGaloisSubextension.toFiniteAbstractExtension] using
      unramifiedExtensionOfDegree_isUnramified D K f
  rw [E.residueDegree_eq_degree_of_isUnramified D hE]
  exact finiteUnramifiedExtension_degree D K f

end DegreeData

end

end Atlas.Knowledge
