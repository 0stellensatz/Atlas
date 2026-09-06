import Mathlib
import Atlas.Knowledge.AbstractReciprocityEquiv
import Atlas.Knowledge.AbstractReciprocityTheorem
import Atlas.Knowledge.ClassFieldAxiom
import Atlas.Knowledge.ClassFieldCandidate
import Atlas.Knowledge.FiniteAbelianSubextension
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityHom
import Atlas.Knowledge.FiniteReciprocityNaturalityNorm
import Atlas.Knowledge.NormSubgroupMap
import Atlas.Knowledge.NormTopology
import Atlas.Knowledge.ReciprocityExactRows
import Atlas.Knowledge.UnitCohomologyAxiom

/-!
# finite abelian classification

The finite abelian classification theorem of a class formation
satisfying the class field axiom (#104): the finite abelian extensions
`L / K` of a base `K` finite over the distinguished base correspond
order-reversingly to the open subgroups of `A_K` in the norm topology —
`L ↦ N_{L/K} A_L` is an order isomorphism onto the opposite poset —
with the norm laws `N_{L₁L₂} = N_{L₁} ∩ N_{L₂}` and
`N_{L₁ ∩ L₂} = N_{L₁} N_{L₂}`. Finite reciprocity supplies the vertical
isomorphisms: the compositum law by the joint injectivity of the two
restrictions, re-derived inline on representatives, order reversal by
recovering a field from the order of its finite quotient, and
surjectivity through the class field candidate, whose norm subgroup is
shown to be exactly the given open subgroup. This is the abstract half
of the finite local existence theorem; its local specialization is the
next brick.

## Main definitions

* `FiniteAbelianSubextension.normSubgroupOrderIso` — the order
  isomorphism `L ↦ N_{L/K} A_L` onto the opposite poset of norm-open
  subgroups.

## Main statements

* `FiniteAbelianSubextension.normSubgroup_compositum`,
  `FiniteAbelianSubextension.normSubgroup_intersection` — the two norm
  laws; proved.
* `FiniteAbelianSubextension.le_iff_normSubgroup_le` — field inclusion
  is reverse inclusion of norm subgroups; proved.
* `FiniteAbelianSubextension.normSubgroupMap_bijective` — the norm
  subgroup map is bijective, with its `_injective` and `_surjective`
  halves; proved.
* `FiniteAbelianSubextension.normSubgroupOrderIso_apply` — the order
  isomorphism is `normSubgroupMap` on the nose; `rfl`.
* `FiniteAbelianSubextension.classFieldCandidate_normSubgroup_eq` — the
  class field candidate of a norm-open `H` has norm subgroup exactly
  `H`; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`mem_extensionSubgroup_iff` becoming Mathlib's
`Subgroup.mem_subgroupOf`, and the ambient group is `Type u` with the
class-formation stock. The file is the reciprocity half of the source's
`FiniteAbelianClassification.lean`, whose reciprocity-free half is
`Atlas.Knowledge.NormSubgroupMap`; the split leaves the source's five
local instances re-declared here under `chase_` names, the source's
names being that item's, whose `local` scoping does not reach this
file. Two conventions of the layer's reciprocity items apply
throughout: the unit-cohomology input
`hAxiom : v.SatisfiesUnramifiedUnitCohomology D` is threaded as an
explicit hypothesis beside the class field axiom `hcf` where the source
derives it by `classFieldAxiom_implies_unramifiedUnitCohomology` (the
decision recorded in `Atlas.Knowledge.AbstractReciprocityEquiv`'s
notes), so the nine public declarations carry the extra binder, the
source's `let hAxiom := …` lines are gone, and the two proofs that
consisted of that line and an `exact` are the term; and the source's
`[T2Space G]` is shed (the continuing cascade). `normResidueSymbol` and
`abstractReciprocityEquiv_apply_of` take that `hAxiom` in the same way.
The three same-base naturality rewrites name their arguments —
`A K.field L₁.field P.field hP₁ L₁.below` and its two companions —
where the source leaves the base containment `hMK` to be found by later
unification, since the goal that unification leaves open is one the
layer's `multiGoal` linter reports;
`Atlas.Knowledge.AbstractReciprocityTheorem` rewrites the same way.
`normSubgroupOrderIso` is a plain `def` under the file's
`noncomputable section`, the source's `noncomputable def` under its
own. Everything else ports token-for-token; the file is the source's
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`
`:90`, `:411`, `:591`, and `:746`–`:930`, with the five local instances
of its `:28`, `:34`, `:514`, `:519`, and `:524`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The relative subgroup of a finite abelian subextension is normal,
as an instance local to the section — the source's name is taken by
`Atlas.Knowledge.NormSubgroupMap`'s own local instance, whose `local`
scoping does not reach here (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:28`). -/
local instance chase_extensionQuotient_normal
    (L : FiniteAbelianSubextension K) :
    (L.field.toSubgroup.subgroupOf K.toSubgroup).Normal :=
  L.normal

/-- The relative quotient of a finite abelian subextension is finite,
as an instance local to the section — the source's name is taken by
`Atlas.Knowledge.NormSubgroupMap`'s own local instance, whose `local`
scoping does not reach here (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:34`). -/
local instance chase_representedQuotient_finite
    (L : FiniteAbelianSubextension K) :
    Finite (K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup) :=
  L.finite

/-- **The finite classification compositum argument**, isolated as a
private diagram chase; the final public theorem supplies the three
bijectivity facts directly from finite reciprocity, so they are not
exposed as hypotheses of the classification (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:90`). -/
private theorem normSubgroup_compositum_eq_inf_of_reciprocity_bijective
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (L₁ L₂ : FiniteAbelianSubextension K.field)
    (hbij₁ : Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K L₁.field L₁.below))
    (hbij₂ : Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K L₂.field L₂.below))
    (hbijP : Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K (L₁.compositum L₂).field
        (L₁.compositum L₂).below)) :
    (L₁.compositum L₂).normSubgroup A =
      L₁.normSubgroup A ⊓ L₂.normSubgroup A := by
  let P := L₁.compositum L₂
  let hP₁ : P.field.toSubgroup ≤ L₁.field.toSubgroup := by
    change (L₁.field.toSubgroup ⊓ L₂.field.toSubgroup) ≤
      L₁.field.toSubgroup
    exact inf_le_left
  let hP₂ : P.field.toSubgroup ≤ L₂.field.toSubgroup := by
    change (L₁.field.toSubgroup ⊓ L₂.field.toSubgroup) ≤
      L₂.field.toSubgroup
    exact inf_le_right
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  letI : Finite
      (K.field.toSubgroup ⧸ K.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    (FiniteGaloisSubextension.refl K.field).finite
  apply le_antisymm
  · exact normSubgroup_compositum_le_inf A L₁ L₂
  · intro a ha
    have ha₁ : a ∈ finiteNormSubgroup A K.field L₁.field L₁.below := by
      simpa [FiniteAbelianSubextension.normSubgroup] using ha.1
    have ha₂ : a ∈ finiteNormSubgroup A K.field L₂.field L₂.below := by
      simpa [FiniteAbelianSubextension.normSubgroup] using ha.2
    let z : FiniteNormQuotient A K.field P.field P.below :=
      finiteNormClass A K.field P.field P.below a
    obtain ⟨σ, hσ⟩ := hbijP.2 z
    have hz₁ :
        abstractReciprocityNormProjection A K.field L₁.field P.field hP₁ L₁.below z =
          0 := by
      rw [abstractReciprocityNormProjection_finiteNormClass]
      exact (finiteNormClass_eq_zero_iff A K.field L₁.field L₁.below a).2 ha₁
    have hz₂ :
        abstractReciprocityNormProjection A K.field L₂.field P.field hP₂ L₂.below z =
          0 := by
      rw [abstractReciprocityNormProjection_finiteNormClass]
      exact (finiteNormClass_eq_zero_iff A K.field L₂.field L₂.below a).2 ha₂
    have hnat₁ := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EKK L₁.field P.field L₁.below P.below hP₁
    have hnat₂ := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EKK L₂.field P.field L₂.below P.below hP₂
    rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection
        A K.field L₁.field P.field hP₁ L₁.below,
      finiteReciprocityNaturalityRestriction_sameBase_eq_restriction
        K.field L₁.field P.field hP₁ L₁.below] at hnat₁
    rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection
        A K.field L₂.field P.field hP₂ L₂.below,
      finiteReciprocityNaturalityRestriction_sameBase_eq_restriction
        K.field L₂.field P.field hP₂ L₂.below] at hnat₂
    have hres₁ :
        (abstractReciprocityRestriction K.field L₁.field P.field hP₁
          L₁.below).toAdditive
            σ = 0 := by
      apply hbij₁.1
      calc
        D.finiteReciprocityHom A v hAxiom K L₁.field L₁.below
            ((abstractReciprocityRestriction K.field L₁.field P.field hP₁
              L₁.below).toAdditive σ) =
            abstractReciprocityNormProjection A K.field L₁.field P.field hP₁
              L₁.below
                (D.finiteReciprocityHom A v hAxiom K P.field P.below σ) := by
                  exact (DFunLike.congr_fun hnat₁ σ).symm
        _ = abstractReciprocityNormProjection A K.field L₁.field P.field hP₁
              L₁.below z := congrArg _ hσ
        _ = 0 := hz₁
        _ = D.finiteReciprocityHom A v hAxiom K L₁.field L₁.below 0 :=
          (map_zero _).symm
    have hres₂ :
        (abstractReciprocityRestriction K.field L₂.field P.field hP₂
          L₂.below).toAdditive
            σ = 0 := by
      apply hbij₂.1
      calc
        D.finiteReciprocityHom A v hAxiom K L₂.field L₂.below
            ((abstractReciprocityRestriction K.field L₂.field P.field hP₂
              L₂.below).toAdditive σ) =
            abstractReciprocityNormProjection A K.field L₂.field P.field hP₂
              L₂.below
                (D.finiteReciprocityHom A v hAxiom K P.field P.below σ) := by
                  exact (DFunLike.congr_fun hnat₂ σ).symm
        _ = abstractReciprocityNormProjection A K.field L₂.field P.field hP₂
              L₂.below z := congrArg _ hσ
        _ = 0 := hz₂
        _ = D.finiteReciprocityHom A v hAxiom K L₂.field L₂.below 0 :=
          (map_zero _).symm
    have hleft :
        abstractReciprocityRestriction K.field L₁.field P.field hP₁
          L₁.below σ.toMul =
          1 := by
      exact congrArg Additive.toMul hres₁
    have hright :
        abstractReciprocityRestriction K.field L₂.field P.field hP₂
          L₂.below σ.toMul =
          1 := by
      exact congrArg Additive.toMul hres₂
    have hσMul : σ.toMul = 1 := by
      let k : K.field.toSubgroup := Quotient.out σ.toMul
      have hkleft : k ∈ L₁.field.toSubgroup.subgroupOf K.field.toSubgroup := by
        apply (QuotientGroup.eq_one_iff k).1
        have := hleft
        rw [← Quotient.out_eq' σ.toMul] at this
        exact this
      have hkright : k ∈ L₂.field.toSubgroup.subgroupOf K.field.toSubgroup := by
        apply (QuotientGroup.eq_one_iff k).1
        have := hright
        rw [← Quotient.out_eq' σ.toMul] at this
        exact this
      have hkP : k ∈ P.field.toSubgroup.subgroupOf K.field.toSubgroup := by
        apply Subgroup.mem_subgroupOf.2
        exact ⟨
          Subgroup.mem_subgroupOf.1 hkleft,
          Subgroup.mem_subgroupOf.1 hkright⟩
      calc
        σ.toMul = QuotientGroup.mk k := (Quotient.out_eq' σ.toMul).symm
        _ = 1 := (QuotientGroup.eq_one_iff k).2 hkP
    have hσzero : σ = 0 := by
      apply Additive.ext
      exact hσMul
    have hz : z = 0 := by
      calc
        z = D.finiteReciprocityHom A v hAxiom K P.field P.below σ := hσ.symm
        _ = D.finiteReciprocityHom A v hAxiom K P.field P.below 0 :=
          congrArg _ hσzero
        _ = 0 := map_zero _
    change a ∈ finiteNormSubgroup A K.field P.field P.below
    exact (finiteNormClass_eq_zero_iff A K.field P.field P.below a).1 hz

/-- The order-reversing finite classification argument, kept private
until the public finite abelian classification theorem supplies the
compositum formula and the two reciprocity bijectivities from finite
reciprocity (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:411`). -/
private theorem le_iff_normSubgroup_le_of_compositum_and_reciprocity
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (L₁ L₂ : FiniteAbelianSubextension K.field)
    (hcomp : (L₁.compositum L₂).normSubgroup A =
      L₁.normSubgroup A ⊓ L₂.normSubgroup A)
    (hbijP : Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K (L₁.compositum L₂).field
        (L₁.compositum L₂).below))
    (hbij₂ : Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K L₂.field L₂.below)) :
    L₁ ≤ L₂ ↔ L₂.normSubgroup A ≤ L₁.normSubgroup A := by
  constructor
  · exact normSubgroup_antitone A
  · intro hnorm
    let P := L₁.compositum L₂
    have hNP : P.normSubgroup A = L₂.normSubgroup A := by
      calc
        P.normSubgroup A = L₁.normSubgroup A ⊓ L₂.normSubgroup A := hcomp
        _ = L₂.normSubgroup A := inf_eq_right.mpr hnorm
    letI hPfinite : Finite
        (K.field.toSubgroup ⧸ P.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
      P.finite
    letI hL₂finite : Finite
        (K.field.toSubgroup ⧸ L₂.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
      L₂.finite
    letI hPNormFinite : Finite
        (FiniteNormQuotient A K.field P.field P.below) :=
      Finite.of_surjective
        (D.finiteReciprocityHom A v hAxiom K P.field P.below) hbijP.2
    letI hL₂NormFinite : Finite
        (FiniteNormQuotient A K.field L₂.field L₂.below) :=
      Finite.of_surjective
        (D.finiteReciprocityHom A v hAxiom K L₂.field L₂.below) hbij₂.2
    have hnormCard :
        Nat.card (FiniteNormQuotient A K.field P.field P.below) =
          Nat.card (FiniteNormQuotient A K.field L₂.field L₂.below) := by
      apply Nat.card_congr
      exact ((finiteNormQuotientConcreteEquiv A K.field P.field P.below).trans
        ((QuotientAddGroup.quotientAddEquivOfEq (by
          simpa [FiniteAbelianSubextension.normSubgroup] using hNP)).trans
          (finiteNormQuotientConcreteEquiv A K.field L₂.field L₂.below).symm)).toEquiv
    have hPcard :
        Nat.card P.extensionQuotient =
          Nat.card (FiniteNormQuotient A K.field P.field P.below) := by
      change Nat.card (Additive P.extensionQuotient) =
        Nat.card (FiniteNormQuotient A K.field P.field P.below)
      exact Nat.card_congr (Equiv.ofBijective _ hbijP)
    have hL₂card :
        Nat.card L₂.extensionQuotient =
          Nat.card (FiniteNormQuotient A K.field L₂.field L₂.below) := by
      change Nat.card (Additive L₂.extensionQuotient) =
        Nat.card (FiniteNormQuotient A K.field L₂.field L₂.below)
      exact Nat.card_congr (Equiv.ofBijective _ hbij₂)
    have hcard : Nat.card P.extensionQuotient =
        Nat.card L₂.extensionQuotient :=
      hPcard.trans (hnormCard.trans hL₂card.symm)
    have hL₂P : L₂ = P :=
      eq_of_le_of_extensionQuotient_card_eq
        (le_compositum_right L₁ L₂) hcard
    rw [hL₂P]
    exact le_compositum_left L₁ L₂

end FiniteAbelianSubextension

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G} [IsTopologicalGroup G]

/-- The relative quotient of a finite Galois subextension is finite, as
an instance local to the section — the source's name is taken by
`Atlas.Knowledge.NormSubgroupMap`'s own local instance, whose `local`
scoping does not reach here (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:514`). -/
local instance chase_extensionQuotient_finite
    (E : FiniteGaloisSubextension K) :
    Finite (K.toSubgroup ⧸ E.field.toSubgroup.subgroupOf K.toSubgroup) :=
  E.finite

/-- The relative subgroup of a finite abelian subextension is normal,
as an instance local to the section — the source's name is taken by
`Atlas.Knowledge.NormSubgroupMap`'s own local instance, whose `local`
scoping does not reach here (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:519`). -/
local instance chase_abelianExtension_normal
    (M : FiniteAbelianSubextension K) :
    (M.field.toSubgroup.subgroupOf K.toSubgroup).Normal :=
  M.normal

/-- The relative quotient of a finite abelian subextension is finite,
as an instance local to the section — the source's name is taken by
`Atlas.Knowledge.NormSubgroupMap`'s own local instance, whose `local`
scoping does not reach here (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:524`). -/
local instance chase_abelianExtension_finite
    (M : FiniteAbelianSubextension K) :
    Finite (K.toSubgroup ⧸ M.field.toSubgroup.subgroupOf K.toSubgroup) :=
  M.finite

/-- **The finite classification surjectivity diagram chase.** The final
public theorem feeds `rE` and its compatibility from finite
reciprocity, so neither appears as an assumption of the classification
endpoint (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:591`). -/
private theorem classFieldCandidate_normSubgroup_eq_of_reciprocity
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (E : FiniteGaloisSubextension K.field)
    (H : AddSubgroup (ambientFixedAddSubgroup A K.field))
    (hEH : normSubgroup A E ≤ H)
    (rE : FiniteNormQuotient A K.field E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (hcompatE : ∀ q : E.extensionQuotient,
      rE.symm (Additive.ofMul (Abelianization.of q)) =
        D.finiteReciprocityHom A v hAxiom K E.field E.below
          (Additive.ofMul q))
    (hbijM : Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K
        (classFieldCandidate A E H rE).field
        (classFieldCandidate A E H rE).below)) :
    (classFieldCandidate A E H rE).normSubgroup A = H := by
  let S := reciprocityPreimageSubgroup A E H rE
  let M := classFieldCandidate A E H rE
  let hEM := classFieldCandidate_field_le E A H rE
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  letI : Finite
      (K.field.toSubgroup ⧸ K.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    (FiniteGaloisSubextension.refl K.field).finite
  have hnat := D.finiteReciprocityNaturality_restriction_norm_commutes
    A v hAxiom EKK M.field E.field M.below E.below hEM
  rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection
      A K.field M.field E.field hEM M.below,
    finiteReciprocityNaturalityRestriction_sameBase_eq_restriction
      K.field M.field E.field hEM M.below]
      at hnat
  ext a
  have haClass :=
    reciprocityClass_mem_preimageSubgroup_iff A E H hEH rE a
  let zE : FiniteNormQuotient A K.field E.field E.below :=
    finiteNormClass A K.field E.field E.below a
  let ab : Additive (Abelianization E.extensionQuotient) := rE zE
  let q : E.extensionQuotient := Quotient.out ab.toMul
  let zM : FiniteNormQuotient A K.field M.field M.below :=
    finiteNormClass A K.field M.field M.below a
  have hab : Additive.ofMul (Abelianization.of q) = ab := by
    apply Additive.ext
    exact Quotient.out_eq' ab.toMul
  have hrecE :
      D.finiteReciprocityHom A v hAxiom K E.field E.below
          (Additive.ofMul q) = zE := by
    rw [← hcompatE q, hab, AddEquiv.symm_apply_apply]
  have hcomm :
      D.finiteReciprocityHom A v hAxiom K M.field M.below
          ((abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
            (Additive.ofMul q)) = zM := by
    calc
      D.finiteReciprocityHom A v hAxiom K M.field M.below
          ((abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
            (Additive.ofMul q)) =
        abstractReciprocityNormProjection A K.field M.field E.field hEM M.below
          (D.finiteReciprocityHom A v hAxiom K E.field E.below
            (Additive.ofMul q)) := by
              exact (DFunLike.congr_fun hnat (Additive.ofMul q)).symm
      _ = abstractReciprocityNormProjection A K.field M.field E.field hEM M.below zE :=
        congrArg _ hrecE
      _ = zM := by
        rw [abstractReciprocityNormProjection_finiteNormClass]
  change a ∈ finiteNormSubgroup A K.field M.field M.below ↔ a ∈ H
  constructor
  · intro haM
    have hzM : zM = 0 :=
      (finiteNormClass_eq_zero_iff A K.field M.field M.below a).2 haM
    have hresZero :
        (abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
            (Additive.ofMul q) = 0 := by
      apply hbijM.1
      calc
        D.finiteReciprocityHom A v hAxiom K M.field M.below
            ((abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
              (Additive.ofMul q)) = zM := hcomm
        _ = 0 := hzM
        _ = D.finiteReciprocityHom A v hAxiom K M.field M.below 0 :=
          (map_zero _).symm
    have hresOne :
        abstractReciprocityRestriction K.field M.field E.field hEM M.below q = 1 := by
      exact congrArg Additive.toMul hresZero
    apply haClass.1
    have hqS :=
      (classFieldCandidate_restriction_eq_one_iff E A H rE q).1
        hresOne
    convert hqS using 1; rfl
  · intro haH
    have hqS : q ∈ S := by
      apply haClass.2 at haH
      convert haH using 1; rfl
    have hresOne :
        abstractReciprocityRestriction K.field M.field E.field hEM M.below q = 1 :=
      (classFieldCandidate_restriction_eq_one_iff E A H rE q).2 hqS
    have hresZero :
        (abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
            (Additive.ofMul q) = 0 := by
      exact congrArg Additive.ofMul hresOne
    have hzM : zM = 0 := by
      calc
        zM = D.finiteReciprocityHom A v hAxiom K M.field M.below
            ((abstractReciprocityRestriction K.field M.field E.field hEM M.below).toAdditive
              (Additive.ofMul q)) := hcomm.symm
        _ = D.finiteReciprocityHom A v hAxiom K M.field M.below 0 :=
          congrArg _ hresZero
        _ = 0 := map_zero _
    exact (finiteNormClass_eq_zero_iff A K.field M.field M.below a).1 hzM

end FiniteGaloisSubextension

namespace FiniteAbelianSubextension

variable {D : DegreeData G} {A : Rep ℤ G}

/-- Finite reciprocity specialized to an actual finite abelian
extension: the two halves are supplied by the general Sylow
surjectivity argument and the cyclic-coordinate injectivity argument,
so no bijectivity premise is exposed by the finite abelian
classification theorem (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:746`). -/
private theorem reciprocityEquiv_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (L : FiniteAbelianSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
    Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  letI : (L.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal := L.normal
  letI : Finite
      (K.field.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
  letI : IsMulCommutative L.toFiniteGaloisExtension.extensionQuotient :=
    L.commutative
  exact ⟨
    v.abstractReciprocity_abelian_finiteReciprocityHom_injective
      hcf hAxiom K L.toFiniteGaloisExtension,
    v.abstractReciprocity_finiteReciprocityHom_surjective
      hcf hAxiom K L.toFiniteGaloisExtension⟩

/-- **The first displayed formula of the finite abelian classification
theorem**: the norm subgroup of the compositum is the intersection of
the two norm subgroups — the first paragraph of the finite
classification proof, with finite reciprocity supplying all three
vertical isomorphisms (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:773`). -/
theorem normSubgroup_compositum
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (L₁ L₂ : FiniteAbelianSubextension K.field) :
    (L₁.compositum L₂).normSubgroup A =
      L₁.normSubgroup A ⊓ L₂.normSubgroup A :=
  normSubgroup_compositum_eq_inf_of_reciprocity_bijective
    D A v hAxiom K L₁ L₂
      (reciprocityEquiv_bijective
        v hcf hAxiom K L₁)
      (reciprocityEquiv_bijective
        v hcf hAxiom K L₂)
      (reciprocityEquiv_bijective
        v hcf hAxiom K (L₁.compositum L₂))

/-- **The order reversal of the finite abelian classification
theorem**: field inclusion is exactly reverse inclusion of norm
subgroups (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:793`). -/
theorem le_iff_normSubgroup_le
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (L₁ L₂ : FiniteAbelianSubextension K.field) :
    L₁ ≤ L₂ ↔ L₂.normSubgroup A ≤ L₁.normSubgroup A :=
  le_iff_normSubgroup_le_of_compositum_and_reciprocity
    D A v hAxiom K L₁ L₂
      (normSubgroup_compositum v hcf hAxiom K L₁ L₂)
      (reciprocityEquiv_bijective
        v hcf hAxiom K (L₁.compositum L₂))
      (reciprocityEquiv_bijective
        v hcf hAxiom K L₂)

/-- The forward map of the finite abelian classification theorem is
injective (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:810`). -/
theorem normSubgroupMap_injective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) :
    Function.Injective (normSubgroupMap A :
      FiniteAbelianSubextension K.field → NormOpenAddSubgroup A K.field) := by
  intro L₁ L₂ h
  have hnorm : L₁.normSubgroup A = L₂.normSubgroup A := by
    exact congrArg Subtype.val h
  apply le_antisymm
  · apply (le_iff_normSubgroup_le v hcf hAxiom K L₁ L₂).2
    rw [hnorm]
  · apply (le_iff_normSubgroup_le v hcf hAxiom K L₂ L₁).2
    rw [hnorm]

/-- **The kernel equality of the surjectivity step**: starting from
`N_E ≤ H`, pull `H / N_E` back through the actual norm-residue symbol
of finite reciprocity and take its fixed field; the norm subgroup of
that concrete finite abelian candidate is exactly `H` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:830`). -/
theorem classFieldCandidate_normSubgroup_eq
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (E : FiniteGaloisSubextension K.field)
    (H : AddSubgroup (ambientFixedAddSubgroup A K.field))
    (hEH : FiniteGaloisSubextension.normSubgroup A E ≤ H) :
    let rE := D.normResidueSymbol A v hcf hAxiom K E
    (FiniteGaloisSubextension.classFieldCandidate A E H rE).normSubgroup A = H := by
  dsimp only
  letI : (E.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal := E.normal
  letI : Finite
      (K.field.toSubgroup ⧸ E.field.toSubgroup.subgroupOf K.field.toSubgroup) := E.finite
  let rE := D.normResidueSymbol A v hcf hAxiom K E
  let M := FiniteGaloisSubextension.classFieldCandidate A E H rE
  have hcompatE (q : E.extensionQuotient) :
      rE.symm (Additive.ofMul (Abelianization.of q)) =
        D.finiteReciprocityHom A v hAxiom K E.field E.below
          (Additive.ofMul q) := by
    simpa only [rE, DegreeData.normResidueSymbol, AddEquiv.symm_symm] using
      D.abstractReciprocityEquiv_apply_of A v hcf hAxiom K E q
  exact
    FiniteGaloisSubextension.classFieldCandidate_normSubgroup_eq_of_reciprocity
      D A v hAxiom K E H hEH rE hcompatE
        (reciprocityEquiv_bijective
          v hcf hAxiom K M)

/-- **Every open subgroup in the norm topology is the norm subgroup of
an actual finite abelian extension** — the fixed field of the literal
preimage of `H / N_E` under the norm-residue symbol of finite
reciprocity (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:863`). -/
theorem normSubgroupMap_surjective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) :
    Function.Surjective (normSubgroupMap A :
      FiniteAbelianSubextension K.field → NormOpenAddSubgroup A K.field) := by
  intro H
  obtain ⟨E, hEH⟩ := normOpenAddSubgroup_contains_finiteNormSubgroup
    A K.field H.1 H.2
  letI : (E.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal := E.normal
  letI : Finite
      (K.field.toSubgroup ⧸ E.field.toSubgroup.subgroupOf K.field.toSubgroup) := E.finite
  let rE := D.normResidueSymbol A v hcf hAxiom K E
  let M := FiniteGaloisSubextension.classFieldCandidate A E H.1 rE
  have hM : M.normSubgroup A = H.1 := by
    simpa only [rE, M] using
      classFieldCandidate_normSubgroup_eq
        v hcf hAxiom K E H.1 hEH
  refine ⟨M, ?_⟩
  apply Subtype.ext
  exact hM

/-- The norm subgroup map of the finite abelian classification theorem
is bijective (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:887`). -/
theorem normSubgroupMap_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) :
    Function.Bijective (normSubgroupMap A :
      FiniteAbelianSubextension K.field → NormOpenAddSubgroup A K.field) :=
  ⟨normSubgroupMap_injective v hcf hAxiom K,
    normSubgroupMap_surjective v hcf hAxiom K⟩

/-- **The finite abelian classification theorem**: finite abelian
extensions of the base are order-isomorphic to the opposite poset of
norm-open subgroups (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:899`). -/
def normSubgroupOrderIso
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) :
    FiniteAbelianSubextension K.field ≃o (NormOpenAddSubgroup A K.field)ᵒᵈ where
  toEquiv := Equiv.ofBijective (normSubgroupMap A)
    (normSubgroupMap_bijective v hcf hAxiom K)
  map_rel_iff' := by
    intro L₁ L₂
    change L₂.normSubgroup A ≤ L₁.normSubgroup A ↔ L₁ ≤ L₂
    exact (le_iff_normSubgroup_le v hcf hAxiom K L₁ L₂).symm

/-- The defining evaluation formula for `normSubgroupOrderIso`: the
underlying subgroup of the image of `L` is `L.normSubgroup A`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:917`). -/
@[simp]
theorem normSubgroupOrderIso_apply
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (L : FiniteAbelianSubextension K.field) :
    (OrderDual.ofDual (normSubgroupOrderIso v hcf hAxiom K L)).1 =
      L.normSubgroup A :=
  rfl

/-- **The second displayed formula of the finite abelian classification
theorem**: the norm subgroup of the intersection field is the product
of the two norm subgroups (their supremum in additive notation)
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:930`). -/
theorem normSubgroup_intersection
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G)
    (L₁ L₂ : FiniteAbelianSubextension K.field) :
    (L₁.intersection L₂).normSubgroup A =
      L₁.normSubgroup A ⊔ L₂.normSubgroup A := by
  apply normSubgroup_intersection_eq_sup_of_surjective_and_order
    A K.field L₁ L₂
  · intro H hH
    let Hopen : NormOpenAddSubgroup A K.field := ⟨H, hH⟩
    obtain ⟨L, hL⟩ :=
      normSubgroupMap_surjective v hcf hAxiom K Hopen
    refine ⟨L, ?_⟩
    exact congrArg Subtype.val hL
  · exact le_iff_normSubgroup_le v hcf hAxiom K

end FiniteAbelianSubextension

end

end Atlas.Knowledge
