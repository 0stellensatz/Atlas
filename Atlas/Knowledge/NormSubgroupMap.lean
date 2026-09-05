import Mathlib
import Atlas.Knowledge.ClassFieldCandidate
import Atlas.Knowledge.FiniteAbelianSubextension
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.IntermediateGaloisCorrespondence
import Atlas.Knowledge.NormTopology
import Atlas.Knowledge.ReciprocityExactRows

/-!
# norm subgroup map

The map `L ↦ N_{L/K} A_L` from the finite abelian subextensions of a
class formation to the norm-open subgroups of `A_K` — the forward map
of the finite abelian classification theorem, with openness carried by
the codomain — together with the group-theoretic inputs of that
theorem's proof (#104): restriction along an inclusion of finite
abelian subextensions on the actual finite Galois quotients, the two
restrictions from a compositum's quotient and their joint injectivity,
the recovery of a field from the order of its finite quotient, the
final surjectivity step, which turns the unconditional inclusion for an
intersection field into equality once surjectivity and order reversal
are known, and, for the class field candidate `M` cut out inside a
finite Galois `E / K`, the containment
`E.field.toSubgroup ≤ M.field.toSubgroup` — the candidate lies below
`E` — and the fact that restriction from `E / K` to the candidate is
trivial exactly on the pulled-back subgroup. Finite reciprocity enters
none of these; the classification item supplies it.

## Main definitions

* `FiniteAbelianSubextension.NormOpenAddSubgroup` — the norm-open
  subgroups of `A_K`, ordered by inclusion.
* `FiniteAbelianSubextension.normSubgroupMap` — the map
  `L ↦ N_{L/K} A_L`.
* `FiniteAbelianSubextension.restriction`,
  `FiniteAbelianSubextension.compositumRestrictionLeft`,
  `FiniteAbelianSubextension.compositumRestrictionRight` — restriction
  on the finite Galois quotients.

## Main statements

* `FiniteAbelianSubextension.compositumRestriction_joint_injective` —
  the two restrictions from a compositum are jointly injective; proved.
* `FiniteAbelianSubextension.eq_of_le_of_extensionQuotient_card_eq` — a
  containment with equal finite quotient orders is an equality; proved.
* `FiniteAbelianSubextension.normSubgroup_intersection_eq_sup_of_surjective_and_order`
  — surjectivity and order reversal make the intersection norm law an
  equality; proved.
* `FiniteGaloisSubextension.classFieldCandidate_restriction_eq_one_iff`
  — restriction to the class field candidate is trivial exactly on the
  pulled-back subgroup; proved.
* `FiniteGaloisSubextension.upperQuotientEquiv_quotientMk_eq_restriction`
  — the third-isomorphism quotient by `S` is restriction to the fixed
  field of `S`; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling —
`mem_extensionSubgroup_iff` becoming Mathlib's
`Subgroup.mem_subgroupOf` and `extensionSubgroup_intermediateField_eq`
the correspondence item's `subgroupOf_intermediateField_eq` — and the
ambient group is `Type u` with the class-formation stock, so the
`{G : Type*}` binders with which the source re-declares its two local
instances, its restriction section (`:230`–`:374`), and
`upperQuotientEquiv_quotientMk_eq_restriction` at `Type*`, to escape
the universe pin on its `Rep ℤ G`, are merged into the section's. The
source's `FiniteAbelianClassification.lean` is split in two along the
line finite reciprocity draws: this item is its reciprocity-free half —
the map, the restrictions, the order recovery, the final surjectivity
step, and the candidate's two restriction facts — and
`Atlas.Knowledge.FiniteAbelianClassification` the other, so
`normSubgroup_intersection_eq_sup_of_surjective_and_order`, `private`
in the source, is public here for that item to consume. The restriction
on the finite Galois quotients is the layer's
`abstractReciprocityRestriction`, the norm subgroup of a finite Galois
subextension `Atlas.Knowledge.NormTopology`'s, the candidate
`Atlas.Knowledge.ClassFieldCandidate`'s, and the intermediate
correspondence `Atlas.Knowledge.IntermediateGaloisCorrespondence`'s. Of
the five local instances, the two normality ones are already the
layer's global `subgroupOf_normalInstance` and stay for fidelity; the
three finiteness ones are load-bearing. Everything else ports
token-for-token; the file is the source's
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean`
`:28`–`:74`, `:230`–`:374`, `:479`–`:544`, and `:707` in their
declarations, the one section comment in that range not carried, as the
layer's items carry none.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The relative subgroup of a finite abelian subextension is normal,
as an instance local to the section ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:28`]
[Yamaguchi2026]). -/
local instance extensionQuotient_normal
    (L : FiniteAbelianSubextension K) :
    (L.field.toSubgroup.subgroupOf K.toSubgroup).Normal :=
  L.normal

/-- The relative quotient of a finite abelian subextension is finite,
as an instance local to the section ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:34`]
[Yamaguchi2026]). -/
local instance representedQuotient_finite
    (L : FiniteAbelianSubextension K) :
    Finite (K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup) :=
  L.finite

/-- **The norm-open subgroups**: additive subgroups which are open for
the explicitly declared norm topology. The topology is part of the
predicate, so no ambient topology instance is changed outside the
finite abelian classification theorem ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:43`]
[Yamaguchi2026]). -/
def NormOpenAddSubgroup (A : Rep ℤ G) (K : ClosedSubgroup G) :=
  {H : AddSubgroup (ambientFixedAddSubgroup A K) //
    IsNormOpen A K (H : Set (ambientFixedAddSubgroup A K))}

/-- Norm-open subgroups inherit the literal inclusion order of their
underlying additive subgroups; the instance is stated explicitly
because `NormOpenAddSubgroup` is an opaque boundary type, not a
transparent alias ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:50`]
[Yamaguchi2026]). -/
instance normOpenAddSubgroupPartialOrder (A : Rep ℤ G)
    (K : ClosedSubgroup G) : PartialOrder (NormOpenAddSubgroup A K) :=
  PartialOrder.lift (fun H => H.1) (fun _ _ h => Subtype.ext h)

/-- **The norm subgroup map** `L ↦ N_{L/K} A_L` of the finite abelian
classification theorem, with openness carried by the codomain rather
than assumed ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:56`]
[Yamaguchi2026]). -/
def normSubgroupMap (A : Rep ℤ G)
    (L : FiniteAbelianSubextension K) : NormOpenAddSubgroup A K := by
  refine ⟨L.normSubgroup A, ?_⟩
  simpa [FiniteAbelianSubextension.normSubgroup,
    FiniteGaloisSubextension.normSubgroup] using
    normSubgroup_isOpen A K
      L.toFiniteGaloisExtension

/-- The underlying subgroup of `L.normSubgroupMap A` is
`L.normSubgroup A` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:66`]
[Yamaguchi2026]). -/
@[simp]
theorem normSubgroupMap_val
    (A : Rep ℤ G) (L : FiniteAbelianSubextension K) :
    (L.normSubgroupMap A).1 = L.normSubgroup A :=
  rfl

/-- The subgroup product `N_{L₁} N_{L₂}` (a supremum in additive
notation) is open in the norm topology: it contains the defining norm
neighbourhood attached to `L₁` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:74`]
[Yamaguchi2026]). -/
theorem sup_normSubgroup_isOpen (A : Rep ℤ G)
    (L₁ L₂ : FiniteAbelianSubextension K) :
    IsNormOpen A K
      ((L₁.normSubgroup A ⊔ L₂.normSubgroup A :
        AddSubgroup (ambientFixedAddSubgroup A K)) :
        Set (ambientFixedAddSubgroup A K)) := by
  apply (normTopology_addSubgroup_isOpen_iff A K
    (L₁.normSubgroup A ⊔ L₂.normSubgroup A)).2
  refine ⟨L₁.toFiniteGaloisExtension, ?_⟩
  change L₁.normSubgroup A ≤ L₁.normSubgroup A ⊔ L₂.normSubgroup A
  exact le_sup_left

/-- Restriction along an inclusion of finite abelian subextensions. The
proof-dependent raw quotient map is transported through the two named
quotient boundaries here and nowhere in its callers ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:230`]
[Yamaguchi2026]). -/
def restriction
    {L₁ L₂ : FiniteAbelianSubextension K} (h₁₂ : L₁ ≤ L₂) :
    L₂.extensionQuotient →* L₁.extensionQuotient := by
  letI : (L₁.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L₁.normal
  letI : (L₂.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L₂.normal
  exact L₁.extensionQuotientMulEquiv.symm.toMonoidHom.comp
    ((abstractReciprocityRestriction K L₁.field L₂.field h₁₂ L₁.below).comp
      L₂.extensionQuotientMulEquiv.toMonoidHom)

/-- Restriction sends the class of `k` in the larger quotient to its
class in the smaller ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:244`]
[Yamaguchi2026]). -/
@[simp]
theorem restriction_mk
    {L₁ L₂ : FiniteAbelianSubextension K} (h₁₂ : L₁ ≤ L₂)
    (k : K.toSubgroup) :
    restriction h₁₂ (L₂.extensionQuotientMk k) =
      L₁.extensionQuotientMk k := by
  apply L₁.extensionQuotientMulEquiv.injective
  simp [restriction]

/-- Restriction from the actual Galois quotient of `L₁L₂ / K` to that
of `L₁ / K` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:255`]
[Yamaguchi2026]). -/
def compositumRestrictionLeft
    (L₁ L₂ : FiniteAbelianSubextension K) :
    (L₁.compositum L₂).extensionQuotient →* L₁.extensionQuotient :=
  restriction (L₁.le_compositum_left L₂)

/-- Restriction from the actual Galois quotient of `L₁L₂ / K` to that
of `L₂ / K` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:263`]
[Yamaguchi2026]). -/
def compositumRestrictionRight
    (L₁ L₂ : FiniteAbelianSubextension K) :
    (L₁.compositum L₂).extensionQuotient →* L₂.extensionQuotient :=
  restriction (L₁.le_compositum_right L₂)

/-- The left compositum restriction sends the class of `k` in
`G(L₁L₂/K)` to its class in `G(L₁/K)` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:274`]
[Yamaguchi2026]). -/
@[simp]
theorem compositumRestrictionLeft_mk
    (L₁ L₂ : FiniteAbelianSubextension K) (k : K.toSubgroup) :
    compositumRestrictionLeft L₁ L₂
        ((L₁.compositum L₂).extensionQuotientMk k) =
      L₁.extensionQuotientMk k := by
  exact restriction_mk (L₁.le_compositum_left L₂) k

/-- The right compositum restriction sends the class of `k` in
`G(L₁L₂/K)` to its class in `G(L₂/K)` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:287`]
[Yamaguchi2026]). -/
@[simp]
theorem compositumRestrictionRight_mk
    (L₁ L₂ : FiniteAbelianSubextension K) (k : K.toSubgroup) :
    compositumRestrictionRight L₁ L₂
        ((L₁.compositum L₂).extensionQuotientMk k) =
      L₂.extensionQuotientMk k := by
  exact restriction_mk (L₁.le_compositum_right L₂) k

/-- **The two restriction maps from the Galois group of a compositum
are jointly injective**, proved on the literal quotient
representatives: an element trivial modulo both field subgroups lies in
their intersection, which is the subgroup representing the compositum
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:299`]
[Yamaguchi2026]). -/
theorem compositumRestriction_joint_injective
    (L₁ L₂ : FiniteAbelianSubextension K) :
    Function.Injective (fun q : (L₁.compositum L₂).extensionQuotient ↦
      (compositumRestrictionLeft L₁ L₂ q,
        compositumRestrictionRight L₁ L₂ q)) := by
  intro x y
  revert y
  refine (L₁.compositum L₂).extensionQuotient_inductionOn
    (motive := fun x ↦ ∀ y,
      (compositumRestrictionLeft L₁ L₂ x,
        compositumRestrictionRight L₁ L₂ x) =
          (compositumRestrictionLeft L₁ L₂ y,
            compositumRestrictionRight L₁ L₂ y) → x = y) x ?_
  intro a y
  refine (L₁.compositum L₂).extensionQuotient_inductionOn
    (motive := fun y ↦
      (compositumRestrictionLeft L₁ L₂
          ((L₁.compositum L₂).extensionQuotientMk a),
        compositumRestrictionRight L₁ L₂
          ((L₁.compositum L₂).extensionQuotientMk a)) =
        (compositumRestrictionLeft L₁ L₂ y,
          compositumRestrictionRight L₁ L₂ y) →
        (L₁.compositum L₂).extensionQuotientMk a = y) y ?_
  intro b hab
  have hleft :
      L₁.extensionQuotientMk a = L₁.extensionQuotientMk b :=
    congrArg Prod.fst hab
  have hright :
      L₂.extensionQuotientMk a = L₂.extensionQuotientMk b :=
    congrArg Prod.snd hab
  have hleftRaw := congrArg L₁.extensionQuotientMulEquiv hleft
  have hrightRaw := congrArg L₂.extensionQuotientMulEquiv hright
  simp only [L₁.extensionQuotientMk_apply] at hleftRaw
  simp only [L₂.extensionQuotientMk_apply] at hrightRaw
  apply (L₁.compositum L₂).extensionQuotientMulEquiv.injective
  simp only [FiniteAbelianSubextension.extensionQuotientMk_apply]
  apply QuotientGroup.eq.mpr
  apply Subgroup.mem_subgroupOf.2
  exact ⟨
    Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.mp hleftRaw),
    Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.mp hrightRaw)⟩

/-- Equivalently, the kernels of the two restrictions have trivial
intersection — the literal group statement used in the first paragraph
of the classification theorem's proof ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:348`]
[Yamaguchi2026]). -/
theorem ker_compositumRestrictionLeft_inf_ker_compositumRestrictionRight
    (L₁ L₂ : FiniteAbelianSubextension K) :
    (compositumRestrictionLeft L₁ L₂).ker ⊓
        (compositumRestrictionRight L₁ L₂).ker = ⊥ := by
  ext q
  constructor
  · intro hq
    rw [Subgroup.mem_inf] at hq
    rw [Subgroup.mem_bot]
    apply compositumRestriction_joint_injective L₁ L₂
    apply Prod.ext
    · simpa using hq.1
    · simpa using hq.2
  · intro hq
    rw [Subgroup.mem_bot] at hq
    subst q
    simp

/-- **A containment of finite abelian extensions whose actual Galois
quotients have the same finite cardinality is an equality** — the
group-theoretic final step of the injectivity argument of the finite
classification, where equality of cardinalities comes from finite
reciprocity ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:374`]
[Yamaguchi2026]). -/
theorem eq_of_le_of_extensionQuotient_card_eq
    {L₁ L₂ : FiniteAbelianSubextension K} (h₁₂ : L₁ ≤ L₂)
    (hcard : Nat.card L₂.extensionQuotient =
      Nat.card L₁.extensionQuotient) :
    L₁ = L₂ := by
  let r := restriction h₁₂
  have hrSurjective : Function.Surjective r := by
    simpa [r, restriction] using
      L₁.extensionQuotientMulEquiv.symm.surjective.comp
        ((abstractReciprocityRestriction_surjective K L₁.field L₂.field
          h₁₂ L₁.below).comp
            L₂.extensionQuotientMulEquiv.surjective)
  have hrBijective : Function.Bijective r :=
    (Nat.bijective_iff_surjective_and_card r).2
      ⟨hrSurjective, hcard⟩
  apply le_antisymm h₁₂
  intro g hg
  let k : K.toSubgroup := ⟨g, L₁.below hg⟩
  have hrOne : r (L₂.extensionQuotientMk k) = 1 := by
    rw [show r (L₂.extensionQuotientMk k) =
      L₁.extensionQuotientMk k by exact restriction_mk h₁₂ k]
    apply L₁.extensionQuotientMulEquiv.injective
    rw [map_one, L₁.extensionQuotientMk_apply]
    apply (QuotientGroup.eq_one_iff k).2
    exact Subgroup.mem_subgroupOf.2 hg
  have hkOne : L₂.extensionQuotientMk k = 1 := by
    apply hrBijective.1
    simpa [r] using hrOne
  have hkOneRaw := congrArg L₂.extensionQuotientMulEquiv hkOne
  simp only [L₂.extensionQuotientMk_apply, map_one] at hkOneRaw
  exact Subgroup.mem_subgroupOf.1
    ((QuotientGroup.eq_one_iff k).1 hkOneRaw)

/-- **The final surjectivity step**: surjectivity and order reversal
turn the unconditional inclusion for an intersection field into
equality ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:479`]
[Yamaguchi2026]). -/
theorem normSubgroup_intersection_eq_sup_of_surjective_and_order
    [IsTopologicalGroup G] [CompactSpace G]
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    (L₁ L₂ : FiniteAbelianSubextension K)
    (hsurjective : ∀ H : AddSubgroup (ambientFixedAddSubgroup A K),
      IsNormOpen A K (H : Set (ambientFixedAddSubgroup A K)) →
        ∃ L : FiniteAbelianSubextension K, L.normSubgroup A = H)
    (horder : ∀ X Y : FiniteAbelianSubextension K,
      X ≤ Y ↔ Y.normSubgroup A ≤ X.normSubgroup A) :
    (L₁.intersection L₂).normSubgroup A =
      L₁.normSubgroup A ⊔ L₂.normSubgroup A := by
  apply le_antisymm
  · let H := L₁.normSubgroup A ⊔ L₂.normSubgroup A
    obtain ⟨L, hL⟩ := hsurjective H (sup_normSubgroup_isOpen A L₁ L₂)
    have hLL₁ : L ≤ L₁ := by
      apply (horder L L₁).2
      rw [hL]
      exact le_sup_left
    have hLL₂ : L ≤ L₂ := by
      apply (horder L L₂).2
      rw [hL]
      exact le_sup_right
    have hLintersection : L ≤ L₁.intersection L₂ :=
      le_intersection hLL₁ hLL₂
    have hnorm := normSubgroup_antitone A hLintersection
    rw [hL] at hnorm
    exact hnorm
  · exact sup_normSubgroup_le_intersection A L₁ L₂

end FiniteAbelianSubextension

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G} [IsTopologicalGroup G]

/-- The relative quotient of a finite Galois subextension is finite, as
an instance local to the section ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:514`]
[Yamaguchi2026]). -/
local instance classification_extensionQuotient_finite
    (E : FiniteGaloisSubextension K) :
    Finite (K.toSubgroup ⧸ E.field.toSubgroup.subgroupOf K.toSubgroup) :=
  E.finite

/-- The relative subgroup of a finite abelian subextension is normal,
as an instance local to the section ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:519`]
[Yamaguchi2026]). -/
local instance classification_abelianExtension_normal
    (M : FiniteAbelianSubextension K) :
    (M.field.toSubgroup.subgroupOf K.toSubgroup).Normal :=
  M.normal

/-- The relative quotient of a finite abelian subextension is finite,
as an instance local to the section ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:524`]
[Yamaguchi2026]). -/
local instance classification_abelianExtension_finite
    (M : FiniteAbelianSubextension K) :
    Finite (K.toSubgroup ⧸ M.field.toSubgroup.subgroupOf K.toSubgroup) :=
  M.finite

/-- The original finite Galois subextension's subgroup lies below the
class field candidate's — the candidate, cut out inside `E`, is the
smaller field ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:531`]
[Yamaguchi2026]). -/
theorem classFieldCandidate_field_le
    (E : FiniteGaloisSubextension K) (A : Rep ℤ G)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    E.field.toSubgroup ≤
      (classFieldCandidate A E H rE).field.toSubgroup := by
  rw [classFieldCandidate_field A E H rE]
  exact E.field_le_intermediateField
    (reciprocityPreimageSubgroup A E H rE)

/-- **Restriction from `E / K` to its class field candidate is trivial
exactly on the pulled-back subgroup** used to define that candidate
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:544`]
[Yamaguchi2026]). -/
theorem classFieldCandidate_restriction_eq_one_iff
    (E : FiniteGaloisSubextension K) (A : Rep ℤ G)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (q : E.extensionQuotient) :
    abstractReciprocityRestriction K
        (classFieldCandidate A E H rE).field E.field
        (classFieldCandidate_field_le E A H rE)
        (classFieldCandidate A E H rE).below q = 1 ↔
      q ∈ reciprocityPreimageSubgroup A E H rE := by
  let S := reciprocityPreimageSubgroup A E H rE
  let M := classFieldCandidate A E H rE
  let hEM := classFieldCandidate_field_le E A H rE
  let k : K.toSubgroup := Quotient.out q
  rw [← Quotient.out_eq' q]
  constructor
  · intro hk
    have hkM : k ∈ M.field.toSubgroup.subgroupOf K.toSubgroup :=
      (QuotientGroup.eq_one_iff k).1 hk
    have hkMfield : k.1 ∈ M.field.toSubgroup :=
      Subgroup.mem_subgroupOf.1 hkM
    have hkIntermediate : k.1 ∈ (E.intermediateField S).toSubgroup := by
      rw [← classFieldCandidate_field A E H rE]
      exact hkMfield
    have hkIntermediateSubgroup :
        k ∈ (E.intermediateField S).toSubgroup.subgroupOf K.toSubgroup :=
      Subgroup.mem_subgroupOf.2 hkIntermediate
    rw [E.subgroupOf_intermediateField_eq S] at hkIntermediateSubgroup
    exact hkIntermediateSubgroup
  · intro hkS
    have hkIntermediateSubgroup : k ∈ E.intermediateSubgroup S := hkS
    rw [← E.subgroupOf_intermediateField_eq S] at hkIntermediateSubgroup
    have hkIntermediate : k.1 ∈ (E.intermediateField S).toSubgroup :=
      Subgroup.mem_subgroupOf.1 hkIntermediateSubgroup
    have hkMfield : k.1 ∈ M.field.toSubgroup := by
      rw [classFieldCandidate_field A E H rE]
      exact hkIntermediate
    apply (QuotientGroup.eq_one_iff k).2
    exact Subgroup.mem_subgroupOf.2 hkMfield

/-- The third-isomorphism quotient by `S` is literally restriction from
`E / K` to the intermediate field fixed by `S` — the
representative-level identity connecting the candidate quotient in the
surjectivity construction of the finite abelian classification theorem
to the restriction map of restriction compatibility ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianClassification.lean:707`]
[Yamaguchi2026]). -/
theorem upperQuotientEquiv_quotientMk_eq_restriction
    (E : FiniteGaloisSubextension K) (S : Subgroup E.extensionQuotient)
    [hS : S.Normal] (q : E.extensionQuotient) :
    letI : (E.field.toSubgroup.subgroupOf K.toSubgroup).Normal := E.normal
    letI : ((E.intermediateField S).toSubgroup.subgroupOf K.toSubgroup).Normal :=
      E.intermediateField_normal S hS
    E.upperQuotientEquiv S (QuotientGroup.mk q) =
      abstractReciprocityRestriction K (E.intermediateField S) E.field
        (E.field_le_intermediateField S)
        (E.intermediateField_le_base S) q := by
  letI : (E.field.toSubgroup.subgroupOf K.toSubgroup).Normal := E.normal
  letI : ((E.intermediateField S).toSubgroup.subgroupOf K.toSubgroup).Normal :=
    E.intermediateField_normal S hS
  refine QuotientGroup.induction_on q ?_
  intro k
  exact E.upperQuotientEquiv_mk_mk S k

end FiniteGaloisSubextension

end

end Atlas.Knowledge
