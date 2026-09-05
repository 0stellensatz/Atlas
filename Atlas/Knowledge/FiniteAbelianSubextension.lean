import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FiniteExtensionTransitivity
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteTower
import Atlas.Knowledge.NormTopology
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.RelativeNormLaws

/-!
# finite abelian subextension

A finite abelian extension `L / K` of a class formation, packaged as a
finite Galois subextension whose relative quotient `G_K / G_L` is
commutative — the index type of the finite abelian classification
theorem (#104): the partial order by field inclusion, base change to an
intermediate field, the compositum `L₁L₂` and, over a compact ambient
group, the intersection `L₁ ∩ L₂`, with the norm subgroup `N_{L/K} A_L`
of each and its antitonicity, which gives the unconditional halves of
the norm laws `N_{L₁L₂} = N_{L₁} ∩ N_{L₂}` and
`N_{L₁ ∩ L₂} = N_{L₁} N_{L₂}`.

## Main definitions

* `FiniteAbelianSubextension` — a finite Galois subextension with
  commutative quotient, with its `PartialOrder`.
* `FiniteAbelianSubextension.baseChange` — base change to an
  intermediate field.
* `FiniteAbelianSubextension.compositum`,
  `FiniteAbelianSubextension.intersection` — the lattice operations on
  fields.
* `FiniteAbelianSubextension.normSubgroup` — the norm subgroup
  `N_{L/K} A_L`.

## Main statements

* `FiniteAbelianSubextension.normSubgroup_eq_galois` — the norm subgroup
  is `Atlas.Knowledge.NormTopology`'s, of the underlying finite Galois
  subextension; `rfl`.
* `FiniteAbelianSubextension.normSubgroup_antitone` — an inclusion of
  fields reverses the inclusion of norm subgroups; proved.
* `FiniteAbelianSubextension.normSubgroup_compositum_le_inf`,
  `sup_normSubgroup_le_intersection` — the unconditional halves of the
  two norm laws; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`mem_extensionSubgroup_iff` becoming Mathlib's
`Subgroup.mem_subgroupOf` — at one base-change step with its element
pinned explicitly, since the goal offers the intermediate field's
subgroup where the hypothesis lives in the base's —
`extensionSubgroup_intersectionField` is renamed
`subgroupOf_intersectionField` with the spelling, the finite tower is
the layer's top-level `FiniteTower`,
`finite_extension_over_intermediate` is the layer's top-level form, and
the ambient group is `Type u` with the class-formation stock. The base
change of the underlying finite Galois subextension is
`FiniteGaloisSubextension.baseChange`, the source's
`FiniteGaloisSubextension.lean:291`, added to
`Atlas.Knowledge.FiniteGaloisSubextension` with this brick since it
needs nothing that item lacks; the norm subgroup is
`Atlas.Knowledge.NormTopology`'s of the underlying finite Galois
subextension, definitionally, which `normSubgroup_eq_galois` records;
the type-valued `extensionQuotient` and its `CommGroup` instance carry
`@[implicit_reducible]` as the source's do. The intersection section's
ambient compactness and topological-group binders are carried by a
`variable` block opened after `field_le_normalizer`, which needs
neither. Everything else ports token-for-token modulo four condensed
proof steps that change no statement — `extensionQuotient_inductionOn`
in term mode for the source's `by exact`, `field_le_normalizer`'s
`have` and `letI` collapsed into one `letI`, `normSubgroup_antitone`'s
finiteness witness without the source's `change`, and the source's
`omit` replaced by that variable placement; the file is the source's
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean`
whole.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **A finite abelian extension `L / K`**: a finite Galois
subextension together with commutativity of its actual quotient
`G_K / G_L` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:36`]
[Yamaguchi2026]). -/
structure FiniteAbelianSubextension (K : ClosedSubgroup G) where
  /-- The underlying finite Galois subextension. -/
  toFiniteGaloisExtension : FiniteGaloisSubextension K
  /-- Commutativity of the relative Galois quotient. -/
  commutative : IsMulCommutative toFiniteGaloisExtension.extensionQuotient

namespace FiniteAbelianSubextension

variable {K : ClosedSubgroup G}

/-- The top field's subgroup ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:47`]
[Yamaguchi2026]). -/
abbrev field (L : FiniteAbelianSubextension K) : ClosedSubgroup G :=
  L.toFiniteGaloisExtension.field

/-- The top field lies over the base ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:51`]
[Yamaguchi2026]). -/
abbrev below (L : FiniteAbelianSubextension K) : L.field.toSubgroup ≤ K.toSubgroup :=
  L.toFiniteGaloisExtension.below

/-- Normality of the relative subgroup ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:56`]
[Yamaguchi2026]). -/
abbrev normal (L : FiniteAbelianSubextension K) :
    (L.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L.toFiniteGaloisExtension.normal

/-- Finiteness of the relative quotient ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:61`]
[Yamaguchi2026]). -/
abbrev finite (L : FiniteAbelianSubextension K) :
    Finite (K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup) :=
  L.toFiniteGaloisExtension.finite

/-- The finite abelian quotient, inherited through the finite Galois
boundary ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:69`]
[Yamaguchi2026]). -/
@[implicit_reducible]
def extensionQuotient (L : FiniteAbelianSubextension K) : Type u :=
  L.toFiniteGaloisExtension.extensionQuotient

/-- The quotient of a finite abelian subextension is a commutative
group ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:74`]
[Yamaguchi2026]). -/
@[implicit_reducible]
instance extensionQuotient_commGroup (L : FiniteAbelianSubextension K) :
    CommGroup L.extensionQuotient := by
  unfold extensionQuotient
  letI : IsMulCommutative L.toFiniteGaloisExtension.extensionQuotient := L.commutative
  exact { (inferInstance : Group L.toFiniteGaloisExtension.extensionQuotient) with
    mul_comm := L.commutative.is_comm.comm }

/-- The quotient of a finite abelian subextension is finite ([Yamaguchi
2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:85`]
[Yamaguchi2026]). -/
instance extensionQuotient_finite (L : FiniteAbelianSubextension K) :
    Finite L.extensionQuotient := by
  unfold extensionQuotient
  infer_instance

/-- Comparison with the quotient presentation of the group library
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:92`]
[Yamaguchi2026]). -/
def extensionQuotientMulEquiv (L : FiniteAbelianSubextension K) :
    L.extensionQuotient ≃* (K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup) :=
  L.toFiniteGaloisExtension.extensionQuotientMulEquiv

/-- The canonical quotient projection ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:98`]
[Yamaguchi2026]). -/
def extensionQuotientMk (L : FiniteAbelianSubextension K) :
    K.toSubgroup →* L.extensionQuotient :=
  L.toFiniteGaloisExtension.extensionQuotientMk

/-- The named projection agrees with the underlying quotient map
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:104`]
[Yamaguchi2026]). -/
@[simp]
theorem extensionQuotientMk_apply (L : FiniteAbelianSubextension K) (k : K.toSubgroup) :
    L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k : K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup) :=
  L.toFiniteGaloisExtension.extensionQuotientMk_apply k

/-- Eliminate an abelian extension quotient without choosing a
representative ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:112`]
[Yamaguchi2026]). -/
protected theorem extensionQuotient_inductionOn (L : FiniteAbelianSubextension K)
    {motive : L.extensionQuotient → Prop} (q : L.extensionQuotient)
    (mk : ∀ k : K.toSubgroup, motive (L.extensionQuotientMk k)) : motive q :=
  L.toFiniteGaloisExtension.extensionQuotient_inductionOn q mk

/-- Two packages with the same closed subgroup are the same finite
abelian extension ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:122`]
[Yamaguchi2026]). -/
@[ext]
theorem ext {L₁ L₂ : FiniteAbelianSubextension K} (h : L₁.field = L₂.field) : L₁ = L₂ := by
  cases L₁ with
  | mk L₁ h₁ =>
      cases L₂ with
      | mk L₂ h₂ =>
          cases L₁ with
          | mk F₁ b₁ n₁ f₁ =>
              cases L₂ with
              | mk F₂ b₂ n₂ f₂ =>
                  dsimp only [field] at h
                  cases h
                  rfl

/-- The order is field inclusion — the opposite of the subgroup order,
fields being represented by their absolute Galois subgroups ([Yamaguchi
2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:138`]
[Yamaguchi2026]). -/
instance : PartialOrder (FiniteAbelianSubextension K) where
  le L₁ L₂ := L₂.field.toSubgroup ≤ L₁.field.toSubgroup
  le_refl _ := le_rfl
  le_trans _ _ _ h₁₂ h₂₃ := h₂₃.trans h₁₂
  le_antisymm L₁ L₂ h₁₂ h₂₁ := by
    apply ext
    apply ClosedSubgroup.ext
    have hs : L₁.field.toSubgroup = L₂.field.toSubgroup := le_antisymm h₂₁ h₁₂
    exact congrArg (fun H : Subgroup G => H.carrier) hs

/-- The order is containment of the fields' subgroups, reversed
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:150`]
[Yamaguchi2026]). -/
theorem le_iff (L₁ L₂ : FiniteAbelianSubextension K) :
    L₁ ≤ L₂ ↔ L₂.field.toSubgroup ≤ L₁.field.toSubgroup := Iff.rfl

/-- **Base change of a finite abelian extension** to an intermediate
abstract field: the new top subgroup is the intersection with the new
base subgroup ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:157`]
[Yamaguchi2026]). -/
def baseChange (M : FiniteAbelianSubextension K) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) : FiniteAbelianSubextension L where
  toFiniteGaloisExtension := M.toFiniteGaloisExtension.baseChange L hLK
  commutative := by
    let P := M.toFiniteGaloisExtension.baseChange L hLK
    letI : (M.field.toSubgroup.subgroupOf K.toSubgroup).Normal := M.normal
    letI : (P.field.toSubgroup.subgroupOf L.toSubgroup).Normal := P.normal
    refine ⟨⟨?_⟩⟩
    intro x y
    refine P.extensionQuotient_inductionOn (motive := fun x => x * y = y * x) x ?_
    intro a
    refine P.extensionQuotient_inductionOn
      (motive := fun y => P.extensionQuotientMk a * y = y * P.extensionQuotientMk a) y ?_
    intro b
    apply P.extensionQuotientMulEquiv.injective
    simp only [map_mul, P.extensionQuotientMk_apply]
    apply QuotientGroup.eq.mpr
    apply Subgroup.mem_subgroupOf.2
    constructor
    · exact ((a * b)⁻¹ * (b * a)).property
    · let aK : K.toSubgroup := Subgroup.inclusion hLK a
      let bK : K.toSubgroup := Subgroup.inclusion hLK b
      have hcomm :=
        M.commutative.is_comm.comm (M.extensionQuotientMk aK) (M.extensionQuotientMk bK)
      have hcommRaw := congrArg M.extensionQuotientMulEquiv hcomm
      simp only [map_mul, M.extensionQuotientMk_apply] at hcommRaw
      have h : (((aK * bK)⁻¹ * (bK * aK) : K.toSubgroup) : G) ∈ M.field.toSubgroup :=
        (Subgroup.mem_subgroupOf (h := (aK * bK)⁻¹ * (bK * aK))).1 (QuotientGroup.eq.mp hcommRaw)
      exact h

/-- **The compositum `L₁L₂`**, contravariantly `G_{L₁} ∩ G_{L₂}`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:206`]
[Yamaguchi2026]). -/
def compositum (L₁ L₂ : FiniteAbelianSubextension K) : FiniteAbelianSubextension K where
  toFiniteGaloisExtension := L₁.toFiniteGaloisExtension.compositum L₂.toFiniteGaloisExtension
  commutative := by
    let P := L₁.toFiniteGaloisExtension.compositum L₂.toFiniteGaloisExtension
    letI : (L₁.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L₁.normal
    letI : (L₂.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L₂.normal
    letI : (P.field.toSubgroup.subgroupOf K.toSubgroup).Normal := P.normal
    refine ⟨⟨?_⟩⟩
    intro x y
    refine P.extensionQuotient_inductionOn (motive := fun x => x * y = y * x) x ?_
    intro a
    refine P.extensionQuotient_inductionOn
      (motive := fun y => P.extensionQuotientMk a * y = y * P.extensionQuotientMk a) y ?_
    intro b
    apply P.extensionQuotientMulEquiv.injective
    simp only [map_mul, P.extensionQuotientMk_apply]
    apply QuotientGroup.eq.mpr
    apply Subgroup.mem_subgroupOf.2
    constructor
    · have hcomm :=
        L₁.commutative.is_comm.comm (L₁.extensionQuotientMk a) (L₁.extensionQuotientMk b)
      have hcommRaw := congrArg L₁.extensionQuotientMulEquiv hcomm
      simp only [map_mul, L₁.extensionQuotientMk_apply] at hcommRaw
      exact Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.mp hcommRaw)
    · have hcomm :=
        L₂.commutative.is_comm.comm (L₂.extensionQuotientMk a) (L₂.extensionQuotientMk b)
      have hcommRaw := congrArg L₂.extensionQuotientMulEquiv hcomm
      simp only [map_mul, L₂.extensionQuotientMk_apply] at hcommRaw
      exact Subgroup.mem_subgroupOf.1 (QuotientGroup.eq.mp hcommRaw)

/-- The left subextension embeds into the compositum ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:244`]
[Yamaguchi2026]). -/
theorem le_compositum_left (L₁ L₂ : FiniteAbelianSubextension K) :
    L₁ ≤ L₁.compositum L₂ := by
  change (L₁.field.toSubgroup ⊓ L₂.field.toSubgroup) ≤ L₁.field.toSubgroup
  exact inf_le_left

/-- The right subextension embeds into the compositum ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:252`]
[Yamaguchi2026]). -/
theorem le_compositum_right (L₁ L₂ : FiniteAbelianSubextension K) :
    L₂ ≤ L₁.compositum L₂ := by
  change (L₁.field.toSubgroup ⊓ L₂.field.toSubgroup) ≤ L₂.field.toSubgroup
  exact inf_le_right

/-- The compositum is the least subextension containing both inputs
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:260`]
[Yamaguchi2026]). -/
theorem compositum_le {L₁ L₂ P : FiniteAbelianSubextension K} (h₁ : L₁ ≤ P) (h₂ : L₂ ≤ P) :
    L₁.compositum L₂ ≤ P :=
  fun _ hp => ⟨h₁ hp, h₂ hp⟩

section Intersection

/-- Each field subgroup normalizes the other, from the packaged
normality of `G_L` inside `G_K` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:273`]
[Yamaguchi2026]). -/
theorem field_le_normalizer (L₁ L₂ : FiniteAbelianSubextension K) :
    L₁.field.toSubgroup ≤ Subgroup.normalizer L₂.field.toSubgroup := by
  letI : (L₂.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L₂.normal
  exact L₁.below.trans (Subgroup.le_normalizer_of_normal_subgroupOf L₂.below)

variable [IsTopologicalGroup G] [CompactSpace G]

/-- **The field intersection `L₁ ∩ L₂`**, contravariantly the subgroup
generated by `G_{L₁}` and `G_{L₂}`, closed by the product description
and compactness ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:285`]
[Yamaguchi2026]). -/
def intersectionField (L₁ L₂ : FiniteAbelianSubextension K) : ClosedSubgroup G where
  toSubgroup := L₁.field.toSubgroup ⊔ L₂.field.toSubgroup
  isClosed' := by
    change IsClosed ((↑(L₁.field.toSubgroup ⊔ L₂.field.toSubgroup) : Set G))
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (field_le_normalizer L₁ L₂)]
    exact L₂.field.isClosed'.mul_left_of_isCompact L₁.field.isClosed'.isCompact

/-- The intersection field lies over the base ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:297`]
[Yamaguchi2026]). -/
theorem intersectionField_below (L₁ L₂ : FiniteAbelianSubextension K) :
    (intersectionField L₁ L₂).toSubgroup ≤ K.toSubgroup :=
  sup_le L₁.below L₂.below

/-- Inside `G_K` the generated subgroup is the supremum of the two
relative subgroups ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:303`]
[Yamaguchi2026]). -/
theorem subgroupOf_intersectionField (L₁ L₂ : FiniteAbelianSubextension K) :
    (intersectionField L₁ L₂).toSubgroup.subgroupOf K.toSubgroup =
      L₁.field.toSubgroup.subgroupOf K.toSubgroup ⊔
        L₂.field.toSubgroup.subgroupOf K.toSubgroup := by
  simpa [intersectionField] using (Subgroup.subgroupOf_sup L₁.below L₂.below)

/-- The finite Galois package underlying the intersection field
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:313`]
[Yamaguchi2026]). -/
def intersectionGalois (L₁ L₂ : FiniteAbelianSubextension K) : FiniteGaloisSubextension K where
  field := intersectionField L₁ L₂
  below := intersectionField_below L₁ L₂
  normal := by
    rw [subgroupOf_intersectionField]
    letI : (L₁.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L₁.normal
    letI : (L₂.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L₂.normal
    exact Subgroup.sup_normal _ _
  finite := by
    rw [subgroupOf_intersectionField]
    letI : (L₁.field.toSubgroup.subgroupOf K.toSubgroup).FiniteIndex :=
      @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
        (L₁.field.toSubgroup.subgroupOf K.toSubgroup) L₁.finite
    letI : (L₁.field.toSubgroup.subgroupOf K.toSubgroup ⊔
        L₂.field.toSubgroup.subgroupOf K.toSubgroup).FiniteIndex :=
      Subgroup.finiteIndex_of_le le_sup_left
    exact Subgroup.finite_quotient_of_finiteIndex

/-- **The intersection of two finite abelian extensions** ([Yamaguchi
2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:333`]
[Yamaguchi2026]). -/
def intersection (L₁ L₂ : FiniteAbelianSubextension K) : FiniteAbelianSubextension K where
  toFiniteGaloisExtension := intersectionGalois L₁ L₂
  commutative := by
    let P := intersectionGalois L₁ L₂
    letI : (L₁.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L₁.normal
    letI : (L₂.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L₂.normal
    letI : (P.field.toSubgroup.subgroupOf K.toSubgroup).Normal := P.normal
    refine ⟨⟨?_⟩⟩
    intro x y
    refine P.extensionQuotient_inductionOn (motive := fun x => x * y = y * x) x ?_
    intro a
    refine P.extensionQuotient_inductionOn
      (motive := fun y => P.extensionQuotientMk a * y = y * P.extensionQuotientMk a) y ?_
    intro b
    apply P.extensionQuotientMulEquiv.injective
    simp only [map_mul, P.extensionQuotientMk_apply]
    apply QuotientGroup.eq.mpr
    change (a * b)⁻¹ * (b * a) ∈ (intersectionField L₁ L₂).toSubgroup.subgroupOf K.toSubgroup
    rw [subgroupOf_intersectionField]
    have hcomm :=
      L₁.commutative.is_comm.comm (L₁.extensionQuotientMk a) (L₁.extensionQuotientMk b)
    have hcommRaw := congrArg L₁.extensionQuotientMulEquiv hcomm
    simp only [map_mul, L₁.extensionQuotientMk_apply] at hcommRaw
    have hin : (a * b)⁻¹ * (b * a) ∈ L₁.field.toSubgroup.subgroupOf K.toSubgroup :=
      QuotientGroup.eq.mp hcommRaw
    exact (show L₁.field.toSubgroup.subgroupOf K.toSubgroup ≤
      L₁.field.toSubgroup.subgroupOf K.toSubgroup ⊔ L₂.field.toSubgroup.subgroupOf K.toSubgroup
      from le_sup_left) hin

/-- The intersection lies below its left input ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:369`]
[Yamaguchi2026]). -/
theorem intersection_le_left (L₁ L₂ : FiniteAbelianSubextension K) :
    L₁.intersection L₂ ≤ L₁ := by
  change L₁.field.toSubgroup ≤ L₁.field.toSubgroup ⊔ L₂.field.toSubgroup
  exact le_sup_left

/-- The intersection lies below its right input ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:376`]
[Yamaguchi2026]). -/
theorem intersection_le_right (L₁ L₂ : FiniteAbelianSubextension K) :
    L₁.intersection L₂ ≤ L₂ := by
  change L₂.field.toSubgroup ≤ L₁.field.toSubgroup ⊔ L₂.field.toSubgroup
  exact le_sup_right

/-- A subextension below both inputs lies below their intersection
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:383`]
[Yamaguchi2026]). -/
theorem le_intersection {P L₁ L₂ : FiniteAbelianSubextension K} (h₁ : P ≤ L₁) (h₂ : P ≤ L₂) :
    P ≤ L₁.intersection L₂ := by
  change L₁.field.toSubgroup ⊔ L₂.field.toSubgroup ≤ P.field.toSubgroup
  exact sup_le h₁ h₂

end Intersection

/-- **The norm subgroup `N_L = N_{L/K} A_L` of a finite abelian
extension** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:407`]
[Yamaguchi2026]). -/
def normSubgroup (A : Rep ℤ G) (L : FiniteAbelianSubextension K) :
    AddSubgroup (ambientFixedAddSubgroup A K) := by
  letI : Finite (K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup) := L.finite
  exact finiteNormSubgroup A K L.field L.below

/-- The norm subgroup of a finite abelian subextension is
`Atlas.Knowledge.NormTopology`'s norm subgroup of its underlying finite
Galois subextension, definitionally — the two spellings the source
keeps in two files are one object here, and the build keeps the
identification honest where a note would not. -/
theorem normSubgroup_eq_galois (A : Rep ℤ G) (L : FiniteAbelianSubextension K) :
    normSubgroup A L =
      FiniteGaloisSubextension.normSubgroup A L.toFiniteGaloisExtension :=
  rfl

/-- **An inclusion of fields reverses the inclusion of norm subgroups**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:415`]
[Yamaguchi2026]). -/
theorem normSubgroup_antitone (A : Rep ℤ G) {L₁ L₂ : FiniteAbelianSubextension K}
    (h : L₁ ≤ L₂) :
    normSubgroup A L₂ ≤ normSubgroup A L₁ := by
  letI : Finite (K.toSubgroup ⧸ L₂.field.toSubgroup.subgroupOf K.toSubgroup) := L₂.finite
  letI : Finite (K.toSubgroup ⧸ L₁.field.toSubgroup.subgroupOf K.toSubgroup) := L₁.finite
  letI hL₂L₁finite :
      Finite (L₁.field.toSubgroup ⧸ L₂.field.toSubgroup.subgroupOf L₁.field.toSubgroup) :=
    finite_extension_over_intermediate L₂.below L₁.below h
  let T : FiniteTower G :=
    { top := L₂.field
      middle := L₁.field
      base := K
      top_le_middle := h
      middle_le_base := L₁.below
      finiteTopQuotient := hL₂L₁finite
      finiteBaseQuotient := L₁.finite }
  change finiteNormSubgroup A K L₂.field L₂.below ≤ finiteNormSubgroup A K L₁.field L₁.below
  rintro _ ⟨a, rfl⟩
  refine ⟨relativeNorm A L₁.field L₂.field h a, ?_⟩
  exact T.norm_trans_apply A a

/-- The unconditional half of `N_{L₁L₂} = N_{L₁} ∩ N_{L₂}` ([Yamaguchi
2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:445`]
[Yamaguchi2026]). -/
theorem normSubgroup_compositum_le_inf (A : Rep ℤ G) (L₁ L₂ : FiniteAbelianSubextension K) :
    normSubgroup A (L₁.compositum L₂) ≤ normSubgroup A L₁ ⊓ normSubgroup A L₂ := by
  intro x hx
  exact ⟨normSubgroup_antitone A (le_compositum_left L₁ L₂) hx,
    normSubgroup_antitone A (le_compositum_right L₁ L₂) hx⟩

/-- The unconditional half of `N_{L₁ ∩ L₂} = N_{L₁} N_{L₂}`, in
additive notation ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:455`]
[Yamaguchi2026]). -/
theorem sup_normSubgroup_le_intersection [IsTopologicalGroup G] [CompactSpace G] (A : Rep ℤ G)
    (L₁ L₂ : FiniteAbelianSubextension K) :
    normSubgroup A L₁ ⊔ normSubgroup A L₂ ≤ normSubgroup A (L₁.intersection L₂) := by
  apply sup_le
  · exact normSubgroup_antitone A (intersection_le_left L₁ L₂)
  · exact normSubgroup_antitone A (intersection_le_right L₁ L₂)

end FiniteAbelianSubextension

end

end Atlas.Knowledge
