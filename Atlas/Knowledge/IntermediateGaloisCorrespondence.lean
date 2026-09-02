import Mathlib
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteExtensionTransitivity
import Atlas.Knowledge.FiniteGaloisSubextension

/-!
# Intermediate Galois correspondence

For a packaged finite Galois extension `L / K` and a subgroup
`S ≤ G(L/K)`, the inverse image of `S` in `G_K` is realized as an actual
closed intermediate field `M`, and the two Galois-group identifications
`G(L/M) ≃ S` and `G(L/K)/S ≃ G(M/K)` are obtained from the actual
restriction map and the first and third isomorphism theorems — the
finite Galois correspondence in the direction the three reductions of
the abstract reciprocity proof use, with no correspondence certificate
assumed (#104).

## Main definitions

* `FiniteGaloisSubextension.intermediateField` — the closed intermediate
  field cut out by `S ≤ G(L/K)`.
* `FiniteGaloisSubextension.lowerQuotientEquiv` — the identification
  `G(L/M) ≃ S`.
* `FiniteGaloisSubextension.upperQuotientEquiv` — the identification
  `G(L/K)/S ≃ G(M/K)`.

## Main statements

* `FiniteGaloisSubextension.intermediateSubgroup_isClosed` — closedness
  of the inverse image, by its finite coset decomposition.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, so
`mem_extensionSubgroup_iff` becomes Mathlib's `Subgroup.mem_subgroupOf`,
the source's closedness lemma for the relative subgroup is inlined as
`isClosed'.preimage continuous_subtype_val` (the layer never grew the
wrapper), and five names shed the `extensionSubgroup` prefix the way the
parent item's `subgroupOf_normalInstance` did:
`subgroupOf_le_intermediateSubgroup`, `subgroupOf_intermediateField_eq`,
`subgroupOf_over_intermediate_eq_comap`,
`subgroupOf_over_intermediate_normal`, and
`subgroupOf_over_intermediate_normalInstance`.
`FiniteAbstractExtension` lives at the layer's top level rather than
inside `DegreeData`, and the tower-finiteness call is the layer's
`Atlas.Knowledge.finite_extension_over_intermediate`. The source's
`omit [IsTopologicalGroup G] in` markers port as-is.
`lowerQuotientEquiv_mk_coe` loses the source's `@[simp]`: its left-hand
side already simplifies through `lowerQuotientEquiv_mk` and
`lowerRestrictionHom_apply_coe`, so the attribute fails the simp-normal
form check; the lemma itself is unchanged.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The inverse image in `G_K` of a subgroup of `G(L/K)`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:34`]
[Yamaguchi2026]). -/
def intermediateSubgroup (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : Subgroup K.toSubgroup := by
  exact S.comap L.extensionQuotientMk

omit [IsTopologicalGroup G] in
/-- Membership in the intermediate subgroup is characterized by
membership of the underlying ambient element ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:42`]
[Yamaguchi2026]). -/
@[simp]
theorem mem_intermediateSubgroup_iff
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (k : K.toSubgroup) :
    k ∈ L.intermediateSubgroup S ↔ L.extensionQuotientMk k ∈ S :=
  Iff.rfl

omit [IsTopologicalGroup G] in
/-- The original `G_L` lies in every inverse-image subgroup
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:50`]
[Yamaguchi2026]). -/
theorem subgroupOf_le_intermediateSubgroup
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    L.field.toSubgroup.subgroupOf K.toSubgroup ≤
      L.intermediateSubgroup S := by
  intro x hx
  apply (L.mem_intermediateSubgroup_iff S x).2
  have hmk : L.extensionQuotientMk x = 1 :=
    (L.extensionQuotientMk_eq_one_iff x).2 hx
  rw [hmk]
  exact S.one_mem

/-- The `G_L`-coset classified by `q ∈ G(L/K)`, defined canonically as a
fiber of the quotient map; its public definition does not choose a
representative of `q` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:63`]
[Yamaguchi2026]). -/
def intermediateCoset (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : Set K.toSubgroup :=
  {x | L.extensionQuotientMk x = q}

/- A representative-based description used only to prove topological
facts about the canonical quotient fiber ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:69`]
[Yamaguchi2026]). -/
private def representativeIntermediateCoset (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : Set K.toSubgroup :=
  (fun x : K.toSubgroup =>
      x * Quotient.out (L.extensionQuotientMulEquiv q)) ''
    (L.field.toSubgroup.subgroupOf K.toSubgroup : Set K.toSubgroup)

omit [IsTopologicalGroup G] in
/-- Membership in the canonical coset is equality with its quotient
class ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:77`]
[Yamaguchi2026]). -/
theorem mem_intermediateCoset_iff (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) (x : K.toSubgroup) :
    x ∈ L.intermediateCoset q ↔
      L.extensionQuotientMk x = q :=
  Iff.rfl

omit [IsTopologicalGroup G] in
/- Membership in the representative-based coset is the same condition
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:84`]
[Yamaguchi2026]). -/
private theorem mem_representativeIntermediateCoset_iff
    (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) (x : K.toSubgroup) :
    x ∈ representativeIntermediateCoset L q ↔
      L.extensionQuotientMk x = q := by
  letI : (L.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L.normal
  constructor
  · rintro ⟨h, hh, rfl⟩
    apply L.extensionQuotientMulEquiv.injective
    rw [L.extensionQuotientMk_apply]
    rw [← Quotient.out_eq' (L.extensionQuotientMulEquiv q)]
    apply QuotientGroup.eq_iff_div_mem.mpr
    simpa [div_eq_mul_inv, mul_assoc] using hh
  · intro hx
    have hxout :
        (QuotientGroup.mk' (L.field.toSubgroup.subgroupOf K.toSubgroup))
            x =
          (QuotientGroup.mk'
            (L.field.toSubgroup.subgroupOf K.toSubgroup))
              (Quotient.out (L.extensionQuotientMulEquiv q)) := by
      calc
        (QuotientGroup.mk'
            (L.field.toSubgroup.subgroupOf K.toSubgroup)) x =
              L.extensionQuotientMulEquiv (L.extensionQuotientMk x) :=
          (L.extensionQuotientMk_apply x).symm
        _ = L.extensionQuotientMulEquiv q :=
          congrArg L.extensionQuotientMulEquiv hx
        _ = (QuotientGroup.mk'
            (L.field.toSubgroup.subgroupOf K.toSubgroup))
              (Quotient.out (L.extensionQuotientMulEquiv q)) :=
          (Quotient.out_eq' (L.extensionQuotientMulEquiv q)).symm
    have hdiv : x / Quotient.out (L.extensionQuotientMulEquiv q) ∈
        L.field.toSubgroup.subgroupOf K.toSubgroup :=
      QuotientGroup.eq_iff_div_mem.mp hxout
    refine ⟨x / Quotient.out (L.extensionQuotientMulEquiv q), hdiv, ?_⟩
    simp [div_eq_mul_inv, mul_assoc]

omit [IsTopologicalGroup G] in
/- The canonical coset is the representative-based one ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:121`]
[Yamaguchi2026]). -/
private theorem intermediateCoset_eq_representativeIntermediateCoset
    (L : FiniteGaloisSubextension K) (q : L.extensionQuotient) :
    L.intermediateCoset q = representativeIntermediateCoset L q := by
  ext x
  exact (mem_representativeIntermediateCoset_iff L q x).symm

omit [IsTopologicalGroup G] in
/-- The inverse image of `S` is literally the finite union of the `G_L`
cosets indexed by the elements of `S` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:130`]
[Yamaguchi2026]). -/
theorem intermediateSubgroup_eq_iUnion_cosets
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (L.intermediateSubgroup S : Set K.toSubgroup) =
      ⋃ q ∈ (S : Set L.extensionQuotient), L.intermediateCoset q := by
  ext x
  constructor
  · intro hx
    have hxS := (L.mem_intermediateSubgroup_iff S x).1 hx
    refine Set.mem_iUnion₂.mpr ⟨
      L.extensionQuotientMk x, hxS, ?_⟩
    exact (mem_intermediateCoset_iff L _ x).2 rfl
  · intro hx
    rcases Set.mem_iUnion₂.mp hx with ⟨q, hqS, hxq⟩
    apply (L.mem_intermediateSubgroup_iff S x).2
    rw [(mem_intermediateCoset_iff L q x).1 hxq]
    exact hqS

/- The representative-based coset is closed: it is a right translate of
the closed relative subgroup ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:147`]
[Yamaguchi2026]). -/
private theorem representativeIntermediateCoset_isClosed
    (L : FiniteGaloisSubextension K) (q : L.extensionQuotient) :
    IsClosed (representativeIntermediateCoset L q) := by
  exact isClosedMap_mul_right
    (Quotient.out (L.extensionQuotientMulEquiv q)) _
    (L.field.isClosed'.preimage continuous_subtype_val)

/-- Every coset in the preceding union is closed: it is the image of the
closed subgroup `G_L ≤ G_K` under right translation ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:156`]
[Yamaguchi2026]). -/
theorem intermediateCoset_isClosed (L : FiniteGaloisSubextension K)
    (q : L.extensionQuotient) : IsClosed (L.intermediateCoset q) := by
  rw [intermediateCoset_eq_representativeIntermediateCoset]
  exact representativeIntermediateCoset_isClosed L q

/-- **Closedness of the inverse image, proved by its finite coset
decomposition rather than postulated as a Galois-correspondence
property** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:163`]
[Yamaguchi2026]). -/
theorem intermediateSubgroup_isClosed (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    IsClosed (L.intermediateSubgroup S : Set K.toSubgroup) := by
  letI : Finite L.extensionQuotient := L.finite
  rw [intermediateSubgroup_eq_iUnion_cosets]
  have hfinite : (S : Set L.extensionQuotient).Finite := Set.toFinite _
  exact hfinite.isClosed_biUnion fun q _ => intermediateCoset_isClosed L q

/-- **The closed intermediate field cut out by `S ≤ G(L/K)`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:172`]
[Yamaguchi2026]). -/
def intermediateField (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : ClosedSubgroup G where
  toSubgroup := (L.intermediateSubgroup S).map K.toSubgroup.subtype
  isClosed' := by
    change IsClosed
      ((fun x : K.toSubgroup => (x : G)) ''
        (L.intermediateSubgroup S : Set K.toSubgroup))
    exact K.isClosed'.isClosedMap_subtype_val _
      (intermediateSubgroup_isClosed L S)

/-- The constructed intermediate field lies over `K` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:183`]
[Yamaguchi2026]). -/
theorem intermediateField_le_base (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.intermediateField S).toSubgroup ≤ K.toSubgroup := by
  rintro _ ⟨m, hm, rfl⟩
  exact m.property

/-- Pulling the constructed field back to `G_K` recovers exactly the
inverse-image subgroup ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:191`]
[Yamaguchi2026]). -/
theorem subgroupOf_intermediateField_eq
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (L.intermediateField S).toSubgroup.subgroupOf K.toSubgroup =
      L.intermediateSubgroup S := by
  ext x
  simp [intermediateField]
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hyx : y = x := Subtype.ext hxy
    simpa [hyx] using hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The constructed field sits under the top field: `G_L ≤ G_M`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:207`]
[Yamaguchi2026]). -/
theorem field_le_intermediateField (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    L.field.toSubgroup ≤ (L.intermediateField S).toSubgroup := by
  intro x hx
  let xK : K.toSubgroup := ⟨x, L.below hx⟩
  have hxH : xK ∈ L.field.toSubgroup.subgroupOf K.toSubgroup :=
    Subgroup.mem_subgroupOf.2 hx
  have hxP : xK ∈ L.intermediateSubgroup S :=
    L.subgroupOf_le_intermediateSubgroup S hxH
  exact ⟨xK, hxP, rfl⟩

/-- The relative subgroup for `L/M` is the pullback of `G_L ◁ G_K` along
`G_M → G_K` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:220`]
[Yamaguchi2026]). -/
theorem subgroupOf_over_intermediate_eq_comap
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    L.field.toSubgroup.subgroupOf (L.intermediateField S).toSubgroup =
      (L.field.toSubgroup.subgroupOf K.toSubgroup).comap
        (Subgroup.inclusion (L.intermediateField_le_base S)) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap,
    Subgroup.mem_subgroupOf]
  rfl

/-- `L/M` is normal because it is obtained by restricting the normal
subgroup `G_L ◁ G_K` to `G_M` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:233`]
[Yamaguchi2026]). -/
theorem subgroupOf_over_intermediate_normal
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (L.field.toSubgroup.subgroupOf
      (L.intermediateField S).toSubgroup).Normal := by
  rw [subgroupOf_over_intermediate_eq_comap]
  infer_instance

/-- The relative subgroup over an intermediate field is normal in the
intermediate subgroup ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:241`]
[Yamaguchi2026]). -/
instance subgroupOf_over_intermediate_normalInstance
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (L.field.toSubgroup.subgroupOf
      (L.intermediateField S).toSubgroup).Normal :=
  L.subgroupOf_over_intermediate_normal S

/-- The lower extension `L/M` is finite ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:248`]
[Yamaguchi2026]). -/
theorem extension_over_intermediate_finite
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    Finite ((L.intermediateField S).toSubgroup ⧸
      L.field.toSubgroup.subgroupOf (L.intermediateField S).toSubgroup) := by
  letI : Finite (K.toSubgroup ⧸
      L.field.toSubgroup.subgroupOf K.toSubgroup) := L.finite
  exact Atlas.Knowledge.finite_extension_over_intermediate
    L.below (L.intermediateField_le_base S)
      (L.field_le_intermediateField S)

/-- The intermediate extension `M/K` is finite, since its subgroup
contains the finite-index subgroup `G_L` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:261`]
[Yamaguchi2026]). -/
theorem intermediateField_finite
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    Finite (K.toSubgroup ⧸
      (L.intermediateField S).toSubgroup.subgroupOf K.toSubgroup) := by
  rw [subgroupOf_intermediateField_eq]
  letI : (L.field.toSubgroup.subgroupOf K.toSubgroup).FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient K.toSubgroup _
      (L.field.toSubgroup.subgroupOf K.toSubgroup) L.finite
  letI : (L.intermediateSubgroup S).FiniteIndex :=
    Subgroup.finiteIndex_of_le (L.subgroupOf_le_intermediateSubgroup S)
  exact Subgroup.finite_quotient_of_finiteIndex

/-- The generally non-Galois finite extension `L^S/K` attached to an
arbitrary subgroup `S ≤ G(L/K)`; normality is deliberately absent from
this bundle, and clients that only need finite-extension invariants
should use it rather than forcing `S` through `intermediateFiniteGalois`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:277`]
[Yamaguchi2026]). -/
def intermediateFiniteAbstractExtension
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    FiniteAbstractExtension G where
  field := L.intermediateField S
  base := K
  below := L.intermediateField_le_base S
  finiteQuotient := L.intermediateField_finite S

omit [IsTopologicalGroup G] in
/-- A normal subgroup `S ◁ G(L/K)` has normal inverse image in `G_K`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:287`]
[Yamaguchi2026]). -/
theorem intermediateSubgroup_normal
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (hS : S.Normal) : (L.intermediateSubgroup S).Normal := by
  letI : S.Normal := hS
  exact hS.comap L.extensionQuotientMk

/-- Hence `M/K` is normal whenever `S` is normal ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:294`]
[Yamaguchi2026]). -/
theorem intermediateField_normal
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (hS : S.Normal) :
    ((L.intermediateField S).toSubgroup.subgroupOf K.toSubgroup).Normal := by
  rw [subgroupOf_intermediateField_eq]
  exact L.intermediateSubgroup_normal S hS

/-- The actual finite Galois extension `L/M` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:303`]
[Yamaguchi2026]). -/
def lowerFiniteGalois (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    FiniteGaloisSubextension (L.intermediateField S) where
  field := L.field
  below := L.field_le_intermediateField S
  normal := L.subgroupOf_over_intermediate_normal S
  finite := L.extension_over_intermediate_finite S

/-- If `S` is normal, the actual finite Galois extension `M/K`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:312`]
[Yamaguchi2026]). -/
def intermediateFiniteGalois (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) (hS : S.Normal) :
    FiniteGaloisSubextension K where
  field := L.intermediateField S
  below := L.intermediateField_le_base S
  normal := L.intermediateField_normal S hS
  finite := L.intermediateField_finite S

/-- Restriction from `G_M` to the subgroup `S ≤ G(L/K)`; the codomain
membership proof is supplied by the defining inverse-image equation for
`M` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:323`]
[Yamaguchi2026]). -/
def lowerRestrictionHom (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.intermediateField S).toSubgroup →* S :=
  (L.extensionQuotientMk.comp
      (Subgroup.inclusion (L.intermediateField_le_base S))).codRestrict S
    (by
      intro m
      apply (L.mem_intermediateSubgroup_iff S _).1
      rw [← subgroupOf_intermediateField_eq L S]
      exact Subgroup.mem_subgroupOf.2 m.property)

/-- The lower restriction homomorphism evaluates by restricting the
underlying ambient automorphism ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:341`]
[Yamaguchi2026]). -/
@[simp]
theorem lowerRestrictionHom_apply_coe (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    ((L.lowerRestrictionHom S m : S) : L.extensionQuotient) =
      L.extensionQuotientMk
        (Subgroup.inclusion (L.intermediateField_le_base S) m) :=
  rfl

/-- Every element of `S` is represented by an element of `G_M`; hence
the restriction map is onto ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:351`]
[Yamaguchi2026]). -/
theorem lowerRestrictionHom_surjective (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    Function.Surjective (L.lowerRestrictionHom S) := by
  intro s
  rcases L.extensionQuotientMk_surjective s.1 with ⟨k, hk⟩
  have hkP : k ∈ L.intermediateSubgroup S := by
    apply (L.mem_intermediateSubgroup_iff S k).2
    rw [hk]
    exact s.property
  let m : (L.intermediateField S).toSubgroup :=
    ⟨k.1, ⟨k, hkP, rfl⟩⟩
  refine ⟨m, ?_⟩
  apply Subtype.ext
  rw [lowerRestrictionHom_apply_coe]
  change L.extensionQuotientMk k = s
  exact hk

/-- The kernel of restriction is exactly `G_L` viewed inside `G_M`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:369`]
[Yamaguchi2026]). -/
theorem lowerRestrictionHom_ker (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    MonoidHom.ker (L.lowerRestrictionHom S) =
      L.field.toSubgroup.subgroupOf (L.intermediateField S).toSubgroup := by
  ext m
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hm
    let mK : K.toSubgroup :=
      ⟨m.1, L.intermediateField_le_base S m.property⟩
    have hq :
        ((L.lowerRestrictionHom S m : S) : L.extensionQuotient) = 1 :=
      congrArg Subtype.val hm
    rw [lowerRestrictionHom_apply_coe] at hq
    have hH : mK ∈ L.field.toSubgroup.subgroupOf K.toSubgroup :=
      (L.extensionQuotientMk_eq_one_iff mK).1 hq
    exact Subgroup.mem_subgroupOf.1 hH
  · intro hm
    let mK : K.toSubgroup :=
      ⟨m.1, L.intermediateField_le_base S m.property⟩
    have hH : mK ∈ L.field.toSubgroup.subgroupOf K.toSubgroup :=
      Subgroup.mem_subgroupOf.2 hm
    have hq : L.extensionQuotientMk mK = 1 :=
      (L.extensionQuotientMk_eq_one_iff mK).2 hH
    apply Subtype.ext
    rw [lowerRestrictionHom_apply_coe]
    exact hq

/-- **The first actual Galois-group identification used:
`G(L/M) ≃ S`** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:401`]
[Yamaguchi2026]). -/
def lowerQuotientEquiv (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.lowerFiniteGalois S).extensionQuotient ≃* S := by
  letI : (L.field.toSubgroup.subgroupOf
      (L.intermediateField S).toSubgroup).Normal :=
    L.subgroupOf_over_intermediate_normal S
  exact (L.lowerFiniteGalois S).extensionQuotientMulEquiv.trans
    ((QuotientGroup.quotientMulEquivOfEq
        (L.lowerRestrictionHom_ker S).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (L.lowerRestrictionHom S) (L.lowerRestrictionHom_surjective S)))

/-- Representative formula for `G(L/M) ≃ S` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:415`]
[Yamaguchi2026]). -/
@[simp]
theorem lowerQuotientEquiv_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    L.lowerQuotientEquiv S
        ((L.lowerFiniteGalois S).extensionQuotientMk m) =
      L.lowerRestrictionHom S m := by
  letI : (L.field.toSubgroup.subgroupOf
      (L.intermediateField S).toSubgroup).Normal :=
    L.subgroupOf_over_intermediate_normal S
  change
    ((QuotientGroup.quotientMulEquivOfEq
        (L.lowerRestrictionHom_ker S).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective
        (L.lowerRestrictionHom S) (L.lowerRestrictionHom_surjective S)))
      (QuotientGroup.mk m) = L.lowerRestrictionHom S m
  rfl

/-- The same representative formula after forgetting the subtype `S`;
this is the form used when composing restriction maps in the reduction
diagram ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:435`]
[Yamaguchi2026]). -/
theorem lowerQuotientEquiv_mk_coe (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    ((L.lowerQuotientEquiv S
        ((L.lowerFiniteGalois S).extensionQuotientMk m) : S) :
          L.extensionQuotient) =
      L.extensionQuotientMk
        ⟨m.1, L.intermediateField_le_base S m.property⟩ := by
  rw [lowerQuotientEquiv_mk, lowerRestrictionHom_apply_coe]
  apply congrArg L.extensionQuotientMk
  exact Subtype.ext (by rfl)

omit [IsTopologicalGroup G] in
/-- Mapping the inverse image of `S` back to `G(L/K)` recovers `S`
itself ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:450`]
[Yamaguchi2026]). -/
theorem intermediateSubgroup_map_quotient_eq
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    (L.intermediateSubgroup S).map L.extensionQuotientMk = S := by
  exact Subgroup.map_comap_eq_self_of_surjective
    L.extensionQuotientMk_surjective S

/-- The subgroup attached to the intermediate extension is normal
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:457`]
[Yamaguchi2026]). -/
instance intermediateSubgroup_normalInstance
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    [hS : S.Normal] : (L.intermediateSubgroup S).Normal :=
  L.intermediateSubgroup_normal S hS

/-- The field represented by a normal intermediate subgroup is a normal
subextension ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:463`]
[Yamaguchi2026]). -/
instance intermediateField_normalInstance
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    [hS : S.Normal] :
    ((L.intermediateField S).toSubgroup.subgroupOf K.toSubgroup).Normal :=
  L.intermediateField_normal S hS

/-- The third-isomorphism identification used in the normal-subextension
diagram: `G(L/K)/S ≃ G(M/K)` — the named type ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:472`]
[Yamaguchi2026]). -/
def upperQuotient (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) : Type _ :=
  L.extensionQuotient ⧸ S

/-- The upper quotient over an intermediate field carries its canonical
group structure ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:477`]
[Yamaguchi2026]). -/
instance upperQuotient_groupInstance (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    Group (L.upperQuotient S) := by
  change Group (L.extensionQuotient ⧸ S)
  infer_instance

/-- Comparison with the group-library presentation of the upper quotient
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:484`]
[Yamaguchi2026]). -/
def upperQuotientMulEquiv (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.upperQuotient S ≃* (L.extensionQuotient ⧸ S) :=
  MulEquiv.refl _

/-- The canonical projection to the named upper quotient
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:490`]
[Yamaguchi2026]). -/
def upperQuotientMk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.extensionQuotient →* L.upperQuotient S :=
  QuotientGroup.mk' S

omit [IsTopologicalGroup G] in
/-- The named upper quotient projection agrees with the underlying
quotient-group projection ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:498`]
[Yamaguchi2026]). -/
@[simp]
theorem upperQuotientMk_apply (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal]
    (q : L.extensionQuotient) :
    L.upperQuotientMulEquiv S (L.upperQuotientMk S q) =
      (QuotientGroup.mk q : L.extensionQuotient ⧸ S) :=
  rfl

/-- **The third-isomorphism identification, with both source and target
kept behind their named finite-Galois quotient boundaries**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:507`]
[Yamaguchi2026]). -/
def upperQuotientEquiv (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.upperQuotient S ≃*
      (L.intermediateFiniteGalois S inferInstance).extensionQuotient := by
  let H := L.field.toSubgroup.subgroupOf K.toSubgroup
  let P := L.intermediateSubgroup S
  let π : K.toSubgroup →* L.extensionQuotient := L.extensionQuotientMk
  have hHP : H ≤ P := L.subgroupOf_le_intermediateSubgroup S
  have hmap : P.map π = S := L.intermediateSubgroup_map_quotient_eq S
  have hupper : (L.intermediateField S).toSubgroup.subgroupOf
      K.toSubgroup = P :=
    L.subgroupOf_intermediateField_eq S
  letI : H.Normal := L.normal
  letI : P.Normal := L.intermediateSubgroup_normal S inferInstance
  letI : (P.map π).Normal := by rw [hmap]; infer_instance
  exact (L.upperQuotientMulEquiv S).trans
    ((QuotientGroup.quotientMulEquivOfEq hmap.symm).trans
      ((QuotientGroup.quotientQuotientEquivQuotient H P hHP).trans
        ((QuotientGroup.quotientMulEquivOfEq hupper.symm).trans
          (L.intermediateFiniteGalois S
            inferInstance).extensionQuotientMulEquiv.symm)))

/-- Representative formula for `G(L/K)/S ≃ G(M/K)` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/IntermediateExtension.lean:530`]
[Yamaguchi2026]). -/
@[simp]
theorem upperQuotientEquiv_mk_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] (k : K.toSubgroup) :
    L.upperQuotientEquiv S
        (L.upperQuotientMk S (L.extensionQuotientMk k)) =
      (L.intermediateFiniteGalois S inferInstance).extensionQuotientMk k := by
  let H := L.field.toSubgroup.subgroupOf K.toSubgroup
  let P := L.intermediateSubgroup S
  let π : K.toSubgroup →* L.extensionQuotient := L.extensionQuotientMk
  have hHP : H ≤ P := L.subgroupOf_le_intermediateSubgroup S
  have hmap : P.map π = S := L.intermediateSubgroup_map_quotient_eq S
  have hupper : (L.intermediateField S).toSubgroup.subgroupOf
      K.toSubgroup = P :=
    L.subgroupOf_intermediateField_eq S
  letI : H.Normal := L.normal
  letI : P.Normal := L.intermediateSubgroup_normal S inferInstance
  letI : (P.map π).Normal := by rw [hmap]; infer_instance
  change
    (L.intermediateFiniteGalois S
        inferInstance).extensionQuotientMulEquiv.symm
      ((QuotientGroup.quotientMulEquivOfEq hupper.symm)
        ((QuotientGroup.quotientQuotientEquivQuotient H P hHP)
          ((QuotientGroup.quotientMulEquivOfEq hmap.symm)
            (QuotientGroup.mk (L.extensionQuotientMk k))))) =
      (L.intermediateFiniteGalois S inferInstance).extensionQuotientMk k
  apply
    (L.intermediateFiniteGalois S
      inferInstance).extensionQuotientMulEquiv.injective
  rw [MulEquiv.apply_symm_apply,
    (L.intermediateFiniteGalois S inferInstance).extensionQuotientMk_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  have hmk :
      L.extensionQuotientMk k =
        (QuotientGroup.mk k : K.toSubgroup ⧸ H) := by
    change L.extensionQuotientMulEquiv (L.extensionQuotientMk k) =
      (QuotientGroup.mk k : K.toSubgroup ⧸ H)
    exact L.extensionQuotientMk_apply k
  rw [hmk]
  have hthird :
      (QuotientGroup.quotientQuotientEquivQuotient H P hHP)
          ((QuotientGroup.mk
            (QuotientGroup.mk k : K.toSubgroup ⧸ H)) :
              (K.toSubgroup ⧸ H) ⧸
                P.map (QuotientGroup.mk' H)) =
        (QuotientGroup.mk k : K.toSubgroup ⧸ P) := by
    exact
      QuotientGroup.quotientQuotientEquivQuotientAux_mk_mk H P hHP k
  calc
    _ =
        (QuotientGroup.quotientMulEquivOfEq hupper.symm)
          (QuotientGroup.mk k : K.toSubgroup ⧸ P) :=
      congrArg (QuotientGroup.quotientMulEquivOfEq hupper.symm) hthird
    _ = _ := QuotientGroup.quotientMulEquivOfEq_mk hupper.symm k

end FiniteGaloisSubextension

end

end Atlas.Knowledge
