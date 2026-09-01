import Mathlib
import Atlas.Knowledge.AbstractFixedField
import Atlas.Knowledge.AbstractFixedFieldUnitsEquiv
import Atlas.Knowledge.LocalBaseValuation
import Atlas.Knowledge.NormalizedValuationNormSeparable

/-!
# norm range of an abstract fixed field

The valuation datum's remaining condition, computed: for an arbitrary finite
abstract field — not necessarily normal over the local ground field — the
image of the base valuation after the engine's norm is exactly the
residue-degree multiple of the value group. The engine's norm is the field
norm of the concrete fixed field by the coset comparison, and the normalized
valuation of a field norm is the residue degree times the normalized
valuation upstairs, which is the layer's separable norm law (#104).

## Main statements

* `normToBase_abstractFixedFieldUnit_val_of_isSeparable` — the engine's norm
  from an abstract fixed field is the field norm; proved.
* `localBaseValuation_normToBase_abstractFixedFieldUnit` — the base
  valuation of the engine's norm through the normalized valuation; proved.
* `localBaseValuation_comp_normToBase_range_eq_residueFinrank` — the range
  of the base valuation after the norm is `f·Z`; proved.

## Implementation notes

The source's units-level norm is spelled `Units.map` of Mathlib's
`Algebra.norm`, as in the layer's norm law, and the coset transport keeps
the source's explicit congruence to avoid dependent rewriting through the
inclusion proof carried by the relative norm. The range computation closes
on `Atlas.Knowledge.normalizedValuation_norm_of_isSeparable` read through
`Atlas.Knowledge.inertiaDeg_eq_finrank_residueField`, so the fixed field's
hypotheses are the mixed-characteristic carrier of the layer's norm law
where the source assumes a nonarchimedean local field with extension and
integral-closure witnesses. The base-valuation comparison shows the layer's
`Atlas.Knowledge.normalizedValuationAddHom` where the source's line shows
its inverse-standard valuation map — the sign fork recorded with the base
valuation; both statements here are invariant under it.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

universe u

/-- The relative norm's underlying value is unchanged under transport of its
closed-subgroup indices — kept explicit to avoid dependent rewriting through
the inclusion proof ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean:29`]
[Yamaguchi2026]). -/
theorem relativeNorm_coe_eq_of_closedSubgroup_eq
    {G : Type u} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G)
    (B B' C C' : ClosedSubgroup G)
    (hCB : C.toSubgroup ≤ B.toSubgroup)
    (hC'B' : C'.toSubgroup ≤ B'.toSubgroup)
    [hfinite : Finite
      (B.toSubgroup ⧸ C.toSubgroup.subgroupOf B.toSubgroup)]
    [hfinite' : Finite
      (B'.toSubgroup ⧸ C'.toSubgroup.subgroupOf B'.toSubgroup)]
    (hB : B = B') (hC : C = C')
    (x : ambientFixedAddSubgroup A C)
    (x' : ambientFixedAddSubgroup A C')
    (hx : x.1 = x'.1) :
    ((relativeNorm A B C hCB x : ambientFixedAddSubgroup A B) : A.V) =
      ((relativeNorm A B' C' hC'B' x' :
        ambientFixedAddSubgroup A B') : A.V) := by
  subst B'
  subst C'
  have hle : hCB = hC'B' := Subsingleton.elim _ _
  subst hC'B'
  have hfin : hfinite = hfinite' := Subsingleton.elim _ _
  subst hfinite'
  have hxx' : x = x' := Subtype.ext hx
  subst x'
  rfl

section Ambient

variable (K : Type*) (Ω : Type*) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsAlgClosed Ω]

/-- **The engine's norm from an abstract fixed field is the field norm** of
its concrete fixed field, without normality ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean:59`]
[Yamaguchi2026]). -/
theorem normToBase_abstractFixedFieldUnit_val_of_isSeparable
    (H : ClosedSubgroup (Ω ≃ₐ[K] Ω))
    [Finite ((baseField (Ω ≃ₐ[K] Ω)).toSubgroup ⧸
      H.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[K] Ω)).toSubgroup)]
    [FiniteDimensional K (abstractFixedField K Ω H)]
    [Algebra.IsSeparable K (abstractFixedField K Ω H)]
    (x : (abstractFixedField K Ω H)ˣ) :
    ((Additive.toMul
      ((normToBase (galoisAmbientUnitsRep K Ω) H
        (abstractFixedFieldUnitsEquivGaloisFixed K Ω H
          (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
      algebraMap K Ω (Algebra.norm K
        (x : abstractFixedField K Ω H)) := by
  let E := abstractFixedField K Ω H
  let y : ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω) H :=
    abstractFixedFieldUnitsEquivGaloisFixed K Ω H (Additive.ofMul x)
  let yE := intermediateFieldUnitsEquivGaloisFixed K Ω E (Additive.ofMul x)
  have hy : yE.1 = y.1 := by
    rw [intermediateFieldUnitsEquivGaloisFixed_coe]
    exact (abstractFixedFieldUnitsEquivGaloisFixed_coe
      K Ω H (Additive.ofMul x)).symm
  have hnorm :=
    relativeNorm_intermediateFieldUnit_val_of_isSeparable K Ω E x
  have htransport := relativeNorm_coe_eq_of_closedSubgroup_eq
    (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup (⊥ : IntermediateField K Ω))
    (baseField (Ω ≃ₐ[K] Ω))
    (closedFixingSubgroup E) H
    (fixingSubgroupLeBase K Ω E) (le_baseField H)
    (closedFixingSubgroup_bot_eq_baseField K Ω)
    (closedFixingSubgroup_abstractFixedField_eq K Ω H)
    yE y hy
  have htransport' := congrArg
    (fun z : Additive Ωˣ => ((Additive.toMul z : Ωˣ) : Ω)) htransport
  change
    ((Additive.toMul
      ((normToBase (galoisAmbientUnitsRep K Ω) H y).1 :
        Additive Ωˣ) : Ωˣ) : Ω) = _
  exact htransport'.symm.trans hnorm

end Ambient

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- **The base valuation of the engine's norm is the normalized valuation of
the field norm** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean:101`]
[Yamaguchi2026]). -/
theorem localBaseValuation_normToBase_abstractFixedFieldUnit
    (H : ClosedSubgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
    [Finite ((baseField
        (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).toSubgroup ⧸
      H.toSubgroup.subgroupOf (baseField
        (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).toSubgroup)]
    [FiniteDimensional K
      (abstractFixedField K (AlgebraicClosure K) H)]
    (x : (abstractFixedField K (AlgebraicClosure K) H)ˣ) :
    localBaseValuation K
        (normToBase
          (galoisAmbientUnitsRep K (AlgebraicClosure K)) H
          (abstractFixedFieldUnitsEquivGaloisFixed
            K (AlgebraicClosure K) H (Additive.ofMul x))) =
      Int.castRingHom ProfiniteInteger
        (normalizedValuationAddHom K
          (Additive.ofMul
            (Units.map
              ((Algebra.norm K :
                abstractFixedField K (AlgebraicClosure K) H →* K)) x))) := by
  let E := abstractFixedField K (AlgebraicClosure K) H
  let a := normToBase
    (galoisAmbientUnitsRep K (AlgebraicClosure K)) H
    (abstractFixedFieldUnitsEquivGaloisFixed
      K (AlgebraicClosure K) H (Additive.ofMul x))
  have ha : (baseFieldUnitsEquiv K).symm a =
      Additive.ofMul (Units.map ((Algebra.norm K : E →* K)) x) := by
    apply (baseFieldUnitsEquiv K).injective
    rw [(baseFieldUnitsEquiv K).apply_symm_apply]
    apply Subtype.ext
    apply Additive.ext
    apply Units.ext
    calc
      ((Additive.toMul
          ((normToBase
            (galoisAmbientUnitsRep K (AlgebraicClosure K)) H
            (abstractFixedFieldUnitsEquivGaloisFixed
              K (AlgebraicClosure K) H (Additive.ofMul x))).1 :
              Additive (AlgebraicClosure K)ˣ) :
            (AlgebraicClosure K)ˣ) : AlgebraicClosure K) =
          algebraMap K (AlgebraicClosure K)
            (Algebra.norm K (x : E)) :=
        normToBase_abstractFixedFieldUnit_val_of_isSeparable
          K (AlgebraicClosure K) H x
      _ = algebraMap K (AlgebraicClosure K)
          ((Units.map ((Algebra.norm K : E →* K)) x : Kˣ) : K) := rfl
      _ =
          ((Additive.toMul
            ((baseFieldUnitsEquiv K
              (Additive.ofMul
                (Units.map ((Algebra.norm K : E →* K)) x))).1 :
                Additive (AlgebraicClosure K)ˣ) :
              (AlgebraicClosure K)ˣ) : AlgebraicClosure K) :=
        (baseFieldUnitsEquiv_val K
          (Units.map ((Algebra.norm K : E →* K)) x)).symm
  rw [show normToBase
      (galoisAmbientUnitsRep K (AlgebraicClosure K)) H
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (AlgebraicClosure K) H (Additive.ofMul x)) = a from rfl]
  change Int.castRingHom ProfiniteInteger
      (normalizedValuationAddHom K
        ((baseFieldUnitsEquiv K).symm a)) = _
  rw [ha]

/-- **The range of the base valuation after the engine's norm is the
residue-degree multiple of the value group** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean:166`]
[Yamaguchi2026]). -/
theorem localBaseValuation_comp_normToBase_range_eq_residueFinrank
    (H : ClosedSubgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
    [Finite ((baseField
        (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).toSubgroup ⧸
      H.toSubgroup.subgroupOf (baseField
        (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)).toSubgroup)]
    [FiniteDimensional K
      (abstractFixedField K (AlgebraicClosure K) H)]
    [ValuativeRel (abstractFixedField K (AlgebraicClosure K) H)]
    [TopologicalSpace (abstractFixedField K (AlgebraicClosure K) H)]
    [ValuativeExtension K (abstractFixedField K (AlgebraicClosure K) H)]
    [IsMixedCharLocalField
      (abstractFixedField K (AlgebraicClosure K) H)] :
    ((localBaseValuation K).comp
      (normToBase
        (galoisAmbientUnitsRep K (AlgebraicClosure K)) H)).range =
      nsmulImage (localBaseValuation K).range
        (Module.finrank 𝓀[K]
          𝓀[abstractFixedField K (AlgebraicClosure K) H]) := by
  let E := abstractFixedField K (AlgebraicClosure K) H
  let f := Module.finrank 𝓀[K] 𝓀[E]
  have hlaw : ∀ y : Eˣ,
      normalizedValuationAddHom K
          (Additive.ofMul (Units.map ((Algebra.norm K : E →* K)) y)) =
        (f : ℤ) * normalizedValuation E y := by
    intro y
    have hnorm := normalizedValuation_norm_of_isSeparable K E y
    rw [inertiaDeg_eq_finrank_residueField K E] at hnorm
    exact hnorm
  ext z
  constructor
  · rintro ⟨a, rfl⟩
    let x : Additive Eˣ :=
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (AlgebraicClosure K) H).symm a
    have hxa : abstractFixedFieldUnitsEquivGaloisFixed
        K (AlgebraicClosure K) H x = a :=
      (abstractFixedFieldUnitsEquivGaloisFixed
        K (AlgebraicClosure K) H).apply_symm_apply a
    rw [← hxa]
    change localBaseValuation K
      (normToBase (galoisAmbientUnitsRep K (AlgebraicClosure K)) H
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (AlgebraicClosure K) H
            (Additive.ofMul (Additive.toMul x)))) ∈ _
    rw [localBaseValuation_normToBase_abstractFixedFieldUnit]
    rw [hlaw (Additive.toMul x), mem_nsmulImage_iff]
    refine ⟨Int.castRingHom ProfiniteInteger
        (normalizedValuation E (Additive.toMul x)),
      intCast_mem_localBaseValuation_range K _, ?_⟩
    rw [← map_nsmul]
    congr 1
  · rw [mem_nsmulImage_iff]
    rintro ⟨w, hw, hwz⟩
    rw [localBaseValuation_range K] at hw
    obtain ⟨m, rfl⟩ := hw
    obtain ⟨y, hy⟩ := normalizedValuation_surjective E m
    refine ⟨abstractFixedFieldUnitsEquivGaloisFixed
      K (AlgebraicClosure K) H (Additive.ofMul y), ?_⟩
    change localBaseValuation K
      (normToBase (galoisAmbientUnitsRep K (AlgebraicClosure K)) H
        (abstractFixedFieldUnitsEquivGaloisFixed
          K (AlgebraicClosure K) H (Additive.ofMul y))) = z
    rw [localBaseValuation_normToBase_abstractFixedFieldUnit,
      hlaw y, hy]
    calc
      Int.castRingHom ProfiniteInteger ((f : ℤ) * m) =
          f • Int.castRingHom ProfiniteInteger m := by
        rw [← map_nsmul]
        congr 1
      _ = z := hwz

end

end Atlas.Knowledge
