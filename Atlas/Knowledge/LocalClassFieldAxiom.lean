import Mathlib
import Atlas.Knowledge.AbstractRelativeUnitsNorm
import Atlas.Knowledge.ClassFieldAxiom
import Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField
import Atlas.Knowledge.HilbertNinety
import Atlas.Knowledge.NormIndexCyclic

/-!
# local units satisfy the class-field axiom

The reciprocity engine's third input, discharged: the ambient unit
representation of a mixed-characteristic local field satisfies the
class-field axiom. For a finite cyclic abstract tower the closed subgroups
become concrete fixed fields, the lower one a local field in its own right
and the upper one finite cyclic Galois over it; the engine's norm quotient
is the multiplicative norm quotient by the relative dictionary, its order is
the degree by the layer's norm-index theorem, and a vanishing norm is a
`σ − 1`-difference by Hilbert 90 — carried back through the unit
identifications of the descended representation (#104).

## Main statements

* `galoisAmbientUnits_satisfiesClassFieldAxiom` — the class-field axiom for
  the units of the algebraic closure of a mixed-characteristic local field;
  proved.

## Implementation notes

The source proves this through the Tate-cohomology form of the axiom, with
the finite-tower cardinality theorem and the cyclic homology comparisons; in
the layer's elementary form the three fields discharge directly against
`Atlas.Knowledge.normIndexCyclic` and `Atlas.Knowledge.hilbertNinety`, with
the mixed-characteristic structures on the two fixed fields produced by
`Atlas.Knowledge.exists_extension_isMixedCharLocalField` — first on the
lower field over the ground field, then on the upper field over the lower.
The source's separable-closure specialization is the algebraic closure here,
as everywhere on the arc.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

set_option maxHeartbeats 800000 in
-- The generator of the concrete Galois group is the quotient equivalence
-- applied to the abstract generator; the residue-action bookkeeping unfolds
-- it through the unit representation, and the default budget runs out inside
-- the definitional checks of the primitive's two action equations.
/-- **The class-field axiom for the local ambient units** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalClassFieldAxiom.lean:33`]
[Yamaguchi2026]). -/
theorem galoisAmbientUnits_satisfiesClassFieldAxiom
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] :
    SatisfiesClassFieldAxiom
      (galoisAmbientUnitsRep K (AlgebraicClosure K)) := by
  intro Kb Eb
  letI := Kb.finite
  letI := Eb.normal
  letI := Eb.finite
  let Ω := AlgebraicClosure K
  let F := abstractFixedField K Ω Kb.field
  let E := abstractRelativeFixedField K Ω Eb.below
  letI : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional K Ω Kb.field Kb.finite
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional
      K Ω Kb.field Eb.field Eb.below Kb.finite Eb.finite
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois K Ω Kb.field Eb.field Eb.below
      Eb.normal
  obtain ⟨vF, tF, hVF, _hVTF, hF⟩ :=
    exists_extension_isMixedCharLocalField K F
  letI := vF
  letI := tF
  letI := hVF
  letI := hF
  obtain ⟨vE, tE, hVE, _hVTE, hE⟩ :=
    exists_extension_isMixedCharLocalField F E
  letI := vE
  letI := tE
  letI := hVE
  letI := hE
  let eQ := abstractExtensionQuotientEquivGaloisGroup
    K Ω Kb.field Eb.field Eb.below Eb.normal
  let g' : E ≃ₐ[F] E := eQ Eb.generator
  have hg' : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers g' := by
    intro τ
    obtain ⟨q, rfl⟩ := eQ.surjective τ
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Eb.generates q)
    exact Subgroup.mem_zpowers_iff.mpr
      ⟨n, by rw [← map_zpow eQ Eb.generator n, hn]⟩
  have hcard := normIndexCyclic (K := F) (L := E) g' hg'
  have hposCard :
      0 < Nat.card ((F)ˣ ⧸
        (Units.map (Algebra.norm F : E →* F)).range) := by
    rw [hcard]
    exact Module.finrank_pos
  have hfiniteMul :
      Finite ((F)ˣ ⧸ (Units.map (Algebra.norm F : E →* F)).range) :=
    (Nat.card_pos_iff.mp hposCard).2
  let eNQ := finiteNormQuotientEquivRelativeNormQuotient
    K Ω Kb.field Eb.field Eb.below Eb.normal
  letI : Finite (FiniteNormQuotient
      (galoisAmbientUnitsRep K Ω) Kb.field Eb.field Eb.below) := by
    letI := hfiniteMul
    exact Finite.of_equiv _ eNQ.symm.toEquiv
  refine
    { finiteNormQuotient := ‹_›
      card_finiteNormQuotient := ?_
      exists_primitive := ?_ }
  · calc
      Nat.card (FiniteNormQuotient
          (galoisAmbientUnitsRep K Ω) Kb.field Eb.field Eb.below) =
          Nat.card (Additive ((F)ˣ ⧸
            (Units.map (Algebra.norm F : E →* F)).range)) :=
        Nat.card_congr eNQ.toEquiv
      _ = Nat.card ((F)ˣ ⧸
            (Units.map (Algebra.norm F : E →* F)).range) :=
        Nat.card_congr (Additive.toMul)
      _ = Module.finrank F E := hcard
      _ = ((FiniteAbstractExtension.ofInclusion
            Eb.field Kb.field Eb.below).degree : ℕ) :=
        (finiteAbstractExtension_degree_eq_finrank
          K Ω Kb.field Eb.field Eb.below Eb.normal Kb.finite
          Eb.finite).symm
  · intro u w hnorm
    let eL := abstractRelativeFixedFieldUnitsEquivGaloisFixed
      K Ω Kb.field Eb.field Eb.below
    let eU := abstractExtensionFixedRepresentationUnitsEquiv
      K Ω Kb.field Eb.field Eb.below Eb.normal
    let z := w - u
    have hznorm :
        relativeNorm (galoisAmbientUnitsRep K Ω)
          Kb.field Eb.field Eb.below z = 0 := by
      change relativeNorm _ Kb.field Eb.field Eb.below (w - u) = 0
      rw [map_sub, hnorm, sub_self]
    let xE : (E)ˣ := Additive.toMul (eL.symm z)
    have hxz : eL (Additive.ofMul xE) = z := eL.apply_symm_apply z
    have hxnorm : Algebra.norm F ((xE : E)) = 1 := by
      apply (algebraMap F Ω).injective
      have hval := relativeNorm_abstractRelativeFixedFieldUnit_val
        K Ω Kb.field Eb.field Eb.below Eb.normal xE
      rw [hxz, hznorm] at hval
      rw [map_one]
      exact hval.symm
    obtain ⟨y, hy⟩ := hilbertNinety hg' hxnorm
    have hyunit : y * (galUnits (K := F) g' y)⁻¹ = xE := by
      apply Units.ext
      rw [Units.val_mul,
        show ((((galUnits (K := F) g' y)⁻¹ : (E)ˣ)) : E) =
          (((galUnits (K := F) g' y : (E)ˣ)) : E)⁻¹ from
            Units.val_inv_eq_inv_val _,
        show (((galUnits (K := F) g' y : (E)ˣ)) : E) = g' (y : E) from rfl,
        ← div_eq_mul_inv]
      exact hy
    let a := eU.symm (Additive.ofMul (y⁻¹ : (E)ˣ))
    refine ⟨a, ?_⟩
    apply eU.injective
    have haction := abstractExtensionFixedRepresentationUnitsEquiv_action
      K Ω Kb.field Eb.field Eb.below Eb.normal Eb.generator a
    rw [map_sub, haction, eU.apply_symm_apply]
    have hrho :
        (galoisAmbientUnitsRep (abstractFixedField K Ω Kb.field)
            (abstractRelativeFixedField K Ω Eb.below)).ρ
            (abstractExtensionQuotientEquivGaloisGroup
              K Ω Kb.field Eb.field Eb.below Eb.normal Eb.generator)
            (Additive.ofMul (y⁻¹ : (E)ˣ)) =
          Additive.ofMul ((galUnits (K := F) g' y)⁻¹ : (E)ˣ) := by
      apply Additive.ext
      apply Units.ext
      change g' (((y⁻¹ : (E)ˣ) : E)) =
        (((galUnits (K := F) g' y)⁻¹ : (E)ˣ) : E)
      rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val,
        map_inv₀]
      rfl
    have hsub :
        Additive.ofMul ((galUnits (K := F) g' y)⁻¹ : (E)ˣ) -
            Additive.ofMul (y⁻¹ : (E)ˣ) =
          Additive.ofMul xE := by
      rw [← hyunit]
      apply Additive.ext
      change ((galUnits (K := F) g' y)⁻¹ : (E)ˣ) * (y⁻¹ : (E)ˣ)⁻¹ =
        y * (galUnits (K := F) g' y)⁻¹
      rw [inv_inv, mul_comm]
    have hgoal : eU ((extensionFixedRepresentationEquiv
        (galoisAmbientUnitsRep K (AlgebraicClosure K))
        Kb.field Eb.field Eb.below Eb.normal).symm (w - u)) =
      Additive.ofMul xE := by
      apply eL.injective
      rw [abstractRelativeUnitsEquiv_extensionUnitsEquiv,
        AddEquiv.apply_symm_apply, hxz]
    calc _ = Additive.ofMul ((galUnits (K := F) g' y)⁻¹ : (E)ˣ) -
            Additive.ofMul (y⁻¹ : (E)ˣ) :=
          congrArg (· - Additive.ofMul (y⁻¹ : (E)ˣ)) hrho
      _ = Additive.ofMul xE := hsub
      _ = eU ((extensionFixedRepresentationEquiv
          (galoisAmbientUnitsRep K (AlgebraicClosure K))
          Kb.field Eb.field Eb.below Eb.normal).symm (w - u)) := hgoal.symm

end

end Atlas.Knowledge
