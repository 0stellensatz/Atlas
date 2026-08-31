import Mathlib
import Atlas.Knowledge.IntegerIsIntegralClosure
import Atlas.Knowledge.IntegralClosureDVR
import Atlas.Knowledge.MapMaximalIdealEqPowCardInertia
import Atlas.Knowledge.MonogenicIntegralClosure

/-!
# totally ramified monogenic

In a totally ramified extension, any irreducible element of the integral closure
generates it over the base integers: when the base maximal ideal generates the
full-degree power of the maximal ideal upstairs, the residue extension is forced
trivial by the fundamental identity `e f = n`, and the `π`-adic approximation of
`Atlas.Knowledge.MonogenicIntegralClosure.exists_mem_adjoin_sub_mem_pow` then closes at
the chosen irreducible with no residue correction needed. This sharpens
`Atlas.Knowledge.monogenicIntegralClosure` from an existence statement to a statement
about every uniformizer — the form the ramification filtration of the level tower
consumes, whose generator is a specific torsion point.

## Main statements

* `totallyRamifiedMonogenic` — under the full-degree ideal identity, the adjoin of any
  irreducible of the integral closure is everything; proved.

## Implementation notes

Total ramification enters as the ideal identity
`(𝓂[K]) · 𝒪 = 𝓂 ^ [L : K]` on the layer's own carriers `𝒪[K] → 𝒪[L]`, and is carried
to the integral-closure carrier along `Atlas.Knowledge.integerEquivIntegralClosure`;
the statement never mentions the closure of a concrete field, which keeps it
applicable wholesale. The inertia degree is computed
through Mathlib's `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing` — the local
case of the fundamental identity — against the exponent read off the identity by
`Atlas.Knowledge.MapMaximalIdealEqPowCardInertia.ramificationIdx'_eq_of_map_eq_pow`,
and a trivial inertia degree makes every residue class reachable from the base, which
is the whole of what the approximation lemma asks.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer
  New York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] [IsMixedCharLocalField L]

namespace TotallyRamifiedMonogenic

omit [ValuativeRel L] [TopologicalSpace L] [ValuativeExtension K L]
  [IsMixedCharLocalField L] in
/- The closure's maximal ideal lies over the base maximal ideal: the contraction of a
maximal ideal along an integral extension of a local domain is the maximal ideal. -/
private theorem liesOver_maximalIdeal [Algebra.IsAlgebraic K L] :
    (IsLocalRing.maximalIdeal (integralClosure ↥𝒪[K] L)).LiesOver 𝓂[K] := by
  haveI := integralClosureDVR K L
  haveI := integralClosure_isLocalRing K L
  haveI : Algebra.IsIntegral ↥𝒪[K] (integralClosure ↥𝒪[K] L) := inferInstance
  haveI := MonogenicIntegralClosure.faithfulSMul_integralClosure K L
  constructor
  exact (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (IsLocalRing.maximalIdeal (integralClosure ↥𝒪[K] L)))).symm

omit [ValuativeRel L] [TopologicalSpace L] [ValuativeExtension K L]
  [IsMixedCharLocalField L] in
/- A trivial inertia degree makes every residue class upstairs reachable from the base:
the residue extension has rank one, so its bottom subalgebra is everything. -/
private theorem residue_surjective_of_inertiaDeg_eq_one [Algebra.IsAlgebraic K L]
    (hf : Ideal.inertiaDeg' 𝓂[K]
      (IsLocalRing.maximalIdeal (integralClosure ↥𝒪[K] L)) = 1)
    (z : IsLocalRing.ResidueField (integralClosure ↥𝒪[K] L)) :
    ∃ c : ↥𝒪[K], IsLocalRing.residue (integralClosure ↥𝒪[K] L)
      (algebraMap ↥𝒪[K] (integralClosure ↥𝒪[K] L) c) = z := by
  haveI := integralClosureDVR K L
  haveI := integralClosure_isLocalRing K L
  haveI := MonogenicIntegralClosure.faithfulSMul_integralClosure K L
  haveI : IsLocalHom (algebraMap ↥𝒪[K] (integralClosure ↥𝒪[K] L)) :=
    Algebra.IsIntegral.isLocalHom ↥𝒪[K] (integralClosure ↥𝒪[K] L)
  haveI := liesOver_maximalIdeal K L
  rw [Ideal.inertiaDeg'_algebraMap] at hf
  have hbot : (⊥ : Subalgebra 𝓀[K]
      (IsLocalRing.ResidueField (integralClosure ↥𝒪[K] L))) = ⊤ :=
    Subalgebra.bot_eq_top_of_finrank_eq_one hf
  have hz : z ∈ (⊥ : Subalgebra 𝓀[K]
      (IsLocalRing.ResidueField (integralClosure ↥𝒪[K] L))) := by
    rw [hbot]
    exact Algebra.mem_top
  obtain ⟨cbar, hc⟩ := Algebra.mem_bot.mp hz
  obtain ⟨c, rfl⟩ := IsLocalRing.residue_surjective (R := ↥𝒪[K]) cbar
  exact ⟨c, by rw [← hc]; exact (IsLocalRing.ResidueField.algebraMap_residue c).symm⟩

omit [ValuativeRel L] [TopologicalSpace L] [ValuativeExtension K L]
  [IsMixedCharLocalField L] in
/- An irreducible whose residue classes are all base-reachable generates: the
approximation lemma runs at the irreducible itself, and Nakayama closes at the power
the base maximal ideal generates. -/
private theorem adjoin_eq_top_of_irreducible_of_residue [Algebra.IsAlgebraic K L]
    {x : integralClosure ↥𝒪[K] L} (hx : Irreducible x)
    (hres : ∀ z : IsLocalRing.ResidueField (integralClosure ↥𝒪[K] L),
      ∃ c : ↥𝒪[K], IsLocalRing.residue (integralClosure ↥𝒪[K] L)
        (algebraMap ↥𝒪[K] (integralClosure ↥𝒪[K] L) c) = z) :
    Algebra.adjoin ↥𝒪[K] {x} = ⊤ := by
  haveI := integralClosureDVR K L
  haveI := integralClosure_isLocalRing K L
  haveI := MonogenicIntegralClosure.faithfulSMul_integralClosure K L
  haveI : IsLocalHom (algebraMap ↥𝒪[K] (integralClosure ↥𝒪[K] L)) :=
    Algebra.IsIntegral.isLocalHom ↥𝒪[K] (integralClosure ↥𝒪[K] L)
  haveI : Module.Finite ↥𝒪[K] (integralClosure ↥𝒪[K] L) :=
    IsIntegralClosure.finite ↥𝒪[K] K L (integralClosure ↥𝒪[K] L)
  have hadj : Algebra.adjoin 𝓀[K]
      {IsLocalRing.residue (integralClosure ↥𝒪[K] L) x} = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨c, hc⟩ := hres z
    rw [← hc, ← IsLocalRing.ResidueField.algebraMap_residue]
    exact Subalgebra.algebraMap_mem _ _
  obtain ⟨m, hmm⟩ := MapMaximalIdealEqPowCardInertia.exists_map_maximalIdeal_eq_pow
    (FaithfulSMul.algebraMap_injective ↥𝒪[K] (integralClosure ↥𝒪[K] L))
  refine Algebra.toSubmodule_eq_top.mp (top_le_iff.mp ?_)
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp inferInstance)
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_
  intro z _
  obtain ⟨y, hy, hzy⟩ := MonogenicIntegralClosure.exists_mem_adjoin_sub_mem_pow hadj hx
    (Algebra.self_mem_adjoin_singleton _ _) z m
  rw [Ideal.smul_top_eq_map]
  refine Submodule.mem_sup.mpr
    ⟨y, (Subalgebra.mem_toSubmodule _).mpr hy, z - y, ?_, by ring⟩
  rw [Submodule.restrictScalars_mem, hmm]
  exact hzy

end TotallyRamifiedMonogenic

open TotallyRamifiedMonogenic in
/-- **A totally ramified extension is monogenic over any uniformizer**: when the base
maximal ideal generates the full-degree power of the maximal ideal upstairs, the
adjoin of any irreducible of the integral closure is everything
([Serre 1979, Chap. I, §6, Prop. 18, p.19][Serre1979] — Serre states the isomorphism
`B_f ≅ B` for the Eisenstein characteristic polynomial of a uniformizer, of which the
generation is the substance;
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveUniformizer.lean:394`][Yamaguchi2026]
— the source proves the adjoin conclusion at its level tower only, where this statement
is the abstract totally ramified fact). -/
theorem totallyRamifiedMonogenic
    (h𝒪 : Ideal.map (algebraMap ↥𝒪[K] ↥𝒪[L]) 𝓂[K] = 𝓂[L] ^ Module.finrank K L)
    {x : integralClosure ↥𝒪[K] L} (hx : Irreducible x) :
    Algebra.adjoin ↥𝒪[K] {x} = ⊤ := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  haveI := integralClosureDVR K L
  haveI := integralClosure_isLocalRing K L
  -- the ideal identity carried to the closure carrier
  have hcl : Ideal.map (algebraMap ↥𝒪[K] (integralClosure ↥𝒪[K] L)) 𝓂[K] =
      IsLocalRing.maximalIdeal (integralClosure ↥𝒪[K] L) ^ Module.finrank K L := by
    have hcomp : algebraMap ↥𝒪[K] (integralClosure ↥𝒪[K] L) =
        ((integerEquivIntegralClosure K L).symm : ↥𝒪[L] →+* integralClosure ↥𝒪[K] L).comp
          (algebraMap ↥𝒪[K] ↥𝒪[L]) := by
      ext c
      rw [RingHom.comp_apply]
      exact congrArg Subtype.val (integerEquivIntegralClosure_symm_algebraMap K L c).symm
    rw [hcomp, ← Ideal.map_map, h𝒪, Ideal.map_pow,
      MapMaximalIdealEqPowCardInertia.map_maximalIdeal_ringEquiv
        (integerEquivIntegralClosure K L).symm]
  -- the fundamental identity forces a trivial inertia degree
  have he := MapMaximalIdealEqPowCardInertia.ramificationIdx'_eq_of_map_eq_pow hcl
  haveI : Module.Finite ↥𝒪[K] (integralClosure ↥𝒪[K] L) :=
    IsIntegralClosure.finite ↥𝒪[K] K L (integralClosure ↥𝒪[K] L)
  haveI : IsFractionRing (integralClosure ↥𝒪[K] L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  have hef : Ideal.ramificationIdx' 𝓂[K]
        (IsLocalRing.maximalIdeal (integralClosure ↥𝒪[K] L)) *
      Ideal.inertiaDeg' 𝓂[K]
        (IsLocalRing.maximalIdeal (integralClosure ↥𝒪[K] L)) =
      Module.finrank K L :=
    Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
      (R := ↥𝒪[K]) (S := integralClosure ↥𝒪[K] L) (K := K) (L := L)
      (IsDiscreteValuationRing.not_a_field ↥𝒪[K])
  have hfr : 0 < Module.finrank K L := Module.finrank_pos
  have hf : Ideal.inertiaDeg' 𝓂[K]
      (IsLocalRing.maximalIdeal (integralClosure ↥𝒪[K] L)) = 1 := by
    rw [he] at hef
    exact Nat.eq_of_mul_eq_mul_left hfr (by rw [hef, mul_one])
  exact adjoin_eq_top_of_irreducible_of_residue K L hx
    (residue_surjective_of_inertiaDeg_eq_one K L hf)

end Atlas.Knowledge
