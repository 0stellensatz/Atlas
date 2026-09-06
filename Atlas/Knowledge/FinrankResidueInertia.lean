import Mathlib
import Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField
import Atlas.Knowledge.IntegerIsIntegralClosure
import Atlas.Knowledge.IntegralClosureDVR
import Atlas.Knowledge.LowerRamificationGroup
import Atlas.Knowledge.MapMaximalIdealEqPowCardInertia
import Atlas.Knowledge.NormalizedValuationNormSeparable
import Atlas.Knowledge.RamificationNumberRestrictScalars

/-!
# residue degree times inertia order

The fundamental identity of a finite Galois extension of
mixed-characteristic local fields at the middle floor of a tower: the
relative degree is the residue degree times the order of the zeroth
ramification group, `[E : F] = f · #G₀(E/F)` — with the residue tower
multiplicativity that reads relative residue degrees off absolute
ones (#104).

## Main statements

* `finrank_eq_finrank_residueField_mul_card_inertia` — the degree is
  the residue degree times the inertia order; proved.
* `residueFinrank_mul_residueFinrank` — the residue degree is
  multiplicative along a valuative tower; proved.
* `valuativeExtension_trans` — valuative extensions compose along a
  scalar tower; proved.

## Implementation notes

The identity assembles the layer's ideal-model lemmas: the maximal
ideal maps to the power of the inertia order in the
`𝒪[K]`-integral-closure model, transported to the `𝒪[F]`-model along
the carrier identifications, where Mathlib's local fundamental identity
and the inertia-degree reading on residue fields close it. The model
transport mirrors, in reverse, the block its dependency runs internally
— exposing the intermediate `𝒪[F]`-model form upstream would collapse
it, a cleanup-pass item on the ledger. The middle field's topology
never appears in the statement — the mixed-characteristic structure the
residue reading needs upstairs is conjured inside the proof from the
valuative topology. The tower lemma is the residue-field `finrank`
tower; its one load-bearing step is the integer-level `IsScalarTower`,
and its statement binds the base-to-top extension witness — the
conclusion's residue module needs it before any proof step — which
callers derive by the transitivity item. Neither flagship is ported:
the source's counterpart of the identity is
`LocalFieldTheory/NonarchimedeanLocalField/ResidueExtension.lean:362`
in its own model vocabulary, and the tower lemma formalizes no
literature statement beyond the `finrank` tower of the residue degrees.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

/-- Valuative extensions compose along a scalar tower. -/
theorem valuativeExtension_trans
    (K F E : Type*) [Field K] [ValuativeRel K] [Field F] [ValuativeRel F]
    [Field E] [ValuativeRel E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [ValuativeExtension K F] [ValuativeExtension F E] :
    ValuativeExtension K E :=
  ⟨fun a b => by
    rw [IsScalarTower.algebraMap_apply K F E,
      IsScalarTower.algebraMap_apply K F E,
      ValuativeExtension.vle_iff_vle, ValuativeExtension.vle_iff_vle]⟩

/-- The residue-field degree is multiplicative along a valuative tower
of fields: `[𝓀[E] : 𝓀[K]] = [𝓀[F] : 𝓀[K]] · [𝓀[E] : 𝓀[F]]` — the
`finrank` tower of the residue degrees `f` of [Serre 1979, Chap. I,
§4, p.14][Serre1979]. -/
theorem residueFinrank_mul_residueFinrank
    (K F E : Type*) [Field K] [ValuativeRel K] [Field F] [ValuativeRel F]
    [Field E] [ValuativeRel E]
    [Algebra K F] [Algebra F E] [Algebra K E] [IsScalarTower K F E]
    [ValuativeExtension K F] [ValuativeExtension F E]
    [ValuativeExtension K E] :
    Module.finrank 𝓀[K] 𝓀[E] =
      Module.finrank 𝓀[K] 𝓀[F] * Module.finrank 𝓀[F] 𝓀[E] := by
  haveI : IsScalarTower ↥𝒪[K] ↥𝒪[F] ↥𝒪[E] :=
    IsScalarTower.of_algebraMap_eq fun x =>
      Subtype.ext (IsScalarTower.algebraMap_apply K F E (x : K))
  exact (Module.finrank_mul_finrank 𝓀[K] 𝓀[F] 𝓀[E]).symm

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsMixedCharLocalField F] [Algebra K F] [ValuativeExtension K F]
  [FiniteDimensional K F]
variable (E : Type*) [Field E] [ValuativeRel E] [Algebra K E] [Algebra F E]
  [IsScalarTower K F E] [ValuativeExtension F E] [FiniteDimensional K E]
  [IsGalois F E]

include K in
/-- **The relative degree is the residue degree times the inertia
order**: `[E : F] = [𝓀[E] : 𝓀[F]] · #G₀(E/F)` for a finite Galois
extension at the middle floor of a mixed-characteristic tower — the
single-prime local case of `n = Σ e·f` with the ramification index
read as the order of the zeroth ramification group ([Serre 1979,
Chap. I, §4, Prop. 10, pp.14–15][Serre1979]; the source counterpart,
in its own model vocabulary, is Yamaguchi 2026,
`LocalFieldTheory/NonarchimedeanLocalField/ResidueExtension.lean:362`). -/
theorem finrank_eq_finrank_residueField_mul_card_inertia :
    Module.finrank F E =
      Module.finrank 𝓀[F] 𝓀[E] * Nat.card (lowerRamificationGroup F E 0) := by
  classical
  haveI : Algebra.IsAlgebraic K F := Algebra.IsAlgebraic.of_finite K F
  haveI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  haveI : FiniteDimensional F E := Module.Finite.right K F E
  haveI : Algebra.IsAlgebraic F E := Algebra.IsAlgebraic.of_finite F E
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : Algebra.IsSeparable F E := inferInstance
  -- the ideal identity in the `𝒪[K]`-model, exponent the inertia order
  have h1 : Ideal.map ((AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] F E) :
        integralClosure 𝒪[K] F →+* integralClosure 𝒪[K] E))
      (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] F)) =
      IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E) ^
        Nat.card (lowerRamificationGroup F E 0) :=
    map_maximalIdeal_eq_pow_card_inertia K E F
  -- the two carrier identifications
  let ε : integralClosure 𝒪[K] F ≃+* 𝒪[F] := integerEquivIntegralClosure K F
  have hsub : (integralClosure 𝒪[F] E).toSubring = (integralClosure 𝒪[K] E).toSubring :=
    SetLike.ext fun z => by
      rw [Subalgebra.mem_toSubring, Subalgebra.mem_toSubring]
      exact RamificationNumberRestrictScalars.mem_integralClosure_base_iff K E F z
  let η : integralClosure 𝒪[F] E ≃+* integralClosure 𝒪[K] E := RingEquiv.subringCongr hsub
  have hsq : ∀ z : integralClosure 𝒪[K] F,
      η (algebraMap 𝒪[F] (integralClosure 𝒪[F] E) (ε z)) =
        AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] F E) z := by
    intro z
    refine Subtype.ext ?_
    calc ((η (algebraMap 𝒪[F] (integralClosure 𝒪[F] E) (ε z)) :
            integralClosure 𝒪[K] E) : E)
        = algebraMap 𝒪[F] E (ε z) := rfl
      _ = algebraMap F E (algebraMap 𝒪[F] F (ε z)) :=
          IsScalarTower.algebraMap_apply 𝒪[F] F E (ε z)
      _ = algebraMap F E (algebraMap (integralClosure 𝒪[K] F) F z) :=
          congrArg (algebraMap F E)
            (IsIntegralClosure.algebraMap_equiv 𝒪[K] (integralClosure 𝒪[K] F) F 𝒪[F] z)
      _ = ((AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] F E) z :
          integralClosure 𝒪[K] E) : E) := rfl
  have hcomp : ((η.symm : integralClosure 𝒪[K] E →+* integralClosure 𝒪[F] E).comp
        ((AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] F E) :
          integralClosure 𝒪[K] F →+* integralClosure 𝒪[K] E))).comp
        (ε.symm : 𝒪[F] →+* integralClosure 𝒪[K] F) =
      algebraMap 𝒪[F] (integralClosure 𝒪[F] E) := by
    refine RingHom.ext fun w => ?_
    have h := hsq (ε.symm w)
    rw [RingEquiv.apply_symm_apply] at h
    calc η.symm (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] F E) (ε.symm w))
        = η.symm (η (algebraMap 𝒪[F] (integralClosure 𝒪[F] E) w)) := by rw [h]
      _ = algebraMap 𝒪[F] (integralClosure 𝒪[F] E) w := RingEquiv.symm_apply_apply _ _
  -- the ideal identity in the `𝒪[F]`-model
  have hFmodel : Ideal.map (algebraMap 𝒪[F] (integralClosure 𝒪[F] E)) 𝓂[F] =
      IsLocalRing.maximalIdeal (integralClosure 𝒪[F] E) ^
        Nat.card (lowerRamificationGroup F E 0) := by
    rw [← hcomp, ← Ideal.map_map, ← Ideal.map_map,
      MapMaximalIdealEqPowCardInertia.map_maximalIdeal_ringEquiv ε.symm, h1, Ideal.map_pow,
      MapMaximalIdealEqPowCardInertia.map_maximalIdeal_ringEquiv η.symm]
  have he := MapMaximalIdealEqPowCardInertia.ramificationIdx'_eq_of_map_eq_pow hFmodel
  -- the fundamental identity over the `𝒪[F]`-model
  haveI : Module.Finite 𝒪[F] (integralClosure 𝒪[F] E) :=
    IsIntegralClosure.finite 𝒪[F] F E (integralClosure 𝒪[F] E)
  haveI : IsFractionRing (integralClosure 𝒪[F] E) E :=
    integralClosure.isFractionRing_of_finite_extension F E
  have hef : Ideal.ramificationIdx' 𝓂[F]
        (IsLocalRing.maximalIdeal (integralClosure 𝒪[F] E)) *
      Ideal.inertiaDeg' 𝓂[F]
        (IsLocalRing.maximalIdeal (integralClosure 𝒪[F] E)) =
      Module.finrank F E :=
    Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing
      (R := 𝒪[F]) (S := integralClosure 𝒪[F] E) (K := F) (L := E)
      (IsDiscreteValuationRing.not_a_field 𝒪[F])
  -- the inertia degree is the residue-field degree
  let e2a : integralClosure 𝒪[F] E ≃ₐ[𝒪[F]] 𝒪[E] :=
    AlgEquiv.ofRingEquiv (f := integerEquivIntegralClosure F E) fun c => by
      rw [← integerEquivIntegralClosure_symm_algebraMap F E c, RingEquiv.apply_symm_apply]
  have hcm : Ideal.comap e2a (𝓂[E] : Ideal 𝒪[E]) =
      IsLocalRing.maximalIdeal (integralClosure 𝒪[F] E) :=
    IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ e2a.surjective)
  have hf : Ideal.inertiaDeg' 𝓂[F]
      (IsLocalRing.maximalIdeal (integralClosure 𝒪[F] E)) =
      Module.finrank 𝓀[F] 𝓀[E] := by
    letI : TopologicalSpace E := ValuativeRel.topologicalSpace E
    haveI : IsValuativeTopology E := inferInstance
    haveI : IsMixedCharLocalField E := finiteExtension_isMixedCharLocalField F E
    rw [← hcm, Ideal.inertiaDeg'_comap_eq 𝓂[F] e2a 𝓂[E],
      Ideal.inertiaDeg'_eq_inertiaDeg 𝓂[F] 𝓂[E]]
    exact inertiaDeg_eq_finrank_residueField F E
  rw [he, hf] at hef
  rw [← hef]
  exact Nat.mul_comm _ _

end

end Atlas.Knowledge
