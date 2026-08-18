import Mathlib
import Atlas.Knowledge.IntegerIsIntegralClosure
import Atlas.Knowledge.IntegralClosureDVR
import Atlas.Knowledge.LowerRamificationGroup
import Atlas.Knowledge.RamificationNumberRestrictScalars

/-!
# ramification index as inertia order

For an intermediate valued field `E` of a finite extension `L` of a mixed-characteristic local
field `K`, with `L` Galois over `E`, the ramification index of `L` over `E` is the order of the
zeroth ramification group: the ideal identity of `Atlas.Knowledge.AddValMapIntegralClosure`
holds at the exponent `Nat.card (lowerRamificationGroup E L 0)`. This is the source's
identification of `G₀` with the inertia subgroup, read together with the inertia subgroup
having order the ramification index.

## Main statements

* `map_maximalIdeal_eq_pow_card_inertia` — the maximal ideal of the closure of `𝒪[K]` in `E`
  generates the power of the maximal ideal of the closure in `L` whose exponent is
  `Nat.card (lowerRamificationGroup E L 0)`.

## Implementation notes

The classical fact is run through Mathlib's inertia machinery
`Ideal.card_inertia_eq_ramificationIdxIn` over the pair `𝒪[E]` and `integralClosure 𝒪[E] L`,
not over the `𝒪[K]`-carriers of the statement: with `L ≃ₐ[E] L` acting through
`galRestrict 𝒪[E] E L`, Mathlib's `Ideal.inertia` at the maximal ideal is definitionally the
zeroth `Atlas.Knowledge.lowerRamificationGroup`—same action, and the Jacobson radical it is
written in is the maximal ideal—so the group side needs no transport at all. The price is paid
on the ring side, in two isomorphisms with one direction of travel each:
`IsIntegralClosure.equiv` carries `integralClosure 𝒪[K] E` onto `𝒪[E]` through
`Atlas.Knowledge.IntegerIsIntegralClosure`, and `RingEquiv.subringCongr` on the closure
equality of `Atlas.Knowledge.RamificationNumberRestrictScalars` carries
`integralClosure 𝒪[E] L` onto `integralClosure 𝒪[K] L`. The discrete-valuation structure
travels across the first *to* `𝒪[E]` and across the second *from* the `𝒪[K]`-closure, so no
local-field structure is ever placed on `E`: the finiteness of `𝓀[E]` that makes the residue
field perfect (`PerfectField.ofFinite`) descends along the finite `𝒪[K] → 𝒪[E]`, and `E` has
characteristic zero through `K`, which is what makes `L` separable over `E`. The exponent chain
crosses Mathlib's two ramification indices—the module-length `Ideal.ramificationIdx` the
machinery produces and the sSup-form `Ideal.ramificationIdx'`, the primed name being the
current one after the 2026-07-01 renaming—and is pinned against the ideal identity by
`Ideal.ramificationIdx'_spec`, whose strict inequality is the strict decrease of the powers of
the maximal ideal of a discrete valuation ring, read off
`IsDiscreteValuationRing.coheight_pow_maximalIdeal` exactly as in
`Atlas.Knowledge.AddValMapIntegralClosure`. At the end the identity derived over `𝒪[E]` is
pushed across the commuting square of the two isomorphisms onto the `𝒪[K]`-carriers, where it
is the statement. The hypothesis `[FiniteDimensional K E]` is carried explicitly for the reason
recorded in `Atlas.Knowledge.AddValMapIntegralClosure`, and `[IsGalois E L]` is taken directly
rather than derived from `[IsGalois K L]`, which keeps the hypotheses minimal. The scaffolding
carries the namespace as a name prefix instead of a `namespace` block so the shared `variable`
line serves the principal statement too.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]
variable (E : Type*) [Field E] [ValuativeRel E] [Algebra K E] [Algebra E L]
  [IsScalarTower K E L] [ValuativeExtension K E] [Algebra.IsAlgebraic E L]

/-- A discrete valuation ring transports along a ring isomorphism: principality and locality
push forward, and the maximal ideal upstairs is nonzero because its contraction is the nonzero
maximal ideal downstairs. -/
theorem MapMaximalIdealEqPowCardInertia.isDiscreteValuationRing_of_ringEquiv
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S]
    [IsDomain S] (e : R ≃+* S) : IsDiscreteValuationRing S := by
  haveI : IsPrincipalIdealRing S := IsPrincipalIdealRing.of_surjective (e : R →+* S) e.surjective
  haveI : IsLocalRing S := IsLocalRing.of_surjective' (e : R →+* S) e.surjective
  refine ⟨fun hbot => IsDiscreteValuationRing.not_a_field R ?_⟩
  have hmax : IsLocalRing.maximalIdeal R =
      Ideal.comap (e : R →+* S) (IsLocalRing.maximalIdeal S) :=
    (IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ e.surjective)).symm
  rw [hmax, hbot]
  exact Ideal.comap_bot_of_injective _ e.injective

/-- A ring isomorphism of local rings carries the maximal ideal onto the maximal ideal. -/
theorem MapMaximalIdealEqPowCardInertia.map_maximalIdeal_ringEquiv
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (e : R ≃+* S) :
    Ideal.map (e : R →+* S) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal S := by
  rw [Ideal.map_comap_of_equiv]
  exact IsLocalRing.eq_maximalIdeal
    (Ideal.comap_isMaximal_of_surjective _ e.symm.surjective)

/-- Between discrete valuation rings with injective structure map, the maximal ideal downstairs
generates a power of the maximal ideal upstairs—the existence half of
`Atlas.Knowledge.exists_map_maximalIdeal_eq_pow`, over an arbitrary base pair. -/
theorem MapMaximalIdealEqPowCardInertia.exists_map_maximalIdeal_eq_pow
    {R S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S]
    [IsDomain S] [IsDiscreteValuationRing S] [Algebra R S]
    (hinj : Function.Injective (algebraMap R S)) :
    ∃ n, Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) =
      IsLocalRing.maximalIdeal S ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S
  have hbot : Ideal.map (algebraMap R S) (IsLocalRing.maximalIdeal R) ≠ ⊥ := fun h =>
    IsDiscreteValuationRing.not_a_field R ((Ideal.map_eq_bot_iff_of_injective hinj).mp h)
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hbot hϖ
  exact ⟨n, by rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩

/-- The sSup-form ramification index reads off the exponent of the ideal identity: distinct
powers of the maximal ideal of a discrete valuation ring are distinct, so the identity pins the
supremum. -/
theorem MapMaximalIdealEqPowCardInertia.ramificationIdx'_eq_of_map_eq_pow
    {R S : Type*} [CommRing R] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra R S] {p : Ideal R} {n : ℕ}
    (h : Ideal.map (algebraMap R S) p = IsLocalRing.maximalIdeal S ^ n) :
    Ideal.ramificationIdx' p (IsLocalRing.maximalIdeal S) = n := by
  refine Ideal.ramificationIdx'_spec (le_of_eq h) fun hle => ?_
  rw [h] at hle
  have heq : IsLocalRing.maximalIdeal S ^ n = IsLocalRing.maximalIdeal S ^ (n + 1) :=
    le_antisymm hle (Ideal.pow_le_pow_right n.le_succ)
  have hco := congrArg Order.coheight heq
  rw [IsDiscreteValuationRing.coheight_pow_maximalIdeal,
    IsDiscreteValuationRing.coheight_pow_maximalIdeal, Nat.cast_inj] at hco
  omega

set_option synthInstance.maxHeartbeats 80000 in
-- The instance searches of the AKLB package over `𝒪[E]`—flatness through Dedekind, the
-- Galois-group package—overrun the default synthesis budget.
set_option maxHeartbeats 800000 in
-- The whole package is assembled inside this one proof, and its elaboration overruns the
-- default budget.
/-- The ramification index of `L` over `E` is the order of the zeroth ramification group: the
ideal identity of `Atlas.Knowledge.AddValMapIntegralClosure` holds at the exponent
`Nat.card (lowerRamificationGroup E L 0)`—the source's inertia subgroup `G₀` of order the
ramification index
([Serre 1979, Chap. I, §7, Prop. 21 and Cor., p.22 and Chap. IV, §1, Prop. 1,
p.62][Serre1979]). -/
theorem map_maximalIdeal_eq_pow_card_inertia [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K E] [FiniteDimensional K L] [IsGalois E L] :
    Ideal.map (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L))
        (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E)) =
      IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L) ^
        Nat.card (lowerRamificationGroup E L 0) := by
  classical
  haveI : FiniteDimensional E L := Module.Finite.right K E L
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  -- the two carrier identifications
  let ε : integralClosure 𝒪[K] E ≃+* 𝒪[E] :=
    (IsIntegralClosure.equiv 𝒪[K] (integralClosure 𝒪[K] E) E 𝒪[E]).toRingEquiv
  have hsub : (integralClosure 𝒪[E] L).toSubring = (integralClosure 𝒪[K] L).toSubring :=
    SetLike.ext fun z => by
      rw [Subalgebra.mem_toSubring, Subalgebra.mem_toSubring]
      exact RamificationNumberRestrictScalars.mem_integralClosure_base_iff K L E z
  let η : integralClosure 𝒪[E] L ≃+* integralClosure 𝒪[K] L := RingEquiv.subringCongr hsub
  -- the transported discrete-valuation structure
  haveI : IsDiscreteValuationRing 𝒪[E] :=
    MapMaximalIdealEqPowCardInertia.isDiscreteValuationRing_of_ringEquiv ε
  haveI : IsDiscreteValuationRing (integralClosure 𝒪[E] L) :=
    MapMaximalIdealEqPowCardInertia.isDiscreteValuationRing_of_ringEquiv η.symm
  -- the AKLB package over `𝒪[E]`
  haveI : FaithfulSMul 𝒪[E] (integralClosure 𝒪[E] L) :=
    (faithfulSMul_iff_algebraMap_injective 𝒪[E] (integralClosure 𝒪[E] L)).mpr fun a b hab => by
      have h : algebraMap 𝒪[E] L a = algebraMap 𝒪[E] L b :=
        congrArg (algebraMap (integralClosure 𝒪[E] L) L) hab
      rw [IsScalarTower.algebraMap_apply 𝒪[E] E L, IsScalarTower.algebraMap_apply 𝒪[E] E L] at h
      exact Subtype.ext ((algebraMap E L).injective h)
  haveI : Algebra.IsSeparable E L := inferInstance
  haveI : IsDedekindDomain 𝒪[E] := inferInstance
  haveI : Module.Finite 𝒪[E] (integralClosure 𝒪[E] L) :=
    IsIntegralClosure.finite 𝒪[E] E L (integralClosure 𝒪[E] L)
  haveI : IsFractionRing (integralClosure 𝒪[E] L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension 𝒪[E] E L (integralClosure 𝒪[E] L)
  haveI : Module.IsTorsionFree 𝒪[E] (integralClosure 𝒪[E] L) := inferInstance
  haveI : Module.Flat 𝒪[E] (integralClosure 𝒪[E] L) := inferInstance
  haveI : IsDedekindDomain (integralClosure 𝒪[E] L) := inferInstance
  haveI : Finite (L ≃ₐ[E] L) := inferInstance
  letI : MulSemiringAction (L ≃ₐ[E] L) (integralClosure 𝒪[E] L) :=
    IsIntegralClosure.MulSemiringAction 𝒪[E] E L (integralClosure 𝒪[E] L)
  haveI : IsGaloisGroup (L ≃ₐ[E] L) 𝒪[E] (integralClosure 𝒪[E] L) :=
    IsGaloisGroup.of_isFractionRing _ _ _ E L
  -- the maximal ideal upstairs lies over the maximal ideal of `𝒪[E]`
  haveI : (IsLocalRing.maximalIdeal (integralClosure 𝒪[E] L)).LiesOver
      (IsLocalRing.maximalIdeal 𝒪[E]) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (IsLocalRing.maximalIdeal (integralClosure 𝒪[E] L)))).symm⟩
  -- the residue field of `𝒪[E]` is finite, hence perfect
  haveI : FaithfulSMul 𝒪[K] 𝒪[E] :=
    (faithfulSMul_iff_algebraMap_injective 𝒪[K] 𝒪[E]).mpr fun a b hab => by
      have h := congrArg (algebraMap 𝒪[E] E) hab
      rw [← IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[E] E,
        ← IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[E] E, IsScalarTower.algebraMap_apply 𝒪[K] K E,
        IsScalarTower.algebraMap_apply 𝒪[K] K E] at h
      exact IsFractionRing.injective 𝒪[K] K ((algebraMap K E).injective h)
  haveI : Module.Finite 𝒪[K] 𝒪[E] := IsIntegralClosure.finite 𝒪[K] K E 𝒪[E]
  haveI hfinE : Finite 𝓀[E] :=
    IsLocalRing.ResidueField.finite_of_finite (R := 𝒪[K]) (inferInstance : Finite 𝓀[K])
  haveI : Finite (𝒪[E] ⧸ IsLocalRing.maximalIdeal 𝒪[E]) := hfinE
  haveI : PerfectField (IsLocalRing.maximalIdeal 𝒪[E]).ResidueField := PerfectField.ofFinite
  -- the ideal identity over `𝒪[E]`, and its exponent as the inertia order
  obtain ⟨n, hn⟩ := MapMaximalIdealEqPowCardInertia.exists_map_maximalIdeal_eq_pow
    (R := 𝒪[E]) (S := integralClosure 𝒪[E] L)
    (FaithfulSMul.algebraMap_injective 𝒪[E] (integralClosure 𝒪[E] L))
  have hcard : Nat.card
      ((IsLocalRing.maximalIdeal (integralClosure 𝒪[E] L)).inertia (L ≃ₐ[E] L)) = n :=
    (Ideal.card_inertia_eq_ramificationIdxIn (IsLocalRing.maximalIdeal 𝒪[E])
        (IsLocalRing.maximalIdeal (integralClosure 𝒪[E] L))).trans
      ((Ideal.ramificationIdxIn_eq_ramificationIdx (IsLocalRing.maximalIdeal 𝒪[E])
          (IsLocalRing.maximalIdeal (integralClosure 𝒪[E] L)) (L ≃ₐ[E] L)).trans
        ((Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal 𝒪[E])
            (IsLocalRing.maximalIdeal (integralClosure 𝒪[E] L))
            (IsDiscreteValuationRing.not_a_field 𝒪[E])).symm.trans
          (MapMaximalIdealEqPowCardInertia.ramificationIdx'_eq_of_map_eq_pow hn)))
  -- the zeroth ramification group is the inertia group, literally
  have hjac : Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[E] L)) =
      IsLocalRing.maximalIdeal (integralClosure 𝒪[E] L) :=
    IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top
  have hgroup : lowerRamificationGroup E L 0 =
      (IsLocalRing.maximalIdeal (integralClosure 𝒪[E] L)).inertia (L ≃ₐ[E] L) := by
    ext s
    rw [mem_lowerRamificationGroup_iff]
    change (∀ x : integralClosure 𝒪[E] L,
        galRestrict 𝒪[E] E L (integralClosure 𝒪[E] L) s x - x ∈
          Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[E] L)) ^ 1) ↔
      ∀ x : integralClosure 𝒪[E] L,
        galRestrict 𝒪[E] E L (integralClosure 𝒪[E] L) s x - x ∈
          IsLocalRing.maximalIdeal (integralClosure 𝒪[E] L)
    rw [pow_one, hjac]
  have hncard : Nat.card (lowerRamificationGroup E L 0) = n := by
    rw [hgroup]
    exact hcard
  -- the commuting square, elementwise through the coercions into `L`
  have hsq : ∀ z : integralClosure 𝒪[K] E,
      η (algebraMap 𝒪[E] (integralClosure 𝒪[E] L) (ε z)) =
        AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) z := by
    intro z
    refine Subtype.ext ?_
    calc ((η (algebraMap 𝒪[E] (integralClosure 𝒪[E] L) (ε z)) : integralClosure 𝒪[K] L) : L)
        = algebraMap 𝒪[E] L (ε z) := rfl
      _ = algebraMap E L (algebraMap 𝒪[E] E (ε z)) :=
          IsScalarTower.algebraMap_apply 𝒪[E] E L (ε z)
      _ = algebraMap E L (algebraMap (integralClosure 𝒪[K] E) E z) :=
          congrArg (algebraMap E L)
            (IsIntegralClosure.algebraMap_equiv 𝒪[K] (integralClosure 𝒪[K] E) E 𝒪[E] z)
      _ = ((AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) z :
          integralClosure 𝒪[K] L) : L) := rfl
  -- transport the ideal identity onto the `𝒪[K]`-carriers
  have hcomp : ((η : integralClosure 𝒪[E] L →+* integralClosure 𝒪[K] L).comp
        (algebraMap 𝒪[E] (integralClosure 𝒪[E] L))).comp
        (ε : integralClosure 𝒪[K] E →+* 𝒪[E]) =
      (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) :
        integralClosure 𝒪[K] E →+* integralClosure 𝒪[K] L) :=
    RingHom.ext hsq
  have hmapcoe : Ideal.map (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L))
      (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E)) =
      Ideal.map ((AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) :
        integralClosure 𝒪[K] E →+* integralClosure 𝒪[K] L))
      (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E)) := rfl
  rw [hncard, hmapcoe, ← hcomp, ← Ideal.map_map, ← Ideal.map_map,
    MapMaximalIdealEqPowCardInertia.map_maximalIdeal_ringEquiv ε, hn, Ideal.map_pow,
    MapMaximalIdealEqPowCardInertia.map_maximalIdeal_ringEquiv η]

end Atlas.Knowledge
