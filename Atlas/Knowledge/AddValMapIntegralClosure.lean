import Mathlib
import Atlas.Knowledge.IntegralClosureDVR

/-!
# order under the integral-closure pushforward

For an intermediate field `E` of a finite extension `L` of a mixed-characteristic local field
`K`, the inclusion of `E` in `L` restricts to the pushforward `AlgHom.mapIntegralClosure` between
the integral closures of `𝒪[K]`, and pushing an element through it multiplies its order by the
ramification index—the source's statement that the valuation upstairs restricts on the subfield
to the ramification index times the valuation there.

## Main statements

* `exists_map_maximalIdeal_eq_pow` — the maximal ideal of the closure in `E` generates a nonzero
  power of the maximal ideal of the closure in `L`: the ideal identity whose exponent is the
  ramification index.
* `map_maximalIdeal_eq_pow_unique` — that exponent is unique.
* `addVal_mapIntegralClosure` — with `e` that exponent, the order of the image of `z` is `e`
  times the order of `z`.

## Implementation notes

Everything is over the base `𝒪[K]`: the two rings are the integral closures of `𝒪[K]` in `E` and
in `L`, and no valuative structure is placed on `E`—`Atlas.Knowledge.IntegerIsIntegralClosure`
is what relates the closure in `E` to the intrinsic `𝒪[E]` when an item needs it. The exponent
is carried by the ideal identity itself rather than by Mathlib's `Ideal.ramificationIdx`: that
definition and its `Ideal.ramificationIdx'` predecessor are both stated along an `algebraMap`,
so using either would force an `Algebra` instance between the two closures into the statements,
and that instance is the pushforward read as an algebra—global, it invites diamonds, so it stays
a `letI` inside one scaffolding proof. The principal statement takes the ideal identity as a
hypothesis, the existence statement produces it, and the uniqueness statement pins any two
exponents equal, which is the ∃-plus-uniqueness form a consumer instantiates. The hypothesis
`[FiniteDimensional K E]` follows from `[FiniteDimensional K L]` by `FiniteDimensional.left`,
but instance synthesis inside a statement cannot run that derivation, and the statements need
the discrete-valuation-ring instance on the closure in `E`, so it is carried explicitly. The
scaffolding carries the namespace as a name prefix instead of a `namespace` block so the shared
`variable` line serves the public statements too.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
  [Algebra.IsAlgebraic K E]

omit [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K E] in
/-- The pushforward `AlgHom.mapIntegralClosure` of the inclusion of `E` in `L` is injective:
through the closures' coercions it acts as the injective `algebraMap E L`. -/
theorem AddValMapIntegralClosure.mapIntegralClosure_injective :
    Function.Injective (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L)) :=
  fun _ _ h => Subtype.ext ((algebraMap E L).injective (congrArg Subtype.val h))

/-- The maximal ideal of the closure in `L` contracts to the maximal ideal of the closure in
`E`: integrality over `𝒪[K]` makes the extension of closures integral, so the contraction of
the maximal ideal is maximal, and the closure in `E` is local. -/
theorem AddValMapIntegralClosure.comap_maximalIdeal [TopologicalSpace K]
    [IsMixedCharLocalField K] [FiniteDimensional K E] [FiniteDimensional K L] :
    Ideal.comap (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L))
        (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L)) =
      IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E) := by
  letI : Algebra (integralClosure 𝒪[K] E) (integralClosure 𝒪[K] L) :=
    (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L)).toRingHom.toAlgebra
  haveI : IsScalarTower 𝒪[K] (integralClosure 𝒪[K] E) (integralClosure 𝒪[K] L) :=
    IsScalarTower.of_algebraMap_eq'
      (AlgHom.comp_algebraMap (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L))).symm
  haveI : Algebra.IsIntegral (integralClosure 𝒪[K] E) (integralClosure 𝒪[K] L) :=
    ⟨fun x => IsIntegral.tower_top (integralClosure.isIntegral x)⟩
  exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)

/-- There is a nonzero exponent `e` with the image of the maximal ideal under the pushforward
generating the `e`-th power of the maximal ideal upstairs: the single-prime case of the
source's decomposition of an extended prime into the primes above it, whose exponent is the
ramification index ([Serre 1979, Chap. I, §4, p.14][Serre1979]). -/
theorem exists_map_maximalIdeal_eq_pow [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K E] [FiniteDimensional K L] :
    ∃ e ≠ 0, Ideal.map (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L))
        (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E)) =
      IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L) ^ e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure 𝒪[K] L)
  have hbot : Ideal.map (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L))
      (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E)) ≠ ⊥ := fun h =>
    IsDiscreteValuationRing.not_a_field (integralClosure 𝒪[K] E)
      ((Ideal.map_eq_bot_iff_of_injective
        (AddValMapIntegralClosure.mapIntegralClosure_injective K L E)).mp h)
  obtain ⟨e, he⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hbot hϖ
  refine ⟨e, fun h0 => ?_, by rw [he, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩
  have hle := Ideal.map_le_iff_le_comap.mpr
    (AddValMapIntegralClosure.comap_maximalIdeal K L E).ge
  rw [he, h0, pow_zero, Ideal.span_singleton_one] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)

/-- The exponent of `Atlas.Knowledge.exists_map_maximalIdeal_eq_pow` is unique: distinct powers
of the maximal ideal of a discrete valuation ring are distinct ideals
([Serre 1979, Chap. I, §4, p.14][Serre1979]). -/
theorem map_maximalIdeal_eq_pow_unique [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K E] [FiniteDimensional K L] {e e' : ℕ}
    (he : Ideal.map (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L))
        (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E)) =
      IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L) ^ e)
    (he' : Ideal.map (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L))
        (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E)) =
      IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L) ^ e') : e = e' := by
  have h := congrArg Order.coheight (he.symm.trans he')
  rwa [IsDiscreteValuationRing.coheight_pow_maximalIdeal,
    IsDiscreteValuationRing.coheight_pow_maximalIdeal, Nat.cast_inj] at h

/-- Pushing an integral element of `E` into the integral closure in `L` multiplies its order by
the ramification index: with `e` the exponent of the ideal identity, taken here as a
hypothesis, the order of the image of `z` is `e` times the order of `z`—the source's statement
that the valuation upstairs restricts on the subfield to the ramification index times the
valuation there, in the complete setting of the source's fourth chapter
([Serre 1979, Chap. I, §4, p.15 and Chap. IV, p.61][Serre1979]). -/
theorem addVal_mapIntegralClosure [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K E] [FiniteDimensional K L] {e : ℕ}
    (he : Ideal.map (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L))
        (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E)) =
      IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L) ^ e)
    (z : integralClosure 𝒪[K] E) :
    IsDiscreteValuationRing.addVal (integralClosure 𝒪[K] L)
        (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) z) =
      e • IsDiscreteValuationRing.addVal (integralClosure 𝒪[K] E) z := by
  have he0 : e ≠ 0 := by
    intro h0
    have hle := Ideal.map_le_iff_le_comap.mpr
      (AddValMapIntegralClosure.comap_maximalIdeal K L E).ge
    rw [he, h0, pow_zero, Ideal.one_eq_top] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp hle)
  obtain ⟨ϖE, hϖE⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure 𝒪[K] E)
  obtain ⟨ϖL, hϖL⟩ := IsDiscreteValuationRing.exists_irreducible (integralClosure 𝒪[K] L)
  -- the ideal identity read on generators: the image of a uniformizer has order `e`
  have hassoc : Associated (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) ϖE)
      (ϖL ^ e) := by
    rw [← Ideal.span_singleton_eq_span_singleton, ← Set.image_singleton, ← Ideal.map_span,
      ← hϖE.maximalIdeal_eq, ← Ideal.span_singleton_pow, ← hϖL.maximalIdeal_eq]
    exact he
  have hϖEval : IsDiscreteValuationRing.addVal (integralClosure 𝒪[K] L)
      (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) ϖE) = e := by
    rw [(IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr hassoc, hϖL.addVal_pow]
  rcases eq_or_ne z 0 with rfl | hz
  · rw [map_zero, IsDiscreteValuationRing.addVal_zero, IsDiscreteValuationRing.addVal_zero,
      nsmul_eq_mul, ENat.mul_top (Nat.cast_ne_zero.mpr he0)]
  · obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz hϖE
    rw [map_mul, map_pow, IsDiscreteValuationRing.addVal_mul,
      IsDiscreteValuationRing.addVal_pow, hϖEval,
      IsDiscreteValuationRing.addVal_eq_zero_iff.mpr
        (u.isUnit.map (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L))),
      zero_add, IsDiscreteValuationRing.addVal_def' u hϖE m,
      nsmul_eq_mul, nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_mul, Nat.mul_comm]

end Atlas.Knowledge
