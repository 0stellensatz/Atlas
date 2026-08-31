import Mathlib
import Atlas.Knowledge.IntegralClosureDVR

/-!
# ring of integers as integral closure

The ring of integers of a finite extension `E` of a mixed-characteristic local field `K` is the
integral closure of `𝒪[K]` in `E`: an element of `E` is a valuative integer exactly when it is
integral over `𝒪[K]`. This identifies the abstract closure `Atlas.Knowledge.IntegralClosureDVR`
speaks about—Serre's `A_L`—with the intrinsic ring `𝒪[E]` the rest of the knowledge layer is
written in.

## Main statements

* `mem_integer_iff_isIntegral` — membership in `𝒪[E]` is integrality over `𝒪[K]`.
* `integerIsIntegralClosure` — `𝒪[E]` is the integral closure of `𝒪[K]` in `E`.
* `integer_isIntegral` — the integer tower `𝒪[K] → 𝒪[E]` is integral.
* `integerEquivIntegralClosure` — the identification as a ring isomorphism, with its
  coercion identity and structure-map square.

## Implementation notes

The hard inclusion is an overring collapse inside `E`. The integral closure of `𝒪[K]` in `E` is
a discrete valuation ring by `Atlas.Knowledge.integralClosureDVR`, and the spectral-norm
unit-ball description makes it a valuation subring of `E`: an element outside the closure has
spectral norm above one, so its inverse falls strictly inside. The inclusion of that subring in
`𝒪[E]` induces a prime ideal of the closure, and a discrete valuation ring has dimension one, so
the prime is either maximal—pinning the two rings equal—or zero, which would make the valuation
of `E` trivial against `IntegerIsIntegralClosure.isNontrivial`. No rank-one hypothesis is placed
on `E`: nontriviality ascends from `K` through the strictly monotone map of value groups, and
the normed structure on `K` is rebuilt inside the proof exactly as in
`Atlas.Knowledge.IntegralClosureDVR`, so the auxiliary uniformity never escapes. The bridge
instance `IntegerIsIntegralClosure.hasExtension` and the nontriviality ascent
`IntegerIsIntegralClosure.isNontrivial` are generic—no local-field hypotheses—and reusable
wherever a `ValuativeExtension` lives; they stay out of the index deliberately, as scaffolding
of this item rather than items of their own. The scaffolding carries the namespace as a name
prefix instead of a `namespace` block so the shared `variable` line serves the public
statements too. In the source the identification of the valuation ring with the integral
closure sits at proof level: Prop. 3 constructs the closure as the discrete valuation ring of
the extension, and Cor. 2's uniqueness is what pins any compatible valuation to it.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (E : Type*) [Field E] [ValuativeRel E]
  [Algebra K E] [ValuativeExtension K E]

/-- The valuation of `E` extends the valuation of `K`: under `ValuativeExtension K E` the
pullback of `valuation E` along `algebraMap K E` is compatible with the valuative relation of
`K`, and any two compatible valuations are equivalent. This glues Mathlib's two unrelated
extension classes together, and its downstream instances provide `Algebra 𝒪[K] 𝒪[E]` and
`IsScalarTower 𝒪[K] 𝒪[E] E`. -/
instance IntegerIsIntegralClosure.hasExtension : (valuation K).HasExtension (valuation E) :=
  ⟨ValuativeRel.isEquiv _ _⟩

/-- Nontriviality of the valuative relation ascends along an extension of valued fields: a
witness in the value group of `K` pushes forward through the strictly monotone—hence
injective—`ValuativeExtension.mapValueGroupWithZero`, staying away from `0` and `1`. -/
theorem IntegerIsIntegralClosure.isNontrivial [ValuativeRel.IsNontrivial K] :
    ValuativeRel.IsNontrivial E := by
  obtain ⟨γ, h0, h1⟩ := ValuativeRel.IsNontrivial.condition (R := K)
  refine ⟨ValuativeExtension.mapValueGroupWithZero K E γ, fun h => h0 ?_, fun h => h1 ?_⟩
  · exact ValuativeExtension.mapValueGroupWithZero_strictMono.injective (by rw [h, map_zero])
  · exact ValuativeExtension.mapValueGroupWithZero_strictMono.injective (by rw [h, map_one])

/-- An element of a finite extension `E` of a mixed-characteristic local field `K` lies in
`𝒪[E]` if and only if it is integral over `𝒪[K]`
([Serre 1979, Chap. II, §2, Prop. 3 and Cor. 2, pp.28–29][Serre1979]). -/
theorem mem_integer_iff_isIntegral [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K E] {x : E} : x ∈ 𝒪[E] ↔ IsIntegral 𝒪[K] x := by
  haveI : Algebra.IsAlgebraic K E := Algebra.IsAlgebraic.of_finite K E
  haveI hDVR : IsDiscreteValuationRing (integralClosure 𝒪[K] E) := integralClosureDVR K E
  -- Integral elements are integers of `E`: integrality descends the tower to `𝒪[E]`, whose
  -- valuation ring is integrally closed in `E`.
  have hTsub : ∀ z ∈ integralClosure 𝒪[K] E, z ∈ 𝒪[E] := fun z hz =>
    (Valuation.integer.integers (valuation E)).mem_of_integral
      (IsIntegral.tower_top ((mem_integralClosure_iff _ _).mp hz))
  refine ⟨fun hx => ?_, fun hx => hTsub x ((mem_integralClosure_iff _ _).mpr hx)⟩
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : IsUltrametricDist K := inferInstance
  haveI : CompleteSpace K := inferInstance
  have hc : ∀ x : K, ‖x‖ ≤ 1 ↔ valuation K x ≤ 1 := fun x => Valued.toNormedField.norm_le_one_iff
  -- The closure is a valuation subring: an element of spectral norm above one has its inverse
  -- strictly inside the unit ball.
  have hmeminv : ∀ z : E, z ∈ (integralClosure 𝒪[K] E).toSubring ∨
      z⁻¹ ∈ (integralClosure 𝒪[K] E).toSubring := by
    intro z
    rcases le_or_gt (spectralNorm K E z) 1 with hz | hz
    · exact Or.inl (Subalgebra.mem_toSubring.mpr
        ((IntegralClosureDVR.mem_integralClosure_iff_spectralNorm_le_one hc).mpr hz))
    · refine Or.inr (Subalgebra.mem_toSubring.mpr
        ((IntegralClosureDVR.mem_integralClosure_iff_spectralNorm_le_one hc).mpr ?_))
      -- the `z = 0` branch is vacuous under `hz` (`spectralNorm K E 0 = 0`); splitting is
      -- cheaper than deriving `z ≠ 0` from it
      rcases eq_or_ne z 0 with rfl | hz0
      · simp [spectralNorm_zero]
      · have hmul : spectralNorm K E (z * z⁻¹) =
            spectralNorm K E z * spectralNorm K E z⁻¹ := spectralAlgNorm_mul _ _
        rw [mul_inv_cancel₀ hz0, spectralNorm_one] at hmul
        rw [← inv_eq_of_mul_eq_one_right hmul.symm]
        exact inv_le_one_of_one_le₀ hz.le
  let R : ValuationSubring E :=
    ValuationSubring.ofSubring (integralClosure 𝒪[K] E).toSubring hmeminv
  have hRmem : ∀ z : E, z ∈ R ↔ z ∈ integralClosure 𝒪[K] E := fun z =>
    (ValuationSubring.mem_ofSubring _ hmeminv z).trans Subalgebra.mem_toSubring
  have hRS : R ≤ (valuation E).valuationSubring := fun z hz => hTsub z ((hRmem z).mp hz)
  haveI hRdvr : IsDiscreteValuationRing R :=
    inferInstanceAs (IsDiscreteValuationRing (integralClosure 𝒪[K] E))
  rcases eq_or_ne (ValuationSubring.idealOfLE R _ hRS) ⊥ with hP | hP
  · -- A zero prime would collapse the valuation ring of `E` to all of `E`, against
    -- nontriviality, which ascends from `K`.
    exfalso
    have h1 : R.ofPrime ⊥ ≤ R.ofPrime (ValuationSubring.idealOfLE R _ hRS) :=
      ValuationSubring.ofPrime_le_of_le R _ ⊥ hP.le
    rw [ValuationSubring.ofPrime_bot, ValuationSubring.ofPrime_idealOfLE R _ hRS] at h1
    haveI := IntegerIsIntegralClosure.isNontrivial K E
    obtain ⟨γ, hγ0, hγ1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := E)
    obtain ⟨z, hz⟩ := ValuativeRel.valuation_surjective (K := E) γ
    have h2 : valuation E z⁻¹ ≤ 1 := h1 (ValuationSubring.mem_top _)
    rw [map_inv₀, hz] at h2
    exact absurd h2 (not_le.mpr ((one_lt_inv₀ hγ0).mpr hγ1))
  · -- A nonzero prime of a one-dimensional ring is maximal, and the maximal ideal pins the
    -- overring back to the closure itself.
    haveI hPmax : (ValuationSubring.idealOfLE R _ hRS).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance hP
    have h1 : R.ofPrime (ValuationSubring.idealOfLE R _ hRS) ≤
        R.ofPrime (IsLocalRing.maximalIdeal R) :=
      ValuationSubring.ofPrime_le_of_le R _ _ (IsLocalRing.eq_maximalIdeal hPmax).ge
    rw [ValuationSubring.ofPrime_top, ValuationSubring.ofPrime_idealOfLE R _ hRS] at h1
    exact (mem_integralClosure_iff _ _).mp ((hRmem x).mp (h1 hx))

/-- The ring of integers of a finite extension of a mixed-characteristic local field is the
integral closure of the base ring of integers
([Serre 1979, Chap. II, §2, Prop. 3 and Cor. 2, pp.28–29][Serre1979]). -/
instance integerIsIntegralClosure [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K E] : IsIntegralClosure 𝒪[E] 𝒪[K] E where
  algebraMap_injective := Subtype.coe_injective
  isIntegral_iff {x} := ⟨fun hx => ⟨⟨x, (mem_integer_iff_isIntegral K E).mpr hx⟩, rfl⟩, by
    rintro ⟨y, rfl⟩
    exact (mem_integer_iff_isIntegral K E).mp y.2⟩

/-- The integer tower is integral: every element of `𝒪[E]` is integral over `𝒪[K]`
([Serre 1979, Chap. II, §2, Prop. 3 and Cor. 2, pp.28–29][Serre1979]). -/
instance integer_isIntegral [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K E] : Algebra.IsIntegral 𝒪[K] 𝒪[E] :=
  IsIntegralClosure.isIntegral_algebra 𝒪[K] E

/-- The identification of the extension's integers with the integral closure of the base
integers — `Atlas.Knowledge.integerIsIntegralClosure` read as a ring isomorphism, the
form the closure-carrier statements are transported along. -/
noncomputable def integerEquivIntegralClosure [TopologicalSpace K]
    [IsMixedCharLocalField K] [FiniteDimensional K E] :
    integralClosure 𝒪[K] E ≃+* 𝒪[E] :=
  (IsIntegralClosure.equiv 𝒪[K] (integralClosure 𝒪[K] E) E 𝒪[E]).toRingEquiv

/-- The identification acts as the identity through the field: the image of a closure
element has the same coercion. -/
theorem coe_integerEquivIntegralClosure [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K E] (z : integralClosure 𝒪[K] E) :
    ((integerEquivIntegralClosure K E z : 𝒪[E]) : E) =
      algebraMap (integralClosure 𝒪[K] E) E z :=
  IsIntegralClosure.algebraMap_equiv 𝒪[K] (integralClosure 𝒪[K] E) E 𝒪[E] z

/-- The commuting square: the closure's structure map is the integers' through the
identification. -/
theorem integerEquivIntegralClosure_symm_algebraMap [TopologicalSpace K]
    [IsMixedCharLocalField K] [FiniteDimensional K E] (c : 𝒪[K]) :
    (integerEquivIntegralClosure K E).symm (algebraMap 𝒪[K] 𝒪[E] c) =
      algebraMap 𝒪[K] (integralClosure 𝒪[K] E) c := by
  apply (integerEquivIntegralClosure K E).injective
  rw [RingEquiv.apply_symm_apply]
  apply Subtype.ext
  rw [coe_integerEquivIntegralClosure,
    ← IsScalarTower.algebraMap_apply 𝒪[K] (integralClosure 𝒪[K] E) E,
    IsScalarTower.algebraMap_apply 𝒪[K] 𝒪[E] E]
  rfl

end Atlas.Knowledge
