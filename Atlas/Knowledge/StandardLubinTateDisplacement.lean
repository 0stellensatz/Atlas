import Mathlib
import Atlas.Knowledge.IntegerValuation
import Atlas.Knowledge.LubinTateModule
import Atlas.Knowledge.StandardLubinTatePrimitiveValuation
import Atlas.Knowledge.StandardLubinTateTorsion

/-!
# standard Lubin–Tate displacement

How far a unit scalar moves a point of the formal module: `ν([u] x − x) = qʲ ν(x)` at a
level-`n + 1` primitive root, where `j ≤ n` is the depth of `u − 1`. Two power-series
factorizations carry the whole file: the formal group's right displacement `F − X₀` is
`X₁` times a series with constant coefficient one, and the scalar endomorphism `[a]` is
`X` times a series with constant coefficient `a` — so neither the displacement nor a
unit scalar changes a value, and the module law `[u] x = [u − 1] x +[e] x` hands the
displacement to the iterate valuations of
`Atlas.Knowledge.integerValuation_aeval_standardLubinTatePolynomialIterate`. This is
the conjugate-distance input of the root-product/Krasner comparison ahead: the orbit
of a primitive root sits at distances `qʲ ν(x)`, `j ≤ n`.

## Main statements

* `integerValuation_lubinTateAdd_sub_left` — `ν(x +[e] y − x) = ν(y)`; proved.
* `integerValuation_lubinTateSMul_isUnit` — unit scalars preserve the value; proved.
* `integerValuation_lubinTateSMul_sub_self` — `ν([u] x − x) = ν([u − 1] x)`; proved.
* `integerValuation_standardLubinTateSMul_sub_self` — the spectrum `qʲ ν(x)`; proved.

## Implementation notes

The factorizations are extracted by coefficients: `X₁ ∣ F − X₀` because substituting
`![X, 0]` collapses `F` to `X` — which is one application of
`Atlas.Knowledge.lubinTateScalar_add` at `1 + 0` — and the cofactor's constant
coefficient is read off the linear term. The cofactors are `Classical.choose` data and
stay private; the exports carry only values. Evaluation uses the same staged
uniformities as `Atlas.Knowledge.LubinTateModule` — the discrete base, the compact
integer ring upstairs — through `MvPowerSeries.eval₂Hom`, and the cofactor evaluations
land in `1 + 𝓂[E]` and `a + 𝓂[E]` by
`Atlas.Knowledge.eval₂_mem_maximalIdeal` on the constant-coefficient-zero differences.
The spectrum's depth hypothesis is the explicit factorization `u − 1 = πʲ w` with `w` a
unit — the DVR normal form — rather than a two-sided filtration membership; the consumer
converts once.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section Series

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)] {π : A}

/-- The formal group collapses to the identity in its first variable. -/
private theorem formalGroup_subst_X_zero (hπ : Irreducible π) (e : LubinTateSeries A π) :
    MvPowerSeries.subst
        (![(PowerSeries.X : MvPowerSeries Unit A), 0] : Fin 2 → MvPowerSeries Unit A)
        (lubinTateFormalGroupPowerSeries hπ e) =
      (PowerSeries.X : MvPowerSeries Unit A) := by
  have h := lubinTateScalar_add hπ e 1 0
  rw [lubinTateScalar_one, lubinTateScalar_zero, add_zero, lubinTateScalar_one] at h
  simpa using h

/-- Coefficient extraction along the substitution `![X, 0]`. -/
private theorem coeff_subst_X_zero' {R : Type*} [CommRing R]
    (f : MvPowerSeries (Fin 2) R) (d : Fin 2 →₀ ℕ) (hd : d 1 = 0) :
    PowerSeries.coeff (d 0)
        (MvPowerSeries.subst
          (![(PowerSeries.X : MvPowerSeries Unit R), 0] : Fin 2 → MvPowerSeries Unit R)
          f) =
      MvPowerSeries.coeff d f := by
  rw [PowerSeries.coeff, MvPowerSeries.coeff_subst, finsum_eq_single _ d]
  · simp [hd, PowerSeries.coeff_X_pow]
  · intro e hed
    by_cases he : e 1 = 0
    · have he0 : e 0 ≠ d 0 := by
        intro he0
        apply hed
        ext i
        fin_cases i
        · exact he0
        · exact he.trans hd.symm
      simp [he, PowerSeries.coeff_X_pow, he0.symm]
    · simp [he]
  · exact MvPowerSeries.HasSubst.X_zero

/-- The right displacement `F − X₀` is divisible by the second variable. -/
private theorem formalGroup_rightDisplacement_dvd (hπ : Irreducible π)
    (e : LubinTateSeries A π) :
    (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) A) ∣
      lubinTateFormalGroupPowerSeries hπ e - MvPowerSeries.X (0 : Fin 2) := by
  rw [MvPowerSeries.X_dvd_iff]
  intro d hd
  have hhas : MvPowerSeries.HasSubst
      (![(PowerSeries.X : MvPowerSeries Unit A), 0] : Fin 2 → MvPowerSeries Unit A) :=
    MvPowerSeries.HasSubst.X_zero
  have hsubst :
      MvPowerSeries.subst
          (![(PowerSeries.X : MvPowerSeries Unit A), 0] : Fin 2 → MvPowerSeries Unit A)
          (lubinTateFormalGroupPowerSeries hπ e - MvPowerSeries.X (0 : Fin 2)) = 0 := by
    rw [MvPowerSeries.subst_sub hhas, formalGroup_subst_X_zero hπ e,
      MvPowerSeries.subst_X hhas]
    simp
  have hcoeff := congrArg (PowerSeries.coeff (d 0)) hsubst
  rw [coeff_subst_X_zero' _ d hd] at hcoeff
  simpa using hcoeff

/-- The right-displacement cofactor. -/
private noncomputable def rightDisplacementFactor (hπ : Irreducible π)
    (e : LubinTateSeries A π) : MvPowerSeries (Fin 2) A :=
  Classical.choose (formalGroup_rightDisplacement_dvd hπ e)

private theorem rightDisplacement_factor (hπ : Irreducible π) (e : LubinTateSeries A π) :
    lubinTateFormalGroupPowerSeries hπ e - MvPowerSeries.X (0 : Fin 2) =
      MvPowerSeries.X (1 : Fin 2) * rightDisplacementFactor hπ e :=
  Classical.choose_spec (formalGroup_rightDisplacement_dvd hπ e)

/-- The cofactor has constant coefficient one. -/
private theorem rightDisplacementFactor_constantCoeff (hπ : Irreducible π)
    (e : LubinTateSeries A π) :
    MvPowerSeries.constantCoeff (rightDisplacementFactor hπ e) = 1 := by
  have hfactor := congrArg (MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1))
    (rightDisplacement_factor hπ e)
  have hleft : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)
      (lubinTateFormalGroupPowerSeries hπ e - MvPowerSeries.X (0 : Fin 2)) = 1 := by
    rw [map_sub,
      (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).coeff_eq_of_degree_lt_two
        (by simp [Finsupp.degree_single]),
      coeff_lubinTateLinearForm_single]
    simp [MvPowerSeries.coeff_index_single_X]
  have hright : MvPowerSeries.coeff (Finsupp.single (1 : Fin 2) 1)
      (MvPowerSeries.X (1 : Fin 2) * rightDisplacementFactor hπ e) =
      MvPowerSeries.constantCoeff (rightDisplacementFactor hπ e) := by
    rw [MvPowerSeries.X_def]
    simpa only [add_zero, one_mul, MvPowerSeries.coeff_zero_eq_constantCoeff_apply] using
      MvPowerSeries.coeff_add_monomial_mul (m := Finsupp.single (1 : Fin 2) 1)
        (n := 0) (rightDisplacementFactor hπ e) 1
  rw [hleft, hright] at hfactor
  exact hfactor.symm

/-- The scalar endomorphism is divisible by `X`. -/
private theorem scalar_X_dvd (hπ : Irreducible π) (e : LubinTateSeries A π) (a : A) :
    (PowerSeries.X : PowerSeries A) ∣ (lubinTateScalar hπ e a : PowerSeries A) := by
  rw [PowerSeries.X_dvd_iff]
  exact (lubinTateScalar_hasLinearTerm hπ e a).constantCoeff_eq_zero

/-- The scalar cofactor. -/
private noncomputable def scalarFactor (hπ : Irreducible π) (e : LubinTateSeries A π)
    (a : A) : PowerSeries A :=
  Classical.choose (scalar_X_dvd hπ e a)

private theorem scalar_factor (hπ : Irreducible π) (e : LubinTateSeries A π) (a : A) :
    (lubinTateScalar hπ e a : PowerSeries A) =
      PowerSeries.X * scalarFactor hπ e a :=
  Classical.choose_spec (scalar_X_dvd hπ e a)

/-- The scalar cofactor has constant coefficient the scalar. -/
private theorem scalarFactor_constantCoeff (hπ : Irreducible π) (e : LubinTateSeries A π)
    (a : A) : PowerSeries.constantCoeff (scalarFactor hπ e a) = a := by
  have hfactor := congrArg (PowerSeries.coeff 1) (scalar_factor hπ e a)
  have hleft : PowerSeries.coeff 1 (lubinTateScalar hπ e a : PowerSeries A) = a := by
    have h := (lubinTateScalar_hasLinearTerm hπ e a).coeff_eq_of_degree_lt_two
      (d := Finsupp.single () 1) (by simp [Finsupp.degree_single])
    rw [PowerSeries.coeff, h, coeff_lubinTateLinearForm_single]
  rw [hleft, PowerSeries.coeff_succ_X_mul] at hfactor
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  exact hfactor.symm

end Series

section Evaluated

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [Algebra K E]
  [ValuativeExtension K E] [IsMixedCharLocalField E]
variable {π : ↥𝒪[K]} (hπ : Irreducible π)

/-- The evaluated right displacement factors through the second argument, with a
principal-unit cofactor. -/
private theorem lubinTateAdd_sub_left_factor (e : LubinTateSeries ↥𝒪[K] π)
    {x y : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) (hy : y ∈ 𝓂[E]) :
    ∃ c : ↥𝒪[E], c - 1 ∈ 𝓂[E] ∧
      lubinTateAdd K E hπ e x y - x = y * c := by
  letI uK : UniformSpace ↥𝒪[K] := ⊥
  haveI : DiscreteUniformity ↥𝒪[K] := by infer_instance
  letI uE : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  haveI : IsUniformAddGroup ↥𝒪[E] := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace ↥𝒪[E] := complete_of_compact
  have hv : ∀ s : Fin 2, (![x, y] : Fin 2 → ↥𝒪[E]) s ∈ 𝓂[E] := by
    intro s
    fin_cases s
    · exact hx
    · exact hy
  have hb : MvPowerSeries.HasEval (![x, y] : Fin 2 → ↥𝒪[E]) :=
    hasEval_of_mem_maximalIdeal E hv
  haveI hdt : @DiscreteTopology ↥𝒪[K] uK.toTopologicalSpace := inferInstance
  have hφc : @Continuous _ _ uK.toTopologicalSpace uE.toTopologicalSpace
      (algebraMap ↥𝒪[K] ↥𝒪[E]) :=
    @continuous_of_discreteTopology _ uK.toTopologicalSpace hdt _
      uE.toTopologicalSpace _
  set Φ := MvPowerSeries.eval₂Hom hφc hb with hΦ
  refine ⟨Φ (rightDisplacementFactor hπ e), ?_, ?_⟩
  · have hmem := eval₂_mem_maximalIdeal K E
      (F := rightDisplacementFactor hπ e - (MvPowerSeries.C 1 : MvPowerSeries (Fin 2) ↥𝒪[K]))
      (by rw [map_sub, rightDisplacementFactor_constantCoeff hπ e,
        MvPowerSeries.constantCoeff_C]; ring) hv
    have hone : Φ ((MvPowerSeries.C 1 : MvPowerSeries (Fin 2) ↥𝒪[K])) = 1 := by
      rw [hΦ, MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C, map_one]
    have hsub : Φ (rightDisplacementFactor hπ e -
        (MvPowerSeries.C 1 : MvPowerSeries (Fin 2) ↥𝒪[K])) =
        Φ (rightDisplacementFactor hπ e) - 1 := by
      rw [map_sub, hone]
    rw [← hsub, hΦ, MvPowerSeries.coe_eval₂Hom]
    exact hmem
  · have happ := congrArg Φ (rightDisplacement_factor hπ e)
    rw [map_sub, map_mul] at happ
    have hX0 : Φ (MvPowerSeries.X (0 : Fin 2)) = x := by
      rw [hΦ, MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]
      rfl
    have hX1 : Φ (MvPowerSeries.X (1 : Fin 2)) = y := by
      rw [hΦ, MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_X]
      rfl
    have hF : Φ (lubinTateFormalGroupPowerSeries hπ e) = lubinTateAdd K E hπ e x y := by
      rw [hΦ, MvPowerSeries.coe_eval₂Hom]
      rfl
    rw [hX0, hX1, hF] at happ
    exact happ

/-- The evaluated scalar factors through its argument, with a cofactor congruent to
the scalar. -/
private theorem lubinTateSMul_factor (e : LubinTateSeries ↥𝒪[K] π) (a : ↥𝒪[K])
    {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) :
    ∃ c : ↥𝒪[E], c - algebraMap ↥𝒪[K] ↥𝒪[E] a ∈ 𝓂[E] ∧
      lubinTateSMul K E hπ e a x = x * c := by
  letI uK : UniformSpace ↥𝒪[K] := ⊥
  haveI : DiscreteUniformity ↥𝒪[K] := by infer_instance
  letI uE : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  haveI : IsUniformAddGroup ↥𝒪[E] := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace ↥𝒪[E] := complete_of_compact
  have hv : ∀ s : Unit, (fun _ : Unit => x) s ∈ 𝓂[E] := fun _ => hx
  have hb : MvPowerSeries.HasEval (fun _ : Unit => x) :=
    hasEval_of_mem_maximalIdeal E hv
  haveI hdt : @DiscreteTopology ↥𝒪[K] uK.toTopologicalSpace := inferInstance
  have hφc : @Continuous _ _ uK.toTopologicalSpace uE.toTopologicalSpace
      (algebraMap ↥𝒪[K] ↥𝒪[E]) :=
    @continuous_of_discreteTopology _ uK.toTopologicalSpace hdt _
      uE.toTopologicalSpace _
  set Φ := MvPowerSeries.eval₂Hom hφc hb with hΦ
  refine ⟨Φ ((scalarFactor hπ e a : PowerSeries ↥𝒪[K]) : MvPowerSeries Unit ↥𝒪[K]),
    ?_, ?_⟩
  · have hmem := eval₂_mem_maximalIdeal K E
      (F := ((scalarFactor hπ e a : PowerSeries ↥𝒪[K]) : MvPowerSeries Unit ↥𝒪[K]) -
        (MvPowerSeries.C a : MvPowerSeries Unit ↥𝒪[K]))
      (by rw [map_sub, MvPowerSeries.constantCoeff_C]
          have := scalarFactor_constantCoeff hπ e a
          rw [show MvPowerSeries.constantCoeff
              ((scalarFactor hπ e a : PowerSeries ↥𝒪[K]) : MvPowerSeries Unit ↥𝒪[K]) =
              PowerSeries.constantCoeff (scalarFactor hπ e a) from rfl, this]
          ring) hv
    have hC : Φ ((MvPowerSeries.C a : MvPowerSeries Unit ↥𝒪[K])) = algebraMap ↥𝒪[K] ↥𝒪[E] a := by
      rw [hΦ, MvPowerSeries.coe_eval₂Hom, MvPowerSeries.eval₂_C]
    have hsub : Φ (((scalarFactor hπ e a : PowerSeries ↥𝒪[K]) :
        MvPowerSeries Unit ↥𝒪[K]) - (MvPowerSeries.C a : MvPowerSeries Unit ↥𝒪[K])) =
        Φ ((scalarFactor hπ e a : PowerSeries ↥𝒪[K]) : MvPowerSeries Unit ↥𝒪[K]) -
          algebraMap ↥𝒪[K] ↥𝒪[E] a := by
      rw [map_sub, hC]
    rw [← hsub, hΦ, MvPowerSeries.coe_eval₂Hom]
    exact hmem
  · have happ := congrArg Φ (scalar_factor hπ e a)
    rw [show ((PowerSeries.X * scalarFactor hπ e a : PowerSeries ↥𝒪[K]) :
        MvPowerSeries Unit ↥𝒪[K]) =
      (PowerSeries.X : MvPowerSeries Unit ↥𝒪[K]) *
        ((scalarFactor hπ e a : PowerSeries ↥𝒪[K]) : MvPowerSeries Unit ↥𝒪[K])
      from rfl, map_mul] at happ
    have hX : Φ (PowerSeries.X : MvPowerSeries Unit ↥𝒪[K]) = x := by
      rw [show (PowerSeries.X : MvPowerSeries Unit ↥𝒪[K]) =
        MvPowerSeries.X () from rfl, hΦ, MvPowerSeries.coe_eval₂Hom,
        MvPowerSeries.eval₂_X]
    have hS : Φ ((lubinTateScalar hπ e a : PowerSeries ↥𝒪[K]) :
        MvPowerSeries Unit ↥𝒪[K]) = lubinTateSMul K E hπ e a x := by
      rw [hΦ, MvPowerSeries.coe_eval₂Hom]
      rfl
    rw [hX, hS] at happ
    exact happ

/-- **The right displacement takes the displacing value**: `ν(x +[e] y − x) = ν(y)` —
the cofactor of the factorization `F − X₀ = X₁ · G` evaluates to a principal unit
([Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveDisplacement.lean:291`]
[Yamaguchi2026]). -/
theorem integerValuation_lubinTateAdd_sub_left (e : LubinTateSeries ↥𝒪[K] π)
    {x y : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) (hy : y ∈ 𝓂[E]) :
    integerValuation E (lubinTateAdd K E hπ e x y - x) = integerValuation E y := by
  obtain ⟨c, hc, heq⟩ := lubinTateAdd_sub_left_factor K E hπ e hx hy
  have hcunit : IsUnit c := by
    have h := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _
      ((IsLocalRing.mem_maximalIdeal _).mp (neg_mem hc))
    rwa [sub_neg_eq_add, add_comm, sub_add_cancel] at h
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [heq, zero_mul, integerValuation_zero]
  · rw [heq, integerValuation_mul E hy0 hcunit.ne_zero,
      integerValuation_eq_zero_of_isUnit E hcunit, add_zero]

/-- **A unit scalar preserves the value**: `ν([a] x) = ν(x)` for `a` a unit — the
scalar endomorphism is `X` times a series whose evaluation is congruent to `a`
([Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveDisplacement.lean:345`]
[Yamaguchi2026]). -/
theorem integerValuation_lubinTateSMul_isUnit (e : LubinTateSeries ↥𝒪[K] π)
    {a : ↥𝒪[K]} (ha : IsUnit a) {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) :
    integerValuation E (lubinTateSMul K E hπ e a x) = integerValuation E x := by
  obtain ⟨c, hc, heq⟩ := lubinTateSMul_factor K E hπ e a hx
  have haE : IsUnit (algebraMap ↥𝒪[K] ↥𝒪[E] a) := ha.map _
  have hcunit : IsUnit c := by
    by_contra hnc
    have hmemc : c ∈ 𝓂[E] :=
      (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnc)
    have hmema : algebraMap ↥𝒪[K] ↥𝒪[E] a ∈ 𝓂[E] := by
      have := Ideal.sub_mem _ hmemc hc
      simpa using this
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmema
    exact hmema haE
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [heq, zero_mul, integerValuation_zero]
  · rw [heq, integerValuation_mul E hx0 hcunit.ne_zero,
      integerValuation_eq_zero_of_isUnit E hcunit, add_zero]

/-- **The displacement identity**: `ν([u] x − x) = ν([u − 1] x)` — the module law
`[u] x = [u − 1] x +[e] x` reads the displacement off the right-displacement value. -/
theorem integerValuation_lubinTateSMul_sub_self (e : LubinTateSeries ↥𝒪[K] π)
    (u : ↥𝒪[K]) {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) :
    integerValuation E (lubinTateSMul K E hπ e u x - x) =
      integerValuation E (lubinTateSMul K E hπ e (u - 1) x) := by
  have hz : lubinTateSMul K E hπ e (u - 1) x ∈ 𝓂[E] :=
    lubinTateSMul_mem_maximalIdeal K E hπ e _ hx
  have hlaw := lubinTateSMul_add K E hπ e (u - 1) 1 hx
  rw [sub_add_cancel, lubinTateSMul_one] at hlaw
  rw [hlaw, lubinTateAdd_comm K E hπ e hz hx]
  exact integerValuation_lubinTateAdd_sub_left K E hπ e hx hz

/-- **The displacement spectrum at a primitive root**: a scalar whose distance from
one has depth exactly `j ≤ n` displaces the root by value `qʲ ν(x)`
([Milne 2020, Chap. I, §3, the proof of Thm. 3.6 (a), (b), pp.38–39][MilneCFT] — the tower
structure behind the conjugate distances;
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveDisplacement.lean:494`]
[Yamaguchi2026]). -/
theorem integerValuation_standardLubinTateSMul_sub_self
    {n : ℕ} {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E])
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    {j : ℕ} (hj : j ≤ n) {w : ↥𝒪[K]} (hw : IsUnit w) {u : ↥𝒪[K]}
    (hu : u - 1 = π ^ j * w) :
    integerValuation E
        (lubinTateSMul K E hπ (standardLubinTateSeries hπ) u x - x) =
      (Nat.card 𝓀[K] : ℤ) ^ j * integerValuation E x := by
  rw [integerValuation_lubinTateSMul_sub_self K E hπ _ u hx, hu]
  rw [mul_comm (π ^ j) w, ← lubinTateSMul_smul K E hπ _ w (π ^ j) hx]
  rw [integerValuation_lubinTateSMul_isUnit K E hπ _ hw
    (lubinTateSMul_mem_maximalIdeal K E hπ _ _ hx)]
  rw [standardLubinTateSMul_pi_pow K E hπ hx j]
  exact integerValuation_aeval_standardLubinTatePolynomialIterate K E hπ hroot hj

end Evaluated

end Atlas.Knowledge
