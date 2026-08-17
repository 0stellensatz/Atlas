import Mathlib
import Atlas.Knowledge.AddValMapIntegralClosure
import Atlas.Knowledge.IntegralClosureDVR
import Atlas.Knowledge.MinpolyMapEqCharpoly
import Atlas.Knowledge.MonogenicIntegralClosure
import Atlas.Knowledge.RamificationNumber
import Atlas.Knowledge.RamificationNumberEqAddVal
import Atlas.Knowledge.RestrictScalarsHomRangeEqKer

/-!
# ramification number fiber sum

For a normal subextension `E` of a finite Galois extension `L` of a mixed-characteristic local
field `K`, the ramification number of an automorphism `σ'` of `E` over `K`, scaled by the
ramification index of `L` over `E`, is the sum of the ramification numbers of the automorphisms
of `L` restricting to `σ'`—Serre's Prop. 3, in the proof he attributes to J. Tate. This is the
identity from which the ramification groups of a quotient are computed, and the whole of Tate's
argument—the two elements `a = s (y) - y` and `b = ∏ (s t (x) - x)` generating the same ideal by
mutual divisibility—is carried out here in the integral closures.

## Main statements

* `ramificationNumber_fiber_sum` — `e • ramificationNumber K E σ'` equals the sum of
  `ramificationNumber K L s` over the fiber of `AlgEquiv.restrictNormalHom` above `σ'`, with
  `e` the exponent of the ideal identity relating the maximal ideals of the two closures.

## Implementation notes

The statement is assembled from the layer's valuation-free vocabulary: the ramification index
enters as the exponent of the ideal identity between the maximal ideals of the two closures,
taken as a hypothesis exactly as in `Atlas.Knowledge.AddValMapIntegralClosure`, and both
ramification numbers are read as orders through `Atlas.Knowledge.RamificationNumberEqAddVal` at
the generators `Atlas.Knowledge.MonogenicIntegralClosure` supplies. Serre opens the proof by
disposing of `σ = 1`, where both sides are infinite; here no case split is made: the elements
`a` and `b` are compared by mutual divisibility, which at `σ' = 1` degenerates to `0 ∣ 0`, and
the `ℕ∞` arithmetic of `IsDiscreteValuationRing.addVal` absorbs `⊤` uniformly. Serre's `f`, the
minimal polynomial of `x` over the intermediate field, is taken instead over the integral
closure of `𝒪[K]` in `E`—that is what lets the coefficientwise divisibility by `a` be stated
inside the closure—and `minpoly.isIntegrallyClosed_eq_field_fractions'` identifies its
pushforward into `E` with the field minimal polynomial, whence
`Atlas.Knowledge.MinpolyMapEqCharpoly` writes the further pushforward into `L` as the orbit
product `∏ (X - C (t • x))`. The two halves of the divisibility are the source's two displays:
"`s (f) - f` has all coefficients divisible by `s (y) - y`" is `sub_dvd_galRestrict_sub`, each
coefficient a polynomial in `y` over `𝒪[K]` by monogenicity so that
`Polynomial.sub_dvd_eval_sub` applies—the pattern of
`natCast_le_ramificationNumber_iff_of_adjoin_eq_top` replayed—and "`g (X) - y = f (X) * h (X)`,
transform by `s` and substitute `x`" is `minpoly.isIntegrallyClosed_dvd` pushed through the
coefficient map, the explicit factor `h` never named. The sign in the source's `s (f) (x)`,
which is `b` up to sign, is the unit `(-1) ^ card`, and both divisibility transports cross it
through `IsUnit.dvd_mul_left` and `IsUnit.mul_left_dvd` rather than normalizing it away. The
scaffolding carries the namespace as a name prefix instead of a `namespace` block so the shared
`variable` line serves the principal statement too.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]

/-- The additive valuation of a discrete valuation ring takes a finite product to the sum of
the factors' valuations—`IsDiscreteValuationRing.addVal_mul` iterated over a `Finset`. -/
theorem RamificationNumberFiberSum.addVal_prod {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {ι : Type*} (s : Finset ι) (f : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, f i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.prod_cons, Finset.sum_cons, IsDiscreteValuationRing.addVal_mul, ih]

/-- An element dividing every coefficient of a polynomial divides its value at any point. -/
theorem RamificationNumberFiberSum.dvd_eval_of_dvd_coeff {R : Type*} [CommRing R] {a z : R}
    {p : Polynomial R} (h : ∀ i, a ∣ p.coeff i) : a ∣ p.eval z := by
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  exact Finset.dvd_sum fun i _ => (h i).mul_right _

/-- A generator of the integral closure of `𝒪[K]` in `L` is a primitive element of `L` over any
intermediate field: every element of `L` is an `𝒪[K]`-denominator away from a polynomial in the
generator, so adjoining it to `E` already gives all of `L`
([Serre 1979, Chap. IV, §1, proof of Prop. 3, p.63][Serre1979]). -/
theorem RamificationNumberFiberSum.intermediateField_adjoin_eq_top
    {x : integralClosure 𝒪[K] L}
    (hx : Algebra.adjoin 𝒪[K] ({x} : Set (integralClosure 𝒪[K] L)) = ⊤) :
    IntermediateField.adjoin E {(x : L)} = ⊤ := by
  haveI : Algebra.IsAlgebraic 𝒪[K] L :=
    IsFractionRing.comap_isAlgebraic_iff.mpr ‹Algebra.IsAlgebraic K L›
  rw [eq_top_iff]
  rintro l -
  obtain ⟨d, hd, hint⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic (R := 𝒪[K]) l).exists_integral_multiple
  have hmem : d • l ∈ integralClosure 𝒪[K] L := hint
  have hw : (⟨d • l, hmem⟩ : integralClosure 𝒪[K] L) ∈
      Algebra.adjoin 𝒪[K] ({x} : Set (integralClosure 𝒪[K] L)) := by
    rw [hx]; exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hw
  obtain ⟨P, hP⟩ := hw
  have hcoe : Polynomial.aeval (x : L) P = d • l := by
    rw [← Polynomial.aeval_subalgebra_coe, hP]
  have hinj : Function.Injective (algebraMap 𝒪[K] L) := by
    rw [IsScalarTower.algebraMap_eq 𝒪[K] K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective 𝒪[K] K)
  have hd0 : algebraMap 𝒪[K] L d ≠ 0 := fun h0 =>
    hd (hinj (h0.trans (map_zero (algebraMap 𝒪[K] L)).symm))
  have hxF : (x : L) ∈ IntermediateField.adjoin E {(x : L)} :=
    IntermediateField.mem_adjoin_simple_self E (x : L)
  have haevF : Polynomial.aeval (x : L) P ∈ IntermediateField.adjoin E {(x : L)} := by
    have hle : Algebra.adjoin 𝒪[K] {(x : L)} ≤
        Subalgebra.restrictScalars 𝒪[K] (IntermediateField.adjoin E {(x : L)}).toSubalgebra :=
      Algebra.adjoin_le (Set.singleton_subset_iff.mpr hxF)
    exact hle (Polynomial.aeval_mem_adjoin_singleton _ _)
  have hdF : algebraMap 𝒪[K] L d ∈ IntermediateField.adjoin E {(x : L)} := by
    rw [IsScalarTower.algebraMap_apply 𝒪[K] E L]
    exact (IntermediateField.adjoin E {(x : L)}).algebraMap_mem _
  have hl : l = (algebraMap 𝒪[K] L d)⁻¹ * Polynomial.aeval (x : L) P := by
    rw [hcoe, Algebra.smul_def, inv_mul_cancel_left₀ hd0]
  rw [hl]
  exact (IntermediateField.adjoin E {(x : L)}).mul_mem
    ((IntermediateField.adjoin E {(x : L)}).inv_mem hdF) haevF

/-- The element `a = s (y) - y` divides `s (z') - z'` for the image `z'` of every element `z` of
the closure downstairs: `z` is a polynomial in the generator `y` over `𝒪[K]`, so the difference
is a polynomial difference `Polynomial.sub_dvd_eval_sub` divides—the source's "as `s (f) - f`
has all coefficients divisible by `s (y) - y`", coefficient by coefficient
([Serre 1979, Chap. IV, §1, proof of Prop. 3, p.63][Serre1979]). -/
theorem RamificationNumberFiberSum.sub_dvd_galRestrict_sub
    {y : integralClosure 𝒪[K] E}
    (hy : Algebra.adjoin 𝒪[K] ({y} : Set (integralClosure 𝒪[K] E)) = ⊤)
    (σ : L ≃ₐ[K] L) (z : integralClosure 𝒪[K] E) :
    galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ
          (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y) -
        AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y ∣
      galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ
          (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) z) -
        AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) z := by
  have hz : z ∈ Algebra.adjoin 𝒪[K] ({y} : Set (integralClosure 𝒪[K] E)) := by
    rw [hy]; exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hz
  obtain ⟨P, rfl⟩ := hz
  rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply,
    ← Polynomial.eval_map_algebraMap, ← Polynomial.eval_map_algebraMap]
  exact Polynomial.sub_dvd_eval_sub _ _ _

/-- The pushforward of the closures intertwines the integral restrictions of compatible
automorphisms: for `σ` restricting to `σ'` on `E`, pushing the `galRestrict` of `σ'` forward
along the closure inclusion is applying the `galRestrict` of `σ` to the pushforward—Serre's
tacit identification of the action of an automorphism of the subextension on its closure with
the action of any representative upstairs
([Serre 1979, Chap. IV, §1, proof of Prop. 3, p.63][Serre1979]). -/
theorem RamificationNumberFiberSum.mapIntegralClosure_galRestrict [Normal K E]
    {σ : L ≃ₐ[K] L} {σ' : E ≃ₐ[K] E}
    (hσ : AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E σ = σ')
    (z : integralClosure 𝒪[K] E) :
    AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L)
        (galRestrict 𝒪[K] K E (integralClosure 𝒪[K] E) σ' z) =
      galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ
        (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) z) := by
  have hcomm : ∀ w : E,
      algebraMap E L (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E σ w) =
        σ (algebraMap E L w) := fun w => AlgEquiv.restrictNormal_commutes σ E w
  refine Subtype.ext ?_
  change algebraMap E L (algebraMap (integralClosure 𝒪[K] E) E
      (galRestrict 𝒪[K] K E (integralClosure 𝒪[K] E) σ' z)) =
    algebraMap (integralClosure 𝒪[K] L) L (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ
      (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) z))
  rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply, ← hσ, hcomm]
  rfl

/-- The heart of Tate's proof: the elements `a = s (y) - y` and `b = ∏ (s t (x) - x)` have the
same order in the closure upstairs. Each divides the other up to sign: `a` divides `s (f) (x)`
because `s (f) - f` has all coefficients divisible by `a` while `f (x) = 0`, and `s (f) (x)`
divides `a` because `g (X) - y` has `x` as a root and coefficients downstairs, so the minimal
polynomial `f` divides it; `s (f) (x)` differs from `b` by the unit `(-1) ^ card`, which both
transports cross as a unit
([Serre 1979, Chap. IV, §1, proof of Prop. 3, pp.63–64][Serre1979]). -/
theorem RamificationNumberFiberSum.addVal_eq_addVal_prod [TopologicalSpace K]
    [IsMixedCharLocalField K] [FiniteDimensional K E] [FiniteDimensional K L]
    [FiniteDimensional E L] [IsGalois E L]
    {x : integralClosure 𝒪[K] L}
    (hxring : Algebra.adjoin 𝒪[K] ({x} : Set (integralClosure 𝒪[K] L)) = ⊤)
    {y : integralClosure 𝒪[K] E}
    (hy : Algebra.adjoin 𝒪[K] ({y} : Set (integralClosure 𝒪[K] E)) = ⊤)
    (σ : L ≃ₐ[K] L) :
    IsDiscreteValuationRing.addVal (integralClosure 𝒪[K] L)
        (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ
            (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y) -
          AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y) =
      IsDiscreteValuationRing.addVal (integralClosure 𝒪[K] L)
        (∏ t : L ≃ₐ[E] L, (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
          (σ * AlgEquiv.restrictScalars K t) x - x)) := by
  haveI : IsFractionRing (integralClosure 𝒪[K] E) E :=
    integralClosure.isFractionRing_of_finite_extension K E
  have hALinj : Function.Injective (algebraMap (integralClosure 𝒪[K] L) L) :=
    fun _ _ h => Subtype.ext h
  have hxint : IsIntegral (integralClosure 𝒪[K] E) (x : L) :=
    IsIntegral.tower_top x.2
  have hxfield : IntermediateField.adjoin E {(x : L)} = ⊤ :=
    RamificationNumberFiberSum.intermediateField_adjoin_eq_top K L E hxring
  -- the coefficient map: apply `γ = galRestrict … σ` after the closure pushforward `ι`
  obtain ⟨φ, hφ⟩ : ∃ φ : integralClosure 𝒪[K] E →+* integralClosure 𝒪[K] L,
      ∀ z, φ z = galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ
        (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) z) :=
    ⟨((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ).toAlgHom.toRingHom).comp
      (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L)).toRingHom, fun _ => rfl⟩
  -- `f (x) = 0` read in the closure upstairs: the `ι`-pushed minimal polynomial kills `x`
  have hFι0 : ((minpoly (integralClosure 𝒪[K] E) ((x : L))).map
      (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L)).toRingHom).eval x = 0 := by
    apply hALinj
    rw [map_zero, ← Polynomial.eval₂_at_apply, Polynomial.eval₂_map]
    have hι : (algebraMap (integralClosure 𝒪[K] L) L).comp
        (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L)).toRingHom =
        algebraMap (integralClosure 𝒪[K] E) L := RingHom.ext fun z => rfl
    rw [hι, ← Polynomial.aeval_def]
    exact minpoly.aeval _ _
  -- the coefficients of `s (f) - f` are all divisible by `a = s (y) - y`
  have hcoeffdvd : ∀ i,
      galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ
          (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y) -
        AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y ∣
      ((minpoly (integralClosure 𝒪[K] E) ((x : L))).map φ).coeff i -
        ((minpoly (integralClosure 𝒪[K] E) ((x : L))).map
          (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L)).toRingHom).coeff i := by
    intro i
    rw [Polynomial.coeff_map, Polynomial.coeff_map, hφ]
    exact RamificationNumberFiberSum.sub_dvd_galRestrict_sub K L E hy σ _
  -- hence `a` divides `s (f) (x) = s (f) (x) - f (x)`
  have haFσ : galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ
        (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y) -
      AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y ∣
      ((minpoly (integralClosure 𝒪[K] E) ((x : L))).map φ).eval x := by
    have h0 : ((minpoly (integralClosure 𝒪[K] E) ((x : L))).map φ).eval x =
        ((minpoly (integralClosure 𝒪[K] E) ((x : L))).map φ -
          (minpoly (integralClosure 𝒪[K] E) ((x : L))).map
            (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L)).toRingHom).eval x := by
      rw [Polynomial.eval_sub, hFι0, sub_zero]
    rw [h0]
    refine RamificationNumberFiberSum.dvd_eval_of_dvd_coeff fun i => ?_
    rw [Polynomial.coeff_sub]
    exact hcoeffdvd i
  -- `s (f) (x) = ± b`: the evaluation of the `s`-transformed minimal polynomial is the product
  have hFσeval : ((minpoly (integralClosure 𝒪[K] E) ((x : L))).map φ).eval x =
      (-1) ^ Fintype.card (L ≃ₐ[E] L) *
        ∏ t : L ≃ₐ[E] L, (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
          (σ * AlgEquiv.restrictScalars K t) x - x) := by
    apply hALinj
    have hL1 : algebraMap (integralClosure 𝒪[K] L) L
        (((minpoly (integralClosure 𝒪[K] E) ((x : L))).map φ).eval x) =
        ∏ t : L ≃ₐ[E] L, ((x : L) - σ (t (x : L))) := by
      have hcompL : (algebraMap (integralClosure 𝒪[K] L) L).comp φ =
          σ.toAlgHom.toRingHom.comp (algebraMap (integralClosure 𝒪[K] E) L) := by
        refine RingHom.ext fun z => ?_
        rw [RingHom.comp_apply, hφ, algebraMap_galRestrict_apply]
        rfl
      rw [← Polynomial.eval₂_at_apply, Polynomial.eval₂_map, hcompL,
        IsScalarTower.algebraMap_eq (integralClosure 𝒪[K] E) E L, ← RingHom.comp_assoc,
        ← Polynomial.eval₂_map, ← minpoly.isIntegrallyClosed_eq_field_fractions' E hxint,
        ← Polynomial.eval₂_map, ← Polynomial.eval_map, minpolyMapEqCharpoly E L hxfield,
        MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.eval_prod]
      refine Finset.prod_congr rfl fun t _ => ?_
      rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C]
      rfl
    have hL2 : algebraMap (integralClosure 𝒪[K] L) L
        ((-1) ^ Fintype.card (L ≃ₐ[E] L) *
          ∏ t : L ≃ₐ[E] L, (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
            (σ * AlgEquiv.restrictScalars K t) x - x)) =
        (-1) ^ Fintype.card (L ≃ₐ[E] L) *
          ∏ t : L ≃ₐ[E] L, (σ (t (x : L)) - (x : L)) := by
      rw [map_mul, map_pow, map_neg, map_one, map_prod]
      refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun t _ => ?_)
      rw [map_sub, algebraMap_galRestrict_apply]
      rfl
    rw [hL1, hL2, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun t _ => by rw [neg_one_mul, neg_sub]
  -- `b ∣ ± a`: Serre's `g (X) - y = f (X) · h (X)`, transformed by `s` and evaluated at `x`
  have hyQ : AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y ∈
      Algebra.adjoin 𝒪[K] ({x} : Set (integralClosure 𝒪[K] L)) := by
    rw [hxring]; exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hyQ
  obtain ⟨Q, hQ⟩ := hyQ
  have hR0 : Polynomial.aeval (x : L)
      (Q.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] E)) - Polynomial.C y) = 0 := by
    rw [map_sub, Polynomial.aeval_C, Polynomial.aeval_map_algebraMap, sub_eq_zero,
      ← Polynomial.aeval_subalgebra_coe, hQ]
    rfl
  have hFdvd : minpoly (integralClosure 𝒪[K] E) ((x : L)) ∣
      Q.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] E)) - Polynomial.C y :=
    minpoly.isIntegrallyClosed_dvd hxint hR0
  have hRσ : (Q.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] E)) - Polynomial.C y).map φ =
      Q.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) - Polynomial.C (φ y) := by
    have hcomp : φ.comp (algebraMap 𝒪[K] (integralClosure 𝒪[K] E)) =
        algebraMap 𝒪[K] (integralClosure 𝒪[K] L) :=
      RingHom.ext fun r => by rw [RingHom.comp_apply, hφ, AlgHom.commutes, AlgEquiv.commutes]
    rw [Polynomial.map_sub, Polynomial.map_map, Polynomial.map_C, hcomp]
  have hevalRσ : (Q.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) -
      Polynomial.C (φ y)).eval x =
      -(galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ
          (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y) -
        AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y) := by
    rw [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_map_algebraMap, hQ, hφ, neg_sub]
  have hFσa : ((minpoly (integralClosure 𝒪[K] E) ((x : L))).map φ).eval x ∣
      -(galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ
          (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y) -
        AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y) := by
    rw [← hevalRσ, ← hRσ]
    exact Polynomial.eval_dvd (Polynomial.map_dvd φ hFdvd)
  -- mutual divisibility, the sign crossed as the unit `(-1) ^ card`
  have hunit : IsUnit ((-1 : integralClosure 𝒪[K] L) ^ Fintype.card (L ≃ₐ[E] L)) :=
    isUnit_one.neg.pow _
  have hab : galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ
        (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y) -
      AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y ∣
      ∏ t : L ≃ₐ[E] L, (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
        (σ * AlgEquiv.restrictScalars K t) x - x) := by
    have h := haFσ
    rw [hFσeval] at h
    exact (IsUnit.dvd_mul_left hunit).mp h
  have hba : (∏ t : L ≃ₐ[E] L, (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
        (σ * AlgEquiv.restrictScalars K t) x - x)) ∣
      galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ
          (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y) -
        AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y := by
    have h := hFσa
    rw [hFσeval] at h
    exact dvd_neg.mp ((IsUnit.mul_left_dvd hunit).mp h)
  exact le_antisymm (IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hab)
    (IsDiscreteValuationRing.addVal_le_iff_dvd.mpr hba)

/-- For a normal subextension `E` of a finite Galois extension `L` of a mixed-characteristic
local field `K`, the ramification number of `σ' : E ≃ₐ[K] E` scaled by the ramification
index—the exponent `e` of the ideal identity taken as a hypothesis—is the sum of the
ramification numbers of the automorphisms of `L` restricting to `σ'`, the proof after J. Tate
([Serre 1979, Chap. IV, §1, Prop. 3, pp.63–64][Serre1979]). -/
theorem ramificationNumber_fiber_sum [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K E] [FiniteDimensional K L] [IsGalois K L] [Normal K E]
    [DecidableEq (E ≃ₐ[K] E)] {e : ℕ}
    (he : Ideal.map (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L))
        (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E)) =
      IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L) ^ e)
    (σ' : E ≃ₐ[K] E) :
    e • ramificationNumber K E σ' =
      ∑ s ∈ Finset.univ.filter
          (fun s : L ≃ₐ[K] L => AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E s = σ'),
        ramificationNumber K L s := by
  classical
  haveI : FiniteDimensional E L := Module.Finite.right K E L
  haveI : IsGalois E L := IsGalois.tower_top_of_isGalois K E L
  obtain ⟨y, hy⟩ := monogenicIntegralClosure K E
  obtain ⟨x, hxring⟩ := monogenicIntegralClosure K L
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (E := L) σ'
  calc e • ramificationNumber K E σ'
      = e • IsDiscreteValuationRing.addVal (integralClosure 𝒪[K] E)
          (galRestrict 𝒪[K] K E (integralClosure 𝒪[K] E) σ' y - y) := by
        rw [ramificationNumber_eq_addVal K E hy σ']
    _ = IsDiscreteValuationRing.addVal (integralClosure 𝒪[K] L)
          (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L)
            (galRestrict 𝒪[K] K E (integralClosure 𝒪[K] E) σ' y - y)) :=
        (addVal_mapIntegralClosure K L E he _).symm
    _ = IsDiscreteValuationRing.addVal (integralClosure 𝒪[K] L)
          (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ
              (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y) -
            AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom 𝒪[K] E L) y) := by
        rw [map_sub, RamificationNumberFiberSum.mapIntegralClosure_galRestrict K L E hσ y]
    _ = IsDiscreteValuationRing.addVal (integralClosure 𝒪[K] L)
          (∏ t : L ≃ₐ[E] L, (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
            (σ * AlgEquiv.restrictScalars K t) x - x)) :=
        RamificationNumberFiberSum.addVal_eq_addVal_prod K L E hxring hy σ
    _ = ∑ t : L ≃ₐ[E] L, IsDiscreteValuationRing.addVal (integralClosure 𝒪[K] L)
          (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L)
            (σ * AlgEquiv.restrictScalars K t) x - x) :=
        RamificationNumberFiberSum.addVal_prod _ _
    _ = ∑ t : L ≃ₐ[E] L, ramificationNumber K L (σ * AlgEquiv.restrictScalars K t) :=
        Finset.sum_congr rfl fun t _ => (ramificationNumber_eq_addVal K L hxring _).symm
    _ = ∑ s ∈ Finset.univ.filter
          (fun s : L ≃ₐ[K] L => AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E s = σ'),
        ramificationNumber K L s := by
        rw [restrictNormalHom_fiber_eq K E L σ σ' hσ]
        exact (Finset.sum_image fun t₁ _ t₂ _ h =>
          AlgEquiv.restrictScalarsHom_injective K (mul_left_cancel h)).symm

end Atlas.Knowledge
