import Mathlib
import Atlas.Knowledge.StandardLubinTateDerivativeValuation
import Atlas.Knowledge.StandardLubinTateParameterCongruence
import Atlas.Knowledge.StandardLubinTateSplitting

/-!
# standard Lubin–Tate root proximity

The pigeonhole at the heart of the changed-uniformizer comparison: at a `π`-primitive
root `x` and a `πu`-primitive root `y` in a common carrier, with `u` of depth `n + 1`,
some root of the changed primitive polynomial is equal to `x` or lies at value at least
`qⁿ⁺¹ ν(x)` from it — strictly above the conjugate ceiling `qⁿ ν(x)` of
`Atlas.Knowledge.integerValuation_standardLubinTateSMul_sub_self`, which is the Krasner
gap. The estimate is the classical cluster argument: the evaluation
`Φ_{πu}(x) = ∏ (x − r)` over the roots has total value at least `(n + 2) ν(π)` by the
parameter congruence, the closest root `r₀` absorbs everything the other factors cannot
carry, and the others are capped by `Σ ν(r₀ − r) = ν(Φ′_{πu}(r₀))`, the derivative
exponent — every root of the changed polynomial being itself `πu`-primitive.

## Main statements

* `standardLubinTateRootProximity` — the Krasner-gap root, with its primitivity;
  proved.
* `standardLubinTateRootProximity_lt` — the strict, Krasner-ready form; proved.

## Implementation notes

The conclusion is a disjunction — `x = r` or the value bound — because the `ℤ`-valued
`Atlas.Knowledge.integerValuation` junks to `0` at `0` where the bound would be false;
the source's `ℕ∞` estimate absorbs that case into `⊤` instead. The source also keeps
the maximal-root estimate general and instantiates it separately; here the two are
fused, because the instantiation is where all the values become computable — the
factor products convert through a private multiset version of
`Atlas.Knowledge.integerValuation_mul`, and the final inequality is linear once the
uniformizer value is kept atomic and one ring identity converts `2 ν(π) − (q−2)qⁿ ν(x)`
to `qⁿ⁺¹ ν(x)`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section Proximity

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [Algebra K E]
  [ValuativeExtension K E] [IsMixedCharLocalField E]

/-- The value of a product over a multiset of nonzero integers is the sum of values. -/
private theorem integerValuation_multiset_prod (s : Multiset ↥𝒪[E])
    (h0 : ∀ y ∈ s, y ≠ 0) :
    integerValuation E s.prod = (s.map (integerValuation E)).sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.sum_cons]
    have ha := h0 a (Multiset.mem_cons_self a s)
    have hs : s.prod ≠ 0 := by
      refine Multiset.prod_ne_zero ?_
      intro h0'
      exact h0 0 (Multiset.mem_cons_of_mem h0') rfl
    rw [integerValuation_mul E ha hs, ih (fun y hy => h0 y (Multiset.mem_cons_of_mem hy))]

/-- Divisibility bounds the value from below on nonzero targets. -/
private theorem integerValuation_le_of_dvd {a b : ↥𝒪[E]} (hb : b ≠ 0) (h : a ∣ b) :
    integerValuation E a ≤ integerValuation E b := by
  obtain ⟨c, rfl⟩ := h
  have ha : a ≠ 0 := fun h0 => hb (by rw [h0, zero_mul])
  have hc : c ≠ 0 := fun h0 => hb (by rw [h0, mul_zero])
  rw [integerValuation_mul E ha hc]
  have := integerValuation_nonneg E c
  omega

variable {π : ↥𝒪[K]} (hπ : Irreducible π) {n : ℕ}

include hπ in
/-- **The root-proximity pigeonhole**: at a `π`-primitive root `x` and a
`πu`-primitive root `y` in a common carrier, some root of the changed primitive
polynomial lies within the Krasner gap of `x` — equal to `x`, or at value at least
`qⁿ⁺¹ ν(x)`, strictly above the conjugate ceiling `qⁿ ν(x)` (Yamaguchi 2026,
`LocalFieldTheory/DiscreteValuationField/PolynomialRootProximity.lean:56` — the
general maximal-root estimate this proof fuses with its Lubin–Tate instantiation). -/
theorem standardLubinTateRootProximity
    {u : (↥𝒪[K])ˣ} (hu : u ∈ integerHigherUnitGroup K (n + 1))
    {x y : ↥𝒪[E]}
    (hrootx : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    (hrooty : Polynomial.aeval y
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] (π * (u : ↥𝒪[K])) n) = 0) :
    ∃ r ∈ ((standardLubinTatePrimitivePolynomial ↥𝒪[K] (π * (u : ↥𝒪[K])) n).map
        (algebraMap ↥𝒪[K] ↥𝒪[E])).roots,
      Polynomial.aeval r
          (standardLubinTatePrimitivePolynomial ↥𝒪[K] (π * (u : ↥𝒪[K])) n) = 0 ∧
        (x = r ∨ (Nat.card 𝓀[K] : ℤ) ^ (n + 1) * integerValuation E x ≤
          integerValuation E (x - r)) := by
  classical
  have hπ' : Irreducible (π * (u : ↥𝒪[K])) :=
    (Associated.irreducible_iff ⟨u, rfl⟩).mp hπ
  set p := (standardLubinTatePrimitivePolynomial ↥𝒪[K] (π * (u : ↥𝒪[K])) n).map
    (algebraMap ↥𝒪[K] ↥𝒪[E]) with hp
  have hmonic : p.Monic :=
    (standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] _ n).map _
  have hSplits : p.Splits :=
    standardLubinTatePrimitivePolynomial_map_splits K E hπ' hrooty
  have hcard := (standardLubinTateSplitting K E hπ' hrooty).1
  have hnodup := (standardLubinTateSplitting K E hπ' hrooty).2
  have hprim : ∀ r ∈ p.roots, Polynomial.aeval r
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] (π * (u : ↥𝒪[K])) n) = 0 := by
    intro r hr
    have := (Polynomial.mem_roots hmonic.ne_zero).mp hr
    rwa [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at this
  -- either `x` is itself a root, or every difference is nonzero
  by_cases hxroot : ∃ r ∈ p.roots, x = r
  · obtain ⟨r, hr, hxr⟩ := hxroot
    exact ⟨r, hr, hprim r hr, Or.inl hxr⟩
  have hne0 : ∀ r ∈ p.roots, x - r ≠ 0 := by
    intro r hr h0
    exact hxroot ⟨r, hr, by linear_combination h0⟩
  -- the evaluated product
  have heval : Polynomial.aeval x
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] (π * (u : ↥𝒪[K])) n) =
      (p.roots.map (x - ·)).prod := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← hp]
    exact hSplits.eval_eq_prod_roots_of_monic hmonic x
  have hprodne : (p.roots.map (x - ·)).prod ≠ 0 := by
    refine Multiset.prod_ne_zero ?_
    intro hmem
    obtain ⟨r, hr, hzero⟩ := Multiset.mem_map.mp hmem
    exact hne0 r hr hzero
  -- total value from the evaluation depth
  have hdepth := pow_dvd_aeval_changed_standardLubinTatePrimitivePolynomial K E hπ
    hrootx hu
  have hπE : algebraMap ↥𝒪[K] ↥𝒪[E] π ≠ 0 := algebraMap_pi_ne_zero K E hπ
  have htotal : ((n : ℤ) + 2) * integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) ≤
      ((p.roots.map (x - ·)).map (integerValuation E)).sum := by
    have h1 := integerValuation_le_of_dvd E (heval ▸ hprodne) hdepth
    rw [map_pow, integerValuation_pow E (algebraMap ↥𝒪[K] ↥𝒪[E] π)] at h1
    rw [heval] at h1
    rw [integerValuation_multiset_prod E _ (by
      intro z hz
      obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
      exact hne0 r hr)] at h1
    push_cast at h1
    exact h1
  -- the closest root
  have hD2 : 2 ≤ Nat.card 𝓀[K] := Finite.one_lt_card
  have hrootsne : p.roots ≠ 0 := by
    intro h0
    rw [h0, Multiset.card_zero] at hcard
    have : 0 < (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n :=
      Nat.mul_pos (by omega) (pow_pos (by omega) n)
    omega
  obtain ⟨r₀, hr₀mem, hmax⟩ := Multiset.exists_max_image (s := p.roots)
    (fun r => integerValuation E (x - r)) hrootsne
  refine ⟨r₀, hr₀mem, hprim r₀ hr₀mem, Or.inr ?_⟩
  -- split the total at `r₀`
  have hsplitsum : ((p.roots.map (x - ·)).map (integerValuation E)).sum =
      integerValuation E (x - r₀) +
        (((p.roots.erase r₀).map (x - ·)).map (integerValuation E)).sum := by
    conv_lhs => rw [← Multiset.cons_erase hr₀mem]
    rw [Multiset.map_cons, Multiset.map_cons, Multiset.sum_cons]
  -- each remaining distance is bounded by the distance to `r₀`'s cluster
  have hclusterbound : ∀ r ∈ p.roots.erase r₀,
      integerValuation E (x - r) ≤ integerValuation E (r₀ - r) := by
    intro r hr
    have hrne : r ≠ r₀ := (hnodup.mem_erase_iff.mp hr).1
    have hrmem : r ∈ p.roots := (hnodup.mem_erase_iff.mp hr).2
    have hd3 : r₀ - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrne)
    have hkey : r₀ - r = (r₀ - x) + (x - r) := by ring
    have hmin := min_le_integerValuation_add E (y := r₀ - x) (z := x - r)
      (by rw [← hkey]; exact hd3)
    rw [← hkey] at hmin
    have hneg : integerValuation E (r₀ - x) = integerValuation E (x - r₀) := by
      rw [show r₀ - x = -(x - r₀) by ring, integerValuation_neg]
    rw [hneg] at hmin
    have hmaxr := hmax r hrmem
    omega
  have hsumbound :
      (((p.roots.erase r₀).map (x - ·)).map (integerValuation E)).sum ≤
      (((p.roots.erase r₀).map (r₀ - ·)).map (integerValuation E)).sum := by
    rw [Multiset.map_map, Multiset.map_map]
    exact Multiset.sum_map_le_sum_map _ _ hclusterbound
  -- the cluster sum is the derivative value at `r₀`
  have hr₀root := hprim r₀ hr₀mem
  have hderiv : integerValuation E (Polynomial.aeval r₀ (Polynomial.derivative
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] (π * (u : ↥𝒪[K])) n))) =
      (((p.roots.erase r₀).map (r₀ - ·)).map (integerValuation E)).sum := by
    have hid := hSplits.eval_root_derivative hmonic hr₀mem
    have hlhs : Polynomial.aeval r₀ (Polynomial.derivative
        (standardLubinTatePrimitivePolynomial ↥𝒪[K] (π * (u : ↥𝒪[K])) n)) =
        Polynomial.eval r₀ p.derivative := by
      rw [hp, Polynomial.derivative_map, Polynomial.eval_map, Polynomial.aeval_def]
    rw [hlhs, hid]
    refine integerValuation_multiset_prod E _ ?_
    intro z hz
    obtain ⟨r, hr, rfl⟩ := Multiset.mem_map.mp hz
    have hrne : r ≠ r₀ := (hnodup.mem_erase_iff.mp hr).1
    exact sub_ne_zero.mpr (Ne.symm hrne)
  -- the derivative exponent at `r₀`
  have hexp := standardLubinTateDerivativeValuation K E hπ' hr₀root
  -- values of the two roots agree
  have hidx := standardLubinTatePrimitiveValuation K E hπ hrootx
  have hidr := standardLubinTatePrimitiveValuation K E hπ' hr₀root
  have hπ'E : integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] (π * (u : ↥𝒪[K]))) =
      integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) := by
    have huE : IsUnit (algebraMap ↥𝒪[K] ↥𝒪[E] (u : ↥𝒪[K])) := u.isUnit.map _
    rw [map_mul, integerValuation_mul E hπE huE.ne_zero,
      integerValuation_eq_zero_of_isUnit E huE, add_zero]
  have hpos : (0 : ℤ) < ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n := by
    have hq : (2 : ℤ) ≤ (Nat.card 𝓀[K] : ℤ) := by exact_mod_cast hD2
    exact mul_pos (by omega) (pow_pos (by omega) n)
  have hvals : integerValuation E r₀ = integerValuation E x := by
    rw [hπ'E] at hidr
    have := hidr.trans hidx.symm
    exact mul_left_cancel₀ hpos.ne' this
  -- assemble
  rw [hπ'E, hvals] at hexp
  have hfinal : 2 * integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) -
      ((Nat.card 𝓀[K] : ℤ) - 2) * (Nat.card 𝓀[K] : ℤ) ^ n * integerValuation E x =
      (Nat.card 𝓀[K] : ℤ) ^ (n + 1) * integerValuation E x := by
    rw [← hidx]
    ring
  linarith [htotal, hsplitsum, hsumbound, hderiv, hexp, hfinal]

include hπ in
/-- **The Krasner-ready form**: the root sits strictly beyond the conjugate ceiling
`qⁿ ν(x)` — the strict comparison the Krasner argument consumes (Yamaguchi 2026,
`LubinTate/FiniteLevel/HigherUnitLevelEquiv.lean:838` — the source's instantiated
strict form). -/
theorem standardLubinTateRootProximity_lt
    {u : (↥𝒪[K])ˣ} (hu : u ∈ integerHigherUnitGroup K (n + 1))
    {x y : ↥𝒪[E]}
    (hrootx : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    (hrooty : Polynomial.aeval y
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] (π * (u : ↥𝒪[K])) n) = 0) :
    ∃ r ∈ ((standardLubinTatePrimitivePolynomial ↥𝒪[K] (π * (u : ↥𝒪[K])) n).map
        (algebraMap ↥𝒪[K] ↥𝒪[E])).roots,
      Polynomial.aeval r
          (standardLubinTatePrimitivePolynomial ↥𝒪[K] (π * (u : ↥𝒪[K])) n) = 0 ∧
        (x = r ∨ (Nat.card 𝓀[K] : ℤ) ^ n * integerValuation E x <
          integerValuation E (x - r)) := by
  obtain ⟨r, hr, hrprim, hcase⟩ := standardLubinTateRootProximity K E hπ hu hrootx hrooty
  refine ⟨r, hr, hrprim, hcase.imp id fun h => ?_⟩
  have hq : (2 : ℤ) ≤ (Nat.card 𝓀[K] : ℤ) := by
    exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[K])
  have hπpos : 0 < integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) :=
    (integerValuation_pos_iff E (algebraMap_pi_ne_zero K E hπ)).mpr
      (algebraMap_irreducible_mem_maximalIdeal K E hπ)
  have hidx := standardLubinTatePrimitiveValuation K E hπ hrootx
  have hpn : (0 : ℤ) < (Nat.card 𝓀[K] : ℤ) ^ n := pow_pos (by omega) n
  have hd : (0 : ℤ) < ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n :=
    mul_pos (by omega) hpn
  have hxpos : 0 < integerValuation E x := by
    by_contra hle
    rw [not_lt] at hle
    nlinarith [hidx, hπpos, hd, hle]
  have : (Nat.card 𝓀[K] : ℤ) ^ n * integerValuation E x <
      (Nat.card 𝓀[K] : ℤ) ^ (n + 1) * integerValuation E x := by
    rw [pow_succ]
    nlinarith
  linarith

end Proximity

end Atlas.Knowledge
