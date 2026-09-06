import Mathlib
import Atlas.Knowledge.IntegerValuation
import Atlas.Knowledge.StandardLubinTateTorsion

/-!
# standard Lubin–Tate primitive valuation

The valuation bootstrap at a primitive root: over any carrier extension, the iterate
values `t_i = f^[i](x)` at a root `x` of the level-`n + 1` primitive polynomial have
integer valuation `ν(t_i) = qⁱ ν(x)`, and the top identity `t_n^{q−1} = −π` closes the
system into `(q − 1) qⁿ ν(x) = ν(π)` — the abstract form of total ramification of the
level tower. Instantiated at the level field, where the degree bounds `ν(π)` above,
this forces `ν(x) = 1` — the primitive root is a uniformizer — which is the engine of
the derivative-valuation computation ahead.

## Main statements

* `integerValuation_aeval_standardLubinTatePolynomialIterate` — `ν(t_i) = qⁱ ν(x)` at
  every level `i ≤ n`; proved.
* `standardLubinTatePrimitiveValuation` — `(q − 1) qⁿ ν(x) = ν(π)`; proved.
* `le_integerValuation_algebraMap_pi` — the lower half of the pin,
  `(q − 1) qⁿ ≤ ν(π)`; proved.

## Implementation notes

The source reaches these values through the Eisenstein polynomial itself: the
primitive polynomial is Eisenstein at `𝔪`, hence irreducible, and the level field is
the one simple extension it cuts out; the valuation of the generator is then forced by
comparing the constant coefficient's filtration depth against the middle ones, with the
fundamental identity supplying the degree — Milne's tower `K[π_n] ⊃ ⋯ ⊃ K` is the
book's route, not the source's. This item replaces the coefficient comparison with a
self-contained ultrametric squeeze on the recursion `t_{i+1} = t_i^q + π t_i`: a level
whose `(q − 1)`-multiple is bounded by `ν(π)` forces a strictly bounded level below —
otherwise both summands sit too high and the exact top level is overshot — so the bound
descends from the top identity to every level, and the recursion then reads off
`ν(t_{i+1}) = q ν(t_i)` exactly. No Eisenstein middle coefficients are ever computed,
in the same spirit as the prime-descent membership of
`Atlas.Knowledge.mem_maximalIdeal_of_aeval_primitive`. The identity is stated over the
abstract carrier, where `ν(x)` is a free parameter; the lower half of the pin —
`(q − 1) qⁿ ≤ ν(π)`, at least total ramification — is free here as
`le_integerValuation_algebraMap_pi`, while pinning `ν(x) = 1` exactly needs the
fundamental inequality against the level degree and arrives with the level-field
instantiation.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

section PrimitiveValuation

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [Algebra K E]
  [ValuativeExtension K E] [IsMixedCharLocalField E]
variable {π : ↥𝒪[K]} (hπ : Irreducible π) {n : ℕ} {x : ↥𝒪[E]}

omit [TopologicalSpace E] [IsMixedCharLocalField E] in
/-- The evaluated recursion `t_{i+1} = t_i^q + π t_i`. -/
private theorem aeval_iterate_succ (i : ℕ) :
    Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π (i + 1)) =
      Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ^
          Nat.card 𝓀[K] +
        algebraMap ↥𝒪[K] ↥𝒪[E] π *
          Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i) := by
  rw [standardLubinTatePolynomialIterate_succ, Polynomial.aeval_comp,
    standardLubinTatePolynomial]
  rw [map_add, map_pow, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]

omit [TopologicalSpace E] [IsMixedCharLocalField E] in
/-- A vanishing iterate value stays zero from then on. -/
private theorem aeval_iterate_eq_zero_add {i : ℕ}
    (h0 : Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i) = 0)
    (k : ℕ) :
    Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π (i + k)) = 0 := by
  induction k with
  | zero => simpa using h0
  | succ k ih =>
    have hq : Nat.card 𝓀[K] ≠ 0 := by
      have : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
      omega
    rw [show i + (k + 1) = (i + k) + 1 by omega, aeval_iterate_succ K E, ih]
    simp [hq]

omit [TopologicalSpace E] [IsMixedCharLocalField E] in
include hπ in
/-- Below the level, no iterate value vanishes. -/
private theorem aeval_iterate_ne_zero_of_le
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    {i : ℕ} (hi : i ≤ n) :
    Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ≠ 0 := by
  intro h0
  refine aeval_standardLubinTatePolynomialIterate_ne_zero K E hπ hroot ?_
  have := aeval_iterate_eq_zero_add K E h0 (n - i)
  rwa [Nat.add_sub_cancel' hi] at this

omit [TopologicalSpace E] [IsMixedCharLocalField E] in
/-- The top identity: the `n`-th iterate's `q − 1`-st power is `−π`. -/
private theorem aeval_iterate_top_pow
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0) :
    Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π n) ^
        (Nat.card 𝓀[K] - 1) =
      -(algebraMap ↥𝒪[K] ↥𝒪[E] π) := by
  have h := hroot
  rw [standardLubinTatePrimitivePolynomial, map_add, map_pow, Polynomial.aeval_C] at h
  exact eq_neg_of_add_eq_zero_left h

include hπ in
/-- The descending bound: a controlled level forces a strictly controlled level below —
otherwise both summands of the recursion sit above the uniformizer, and the next level
overshoots. -/
private theorem descending_bound
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    {i : ℕ} (hi : i + 1 ≤ n)
    (hle : ((Nat.card 𝓀[K] : ℤ) - 1) *
        integerValuation E (Polynomial.aeval x
          (standardLubinTatePolynomialIterate ↥𝒪[K] π (i + 1))) ≤
      integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π)) :
    ((Nat.card 𝓀[K] : ℤ) - 1) *
        integerValuation E (Polynomial.aeval x
          (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) <
      integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) := by
  set q := Nat.card 𝓀[K] with hq
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hπE : algebraMap ↥𝒪[K] ↥𝒪[E] π ≠ 0 := algebraMap_pi_ne_zero K E hπ
  have hπEpos : 0 < integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) :=
    (integerValuation_pos_iff E hπE).mpr
      (algebraMap_irreducible_mem_maximalIdeal K E hπ)
  have hti : Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ≠ 0 :=
    aeval_iterate_ne_zero_of_le K E hπ hroot (by omega)
  have hti1 : Polynomial.aeval x
      (standardLubinTatePolynomialIterate ↥𝒪[K] π (i + 1)) ≠ 0 :=
    aeval_iterate_ne_zero_of_le K E hπ hroot hi
  by_contra hnot
  rw [not_lt] at hnot
  -- both summands of the recursion are at least `ν(t_i) + ν(π)`
  have hpow : integerValuation E (Polynomial.aeval x
      (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ^ q) =
      q * integerValuation E (Polynomial.aeval x
        (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) :=
    integerValuation_pow E _ q
  have hmul : integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π *
      Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) =
      integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) +
        integerValuation E (Polynomial.aeval x
          (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) :=
    integerValuation_mul E hπE hti
  have hmin := min_le_integerValuation_add E
    (by rw [← aeval_iterate_succ K E]; exact hti1)
  rw [hpow, hmul, ← aeval_iterate_succ K E] at hmin
  -- the successor level is at least `ν(t_i) + ν(π)`, so its multiple exceeds `ν(π)`
  have hits : integerValuation E (Polynomial.aeval x
        (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) +
        integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) ≤
      integerValuation E (Polynomial.aeval x
        (standardLubinTatePolynomialIterate ↥𝒪[K] π (i + 1))) := by
    have hq1 : (1 : ℤ) ≤ (q : ℤ) - 1 := by
      have : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq2
      omega
    have hqmul : integerValuation E (Polynomial.aeval x
          (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) +
          integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) ≤
        (q : ℤ) * integerValuation E (Polynomial.aeval x
          (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) := by
      have hsplit : (q : ℤ) * integerValuation E (Polynomial.aeval x
          (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) =
          integerValuation E (Polynomial.aeval x
            (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) +
            ((q : ℤ) - 1) * integerValuation E (Polynomial.aeval x
              (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) := by ring
      omega
    omega
  -- multiply out and contradict the controlled successor level
  have hmono := mul_le_mul_of_nonneg_left hits (by omega : (0 : ℤ) ≤ (q : ℤ) - 1)
  have hexp : ((q : ℤ) - 1) * (integerValuation E (Polynomial.aeval x
      (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) +
        integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π)) =
      ((q : ℤ) - 1) * integerValuation E (Polynomial.aeval x
        (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) +
        ((q : ℤ) - 1) * integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) := by ring
  have hq2' : (2 : ℤ) ≤ (q : ℤ) := by exact_mod_cast hq2
  nlinarith [hπEpos]

/-- The exact top level: `(q − 1) ν(t_n) = ν(π)`. -/
private theorem top_level_eq
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0) :
    ((Nat.card 𝓀[K] : ℤ) - 1) *
        integerValuation E (Polynomial.aeval x
          (standardLubinTatePolynomialIterate ↥𝒪[K] π n)) =
      integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) := by
  have h2 : integerValuation E (Polynomial.aeval x
      (standardLubinTatePolynomialIterate ↥𝒪[K] π n) ^ (Nat.card 𝓀[K] - 1)) =
      integerValuation E (-(algebraMap ↥𝒪[K] ↥𝒪[E] π)) := by
    rw [aeval_iterate_top_pow K E hroot]
  rw [integerValuation_pow E _, integerValuation_neg] at h2
  have hq2 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  rw [Nat.cast_sub (by omega : 1 ≤ Nat.card 𝓀[K])] at h2
  push_cast at h2 ⊢
  exact h2

include hπ in
/-- Every level is bounded by the uniformizer's value: the descending bound carries the
top equality down. -/
private theorem level_bound
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    {i : ℕ} (hi : i ≤ n) :
    ((Nat.card 𝓀[K] : ℤ) - 1) *
        integerValuation E (Polynomial.aeval x
          (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) ≤
      integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) := by
  have aux : ∀ k, k ≤ n → ((Nat.card 𝓀[K] : ℤ) - 1) *
      integerValuation E (Polynomial.aeval x
        (standardLubinTatePolynomialIterate ↥𝒪[K] π (n - k))) ≤
      integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa using le_of_eq (top_level_eq K E hroot)
    | succ k ih =>
      intro hk
      have hik := ih (by omega)
      have hsucc : (n - (k + 1)) + 1 = n - k := by omega
      have := descending_bound K E hπ hroot
        (i := n - (k + 1)) (by omega) (by rw [hsucc]; exact hik)
      exact this.le
  have := aux (n - i) (by omega)
  rwa [show n - (n - i) = i by omega] at this

include hπ in
/-- Below the top, the bound is strict. -/
private theorem level_bound_lt
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    {i : ℕ} (hi : i < n) :
    ((Nat.card 𝓀[K] : ℤ) - 1) *
        integerValuation E (Polynomial.aeval x
          (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) <
      integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) :=
  descending_bound K E hπ hroot (by omega) (level_bound K E hπ hroot (by omega))

include hπ in
/-- **The iterate valuations at a primitive root**: `ν(t_i) = qⁱ ν(x)` for `i ≤ n` —
each application of the standard polynomial multiplies the valuation by `q`, because
below the top the `q`-power summand of the recursion sits strictly under the `π`-summand
([Milne 2020, Chap. I, §3, the proof of Thm. 3.6 and Summary 3.7, pp.38–39][MilneCFT];
Yamaguchi 2026, `LubinTate/FiniteLevel/CompletedIterates.lean:73`). -/
theorem integerValuation_aeval_standardLubinTatePolynomialIterate
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    {i : ℕ} (hi : i ≤ n) :
    integerValuation E (Polynomial.aeval x
        (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) =
      (Nat.card 𝓀[K] : ℤ) ^ i * integerValuation E x := by
  induction i with
  | zero =>
    simp [standardLubinTatePolynomialIterate_zero, Polynomial.aeval_X]
  | succ i ih =>
    have hπE : algebraMap ↥𝒪[K] ↥𝒪[E] π ≠ 0 := algebraMap_pi_ne_zero K E hπ
    have hti : Polynomial.aeval x
        (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ≠ 0 :=
      aeval_iterate_ne_zero_of_le K E hπ hroot (by omega)
    have hstrict := level_bound_lt K E hπ hroot (by omega : i < n)
    have hlt : integerValuation E (Polynomial.aeval x
        (standardLubinTatePolynomialIterate ↥𝒪[K] π i) ^ Nat.card 𝓀[K]) <
        integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π *
          Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) := by
      rw [integerValuation_pow E _, integerValuation_mul E hπE hti]
      have hsplit : (Nat.card 𝓀[K] : ℤ) * integerValuation E (Polynomial.aeval x
          (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) =
          integerValuation E (Polynomial.aeval x
            (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) +
            ((Nat.card 𝓀[K] : ℤ) - 1) * integerValuation E (Polynomial.aeval x
              (standardLubinTatePolynomialIterate ↥𝒪[K] π i)) := by
        ring
      linarith [hsplit, hstrict]
    rw [aeval_iterate_succ K E,
      integerValuation_add_of_lt E (pow_ne_zero _ hti) hlt,
      integerValuation_pow E _, ih (by omega)]
    ring

include hπ in
/-- **The primitive valuation identity**: `(q − 1) qⁿ ν(x) = ν(π)` at a level-`n + 1`
primitive root in any carrier — the abstract form of total ramification of the level
tower, closed from the iterate valuations by the top identity `t_n^{q−1} = −π`
([Milne 2020, Chap. I, §3, Thm. 3.6 (a) and its proof, pp.38–39][MilneCFT];
Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveUniformizer.lean:811`). -/
theorem standardLubinTatePrimitiveValuation
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0) :
    ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n * integerValuation E x =
      integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) := by
  have h1 := top_level_eq K E hroot
  rw [integerValuation_aeval_standardLubinTatePolynomialIterate K E hπ hroot le_rfl,
    ← mul_assoc] at h1
  exact h1

include hπ in
/-- **The lower half of the pin**: `(q − 1) qⁿ ≤ ν(π)` — the extension carrying a
level-`n + 1` primitive root is at least totally ramified, read off the identity and
`ν(x) ≥ 1` ([Milne 2020, Chap. I, §3, Thm. 3.6 (a), pp.38–39][MilneCFT]). -/
theorem le_integerValuation_algebraMap_pi
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0) :
    ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n ≤
      integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) := by
  have hπE : algebraMap ↥𝒪[K] ↥𝒪[E] π ≠ 0 := algebraMap_pi_ne_zero K E hπ
  have hπpos : 0 < integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) :=
    (integerValuation_pos_iff E hπE).mpr (algebraMap_irreducible_mem_maximalIdeal K E hπ)
  have hq : (2 : ℤ) ≤ (Nat.card 𝓀[K] : ℤ) := by
    exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[K])
  have hD : (0 : ℤ) < ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n :=
    mul_pos (by omega) (pow_pos (by omega) n)
  have hid := standardLubinTatePrimitiveValuation K E hπ hroot
  have hx1 : 1 ≤ integerValuation E x := by
    by_contra hcon
    rw [not_le] at hcon
    have hnp : ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n *
        integerValuation E x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hD.le (by omega)
    rw [hid] at hnp
    omega
  calc ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n
      = ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n * 1 := by ring
    _ ≤ ((Nat.card 𝓀[K] : ℤ) - 1) * (Nat.card 𝓀[K] : ℤ) ^ n * integerValuation E x :=
        mul_le_mul_of_nonneg_left hx1 hD.le
    _ = integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) := hid

end PrimitiveValuation

end Atlas.Knowledge
