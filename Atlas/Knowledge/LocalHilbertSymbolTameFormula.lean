import Mathlib
import Atlas.Knowledge.IsLocalHilbertSymbol
import Atlas.Knowledge.NormalizedValuation

/-!
# tame formula for the local Hilbert symbol

The explicit computation of the Hilbert symbol when `n` is prime to the residue
characteristic: with `α = v (a)` and `β = v (b)` for `v` the normalized valuation, the unit
`c = (-1) ^ (α β) · a ^ β / b ^ α` reduces to a residue class whose `(q - 1) / n`-th power is
the symbol. The formula is stated as a congruence — the symbol and `c ^ ((q - 1) / n)` differ
by an element of valuation less than one — and the two facts that give the congruence its
force are proved here: reduction is injective on tame roots of unity, so the congruence pins
the symbol exactly, and `n` divides `q - 1`, so the exponent is the integer the literature
writes. The formula itself is the recorded claim.

## Main statements

* `localHilbertSymbol_tame_formula` — Serre's tame formula in congruence form, recorded
  ahead of its proof.
* `eq_one_of_pow_eq_one_of_valuation_sub_one_lt` — a tame `n`-th root of unity congruent to
  `1` is `1`: reduction is injective on `μ_n`, which is what makes the congruence above an
  exact determination.
* `dvd_card_residueField_sub_one` — `n ∣ q - 1` once `K` contains the `n`-th roots of unity
  and `n` is a unit.
* `valuation_eq_one_of_pow_eq_one` — roots of unity are valuation-one, the fact feeding both.

## Implementation notes

Tameness is rendered as `valuation K (n : K) = 1` — `n` a unit of the integer ring — the
same reading the source takes. The congruence form avoids constructing the reduction
isomorphism `μ_n (K) ≃ μ_n (𝓀)` of the literature: Serre's statement passes through the
multiplicative-representative identification, and `v (x - y) < 1` says exactly that `x`
reduces to `y`'s residue without naming the lift. The exponent orientation is Serre's
Prop. 8 read against the *arithmetic* normalization both this layer and the literature fix.
The source's only tame statement
(`LocalClassFieldTheory/Kummer/PowerResidueTameFormula.lean:937`) is the unit-first special
case — its first slot is a valuation-ring unit, so the `(-1)` factor and the `b ^ (- v a)`
term are invisible in it, and the general orientation rests on Serre alone, the reduction to
uniformizers of Prop. 8's proof included. On that sub-case the formulas agree: the source's
two departures — transposed slots and inverted Artin normalization, recorded in
`Atlas.Knowledge.IsLocalHilbertSymbol`'s notes — cancel by skew-symmetry, and its exponent
`- valuationMap` is already the standard valuation, with nothing left to reconcile. The
injectivity proof needs no ultrametric dominance: from `(1 + x) ^ n = 1` the binomial
expansion factors as `x · (n + x · S) = 0` with `S` integral, forcing `v (n) ≤ v (x) < 1`
outright.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section ValuationLemmas

variable (K : Type*) [Field K] [ValuativeRel K]

/-- Roots of unity have valuation one: the value group is torsion-free away from zero
([Serre 1979, Chap. XIV, §3, p.210][Serre1979]). -/
theorem valuation_eq_one_of_pow_eq_one {ζ : K} {n : ℕ} (hn : n ≠ 0) (hζ : ζ ^ n = 1) :
    valuation K ζ = 1 := by
  have h : (valuation K ζ) ^ n = 1 := by rw [← map_pow, hζ, map_one]
  exact (pow_eq_one_iff.mp h).resolve_right hn

private theorem valuation_natCast_le_one (m : ℕ) : valuation K ((m : ℕ) : K) ≤ 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
    push_cast
    exact le_trans ((valuation K).map_add _ _) (max_le ih (by simp))

/-- Reduction is injective on tame roots of unity: when `n` is a unit, an `n`-th root of
unity congruent to `1` is `1`. This is what lets a congruence determine the Hilbert symbol
exactly ([Serre 1979, Chap. XIV, §3, Lemma 1, p.210][Serre1979]). -/
theorem eq_one_of_pow_eq_one_of_valuation_sub_one_lt {n : ℕ}
    (hn : valuation K ((n : ℕ) : K) = 1) {ζ : K} (hζ : ζ ^ n = 1)
    (hlt : valuation K (ζ - 1) < 1) : ζ = 1 := by
  by_contra hne
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  set x : K := ζ - 1 with hxdef
  have hx0 : x ≠ 0 := sub_ne_zero.mpr hne
  set S : K := ∑ k ∈ Finset.Ico 2 (n + 1), (n.choose k : K) * x ^ (k - 2) with hSdef
  have key : ∑ k ∈ Finset.range (n + 1), x ^ k * (n.choose k : K)
      = 1 + x * ((n : K) + x * S) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega),
      Finset.sum_eq_sum_Ico_succ_bot (by omega)]
    have hsum : ∑ k ∈ Finset.Ico 2 (n + 1), x ^ k * (n.choose k : K) = x ^ 2 * S := by
      rw [hSdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk2 := (Finset.mem_Ico.mp hk).1
      rw [show x ^ k = x ^ 2 * x ^ (k - 2) by rw [← pow_add]; congr 1; omega]
      ring
    rw [hsum]
    simp [Nat.choose_one_right]
    ring
  have hpow : (x + 1) ^ n = ∑ k ∈ Finset.range (n + 1), x ^ k * (n.choose k : K) := by
    rw [add_pow]
    simp
  have hone : (x + 1) ^ n = 1 := by
    rw [hxdef, sub_add_cancel]
    exact hζ
  have hzero : x * ((n : K) + x * S) = 0 := by
    have h1 := hpow.symm.trans hone
    rw [key] at h1
    linear_combination h1
  have hcast : ((n : ℕ) : K) = -(x * S) := by
    have h2 := (mul_eq_zero.mp hzero).resolve_left hx0
    linear_combination h2
  have hS1 : valuation K S ≤ 1 := by
    refine Valuation.map_sum_le _ fun k hk => ?_
    rw [map_mul, map_pow]
    exact mul_le_one' (valuation_natCast_le_one K _) (pow_le_one' hlt.le _)
  have hfinal : valuation K ((n : ℕ) : K) < 1 := by
    rw [hcast, Valuation.map_neg, map_mul]
    calc valuation K x * valuation K S ≤ valuation K x * 1 := mul_le_mul' le_rfl hS1
      _ = valuation K x := mul_one _
      _ < 1 := hlt
  rw [hn] at hfinal
  exact absurd hfinal (lt_irrefl 1)

end ValuationLemmas

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- When `K` contains the `n`-th roots of unity and `n` is a unit, `n` divides `q - 1`: the
`n` roots of unity reduce injectively into the residue units, and Lagrange counts. This is
what makes the exponent `(q - 1) / n` of the tame formula the literature's integer
([Serre 1979, Chap. XIV, §3, Example, p.210][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Kummer/PowerResidueTameFormula.lean:380`). -/
theorem dvd_card_residueField_sub_one {n : ℕ} (hn : valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots n K).Nonempty) : n ∣ Nat.card 𝓀[K] - 1 := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  haveI : NeZero n := ⟨hn0⟩
  obtain ⟨ζ₀, hζ₀⟩ := hmu
  have hprim : IsPrimitiveRoot ζ₀ n := (mem_primitiveRoots (Nat.pos_of_ne_zero hn0)).mp hζ₀
  have hpow : ∀ ζ : rootsOfUnity n K, ((ζ : Kˣ) : K) ^ n = 1 := by
    intro ζ
    have h := ζ.2
    rw [mem_rootsOfUnity] at h
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hmem : ∀ ζ : rootsOfUnity n K, ((ζ : Kˣ) : K) ∈ 𝒪[K] := fun ζ =>
    (Valuation.mem_integer_iff _ _).mpr (valuation_eq_one_of_pow_eq_one K hn0 (hpow ζ)).le
  let toInt : rootsOfUnity n K →* 𝒪[K] :=
    { toFun := fun ζ => ⟨((ζ : Kˣ) : K), hmem ζ⟩
      map_one' := by ext; simp
      map_mul' := fun ζ₁ ζ₂ => by ext; simp }
  let red : rootsOfUnity n K →* 𝓀[K] :=
    (IsLocalRing.residue 𝒪[K]).toMonoidHom.comp toInt
  have hinj : Function.Injective red.toHomUnits := by
    intro ζ₁ ζ₂ hred
    have hval : red ζ₁ = red ζ₂ := by
      have := congrArg Units.val hred
      simpa only [MonoidHom.coe_toHomUnits] using this
    have h1 : IsLocalRing.residue 𝒪[K] (toInt ζ₁ - toInt ζ₂) = 0 := by
      rw [map_sub]
      simp only [red, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe,
        MonoidHom.coe_coe] at hval
      rw [hval, sub_self]
    have hsub : (toInt ζ₁ - toInt ζ₂ : 𝒪[K]) ∈ 𝓂[K] :=
      (IsLocalRing.residue_eq_zero_iff _).mp h1
    have hne1 : valuation K ((toInt ζ₁ - toInt ζ₂ : 𝒪[K]) : K) ≠ 1 := fun heq =>
      (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hsub))
        ((Valuation.integer.integers (valuation K)).isUnit_iff_valuation_eq_one.mpr heq)
    have hle1 : valuation K ((toInt ζ₁ - toInt ζ₂ : 𝒪[K]) : K) ≤ 1 :=
      (Valuation.mem_integer_iff _ _).mp (toInt ζ₁ - toInt ζ₂).2
    have hlt : valuation K (((ζ₁ : Kˣ) : K) - ((ζ₂ : Kˣ) : K)) < 1 := by
      have hcoe : ((toInt ζ₁ - toInt ζ₂ : 𝒪[K]) : K)
          = ((ζ₁ : Kˣ) : K) - ((ζ₂ : Kˣ) : K) := rfl
      rw [hcoe] at hne1 hle1
      exact lt_of_le_of_ne hle1 hne1
    have hζ₂0 : ((ζ₂ : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have hw_pow : ((((ζ₁ : Kˣ) * (ζ₂ : Kˣ)⁻¹) : Kˣ) : K) ^ n = 1 := by
      have h2 : ((((ζ₂ : Kˣ)⁻¹ : Kˣ) : K)) ^ n = 1 := by
        rw [Units.val_inv_eq_inv_val, inv_pow, hpow ζ₂, inv_one]
      rw [Units.val_mul, mul_pow, hpow ζ₁, h2, one_mul]
    have hw_lt : valuation K (((((ζ₁ : Kˣ) * (ζ₂ : Kˣ)⁻¹) : Kˣ) : K) - 1) < 1 := by
      have hfactor : ((((ζ₁ : Kˣ) * (ζ₂ : Kˣ)⁻¹) : Kˣ) : K) - 1
          = (((ζ₁ : Kˣ) : K) - ((ζ₂ : Kˣ) : K)) * (((ζ₂ : Kˣ) : K))⁻¹ := by
        rw [Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp
      have hv2 : valuation K ((((ζ₂ : Kˣ) : K))⁻¹) = 1 := by
        refine valuation_eq_one_of_pow_eq_one K hn0 ?_
        rw [inv_pow, hpow ζ₂, inv_one]
      rw [hfactor, map_mul, hv2, mul_one]
      exact hlt
    have hw : ((((ζ₁ : Kˣ) * (ζ₂ : Kˣ)⁻¹) : Kˣ) : K) = 1 :=
      eq_one_of_pow_eq_one_of_valuation_sub_one_lt K hn hw_pow hw_lt
    have hu : ((ζ₁ : Kˣ) * (ζ₂ : Kˣ)⁻¹) = 1 := Units.ext (by rw [hw, Units.val_one])
    exact Subtype.ext (mul_inv_eq_one.mp hu)
  have hdvd := Subgroup.card_dvd_of_injective red.toHomUnits hinj
  rw [hprim.card_rootsOfUnity, Nat.card_units] at hdvd
  exact hdvd

/-- **The tame formula**: when `n` is a unit and `K` contains the `n`-th roots of unity, the
Hilbert symbol `(a, b)` is congruent modulo the maximal ideal to
`((-1) ^ (v a · v b) · a ^ v b · b ^ (- v a)) ^ ((q - 1) / n)` — Serre's
`c = (-1)^{αβ} a^β / b^α` raised to `(q - 1) / n`, read through the reduction that
`eq_one_of_pow_eq_one_of_valuation_sub_one_lt` makes exact. Claim recorded ahead of its
proof ([Serre 1979, Chap. XIV, §3, Prop. 8 and Cor., pp.210–211][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Kummer/PowerResidueTameFormula.lean:937`, the unit-first special
case). -/
theorem localHilbertSymbol_tame_formula {n : ℕ} {h : Kˣ → Kˣ → Kˣ}
    (hh : IsLocalHilbertSymbol K n h) (hn : valuation K ((n : ℕ) : K) = 1)
    (hmu : (primitiveRoots n K).Nonempty) (a b : Kˣ) :
    valuation K
      (((h a b : Kˣ) : K) -
        ((((-1 : Kˣ) ^ (normalizedValuation K a * normalizedValuation K b) *
            a ^ normalizedValuation K b * b ^ (- normalizedValuation K a)) ^
              ((Nat.card 𝓀[K] - 1) / n) : Kˣ) : K)) < 1 := by
  sorry

end Atlas.Knowledge
