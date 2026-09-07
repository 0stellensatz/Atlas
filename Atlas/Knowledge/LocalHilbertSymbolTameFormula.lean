import Mathlib
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.HigherUnitGroupCongruence
import Atlas.Knowledge.IsLocalHilbertSymbol
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LocalHilbertSymbolSkewSymmetry
import Atlas.Knowledge.LocalHilbertSymbolUnitUniformizer
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.ValuationEqOneOfPowEqOne

/-!
# tame formula for the local Hilbert symbol

The explicit computation of the Hilbert symbol when `n` is prime to the residue
characteristic: with `α = v (a)` and `β = v (b)` for `v` the normalized valuation, the unit
`c = (-1) ^ (α β) · a ^ β / b ^ α` reduces to a residue class whose `(q - 1) / n`-th power is
the symbol. The formula is stated as a congruence — the symbol and `c ^ ((q - 1) / n)` differ
by an element of valuation less than one — and the two facts that give the congruence its
force are proved here: reduction is injective on tame roots of unity, so the congruence pins
the symbol exactly, and `n` divides `q - 1`, so the exponent is the integer the literature
writes. The formula itself is proved, by Serre's reduction: the unit-against-uniformizer case
is `Atlas.Knowledge.LocalHilbertSymbolUnitUniformizer`, the Frobenius congruence on the
unramified Kummer field, and bimultiplicativity with the skew-symmetry of
`Atlas.Knowledge.LocalHilbertSymbolSkewSymmetry` carry it to every pair, the congruences
travelling as memberships in the first higher unit group.

## Main statements

* `localHilbertSymbol_tame_formula` — Serre's tame formula in congruence form; proved.
* `eq_one_of_pow_eq_one_of_valuation_sub_one_lt` — a tame `n`-th root of unity congruent to
  `1` is `1`: reduction is injective on `μ_n`, which is what makes the congruence above an
  exact determination.
* `dvd_card_residueField_sub_one` — `n ∣ q - 1` once `K` contains the `n`-th roots of unity
  and `n` is a unit.

## Implementation notes

Tameness is rendered as `valuation K (n : K) = 1` — `n` a unit of the integer ring — the same
reading the source takes. The congruence form avoids constructing the reduction isomorphism
`μ_n (K) ≃ μ_n (𝓀)` of the literature: Serre's statement passes through the
multiplicative-representative identification, and `v (x - y) < 1` says exactly that `x`
reduces to `y`'s residue without naming the lift. The exponent orientation is Serre's Prop. 8
read against the *arithmetic* normalization both this layer and the literature fix. The
source's only general tame formula
(`LocalClassFieldTheory/Kummer/PowerResidueTameFormula.lean:937`) is the unit-first special
case — its first slot is a valuation-ring unit, so the `(-1)` factor and the `b ^ (- v a)`
term are invisible in it, and the general orientation rests on Serre alone, the reduction to
uniformizers of Prop. 8's proof included. That reduction is how the general form is proved
here: a uniformizer `ϖ` splits `a = u_a ϖ ^ α` and `b = u_b ϖ ^ β`, the symbol is the product
`(u_a, u_b) (u_a, ϖ) ^ β (ϖ, u_b) ^ α (ϖ, ϖ) ^ (α β)` by `zpow`-bimultiplicativity, and the
four factors are congruent to `1`, `(u_a ^ k) ^ β`, `(u_b ^ k) ^ (-α)` and
`((-1) ^ k) ^ (α β)` with `k = (q - 1) / n` — the unit-against-uniformizer congruence at `ϖ`
and at `ϖ u_b` for the first, `Atlas.Knowledge.IsLocalHilbertSymbol.skew` for the third, and
`(ϖ, ϖ) = (-1, ϖ)` from `Atlas.Knowledge.IsLocalHilbertSymbol.neg_self` with `skew` for the
last. The congruences are carried as memberships `x⁻¹ * y ∈ U 1 (K)` through
`Atlas.Knowledge.HigherUnitGroupCongruence`, so that products, inverses and integer powers of
congruences are subgroup closure and the final identity is associativity and commutativity
alone; the unit parts are introduced as opaque variables with their defining equations, since
`set` lets `rw` see through them and match the bimultiplicativity lemmas inside their bodies.
On that sub-case the formulas agree: the source's two departures — transposed slots and
inverted Artin normalization, recorded in `Atlas.Knowledge.IsLocalHilbertSymbol`'s notes —
cancel by skew-symmetry, and its exponent `- valuationMap` is already the standard valuation,
with nothing left to reconcile. The injectivity proof needs no ultrametric dominance: from
`(1 + x) ^ n = 1` the binomial expansion factors as `x · (n + x · S) = 0` with `S` integral,
forcing `v (n) ≤ v (x) < 1` outright. That roots of unity have valuation one is
`Atlas.Knowledge.ValuationEqOneOfPowEqOne`, an item below this one and the unit-uniformizer
item, which both consume it.

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
`eq_one_of_pow_eq_one_of_valuation_sub_one_lt` makes exact. Proved by Serre's reduction to a
unit against a uniformizer, `Atlas.Knowledge.localHilbertSymbol_unit_uniformizer`, through
bimultiplicativity and skew-symmetry
([Serre 1979, Chap. XIV, §3, Prop. 8 and Cor., pp.210–211][Serre1979]; Yamaguchi 2026,
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
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hn
  set k := (Nat.card 𝓀[K] - 1) / n with hkdef
  -- the values of the symbol are units of the integers
  have hval : ∀ x y : Kˣ, valuation K ((h x y : Kˣ) : K) = 1 := fun x y =>
    valuation_eq_one_of_pow_eq_one K hn0
      (by rw [← Units.val_pow_eq_pow_val, IsLocalHilbertSymbol.pow_eq_one hh hn0 x y,
        Units.val_one])
  set U := higherUnitGroup K 1 with hUdef
  have hcong : ∀ x y : Kˣ, valuation K (x : K) = 1 →
      (valuation K ((x : K) - y) < 1 ↔ x⁻¹ * y ∈ U) := fun x y hx =>
    (inv_mul_mem_higherUnitGroup_one_iff K x y hx).symm
  -- the symbol is bimultiplicative, hence `zpow`-multiplicative in each slot
  have hR : ∀ (x y : Kˣ) (m : ℤ), h x (y ^ m) = h x y ^ m := fun x y m =>
    map_zpow (MonoidHom.mk' (h x) (IsLocalHilbertSymbol.mul_right hh hn0 x)) y m
  have hL : ∀ (x y : Kˣ) (m : ℤ), h (x ^ m) y = h x y ^ m := fun x y m =>
    map_zpow (MonoidHom.mk' (fun x => h x y)
      (fun x x' => IsLocalHilbertSymbol.mul_left hh hn0 x x' y)) x m
  -- a uniformizer, and the unit parts of `a` and `b`
  obtain ⟨ϖ, hϖ⟩ := normalizedValuation_surjective K 1
  set α := normalizedValuation K a with hαdef
  set β := normalizedValuation K b with hβdef
  have hunit : ∀ x : Kˣ, normalizedValuation K x = 0 → valuation K (x : K) = 1 := fun x hx =>
    (mem_ker_normalizedValuationHom K x).mp (by
      rw [MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [toAdd_normalizedValuationHom, hx]
      rfl)
  obtain ⟨ua, hua_def⟩ : ∃ ua : Kˣ, ua = a * ϖ ^ (-α) := ⟨_, rfl⟩
  obtain ⟨ub, hub_def⟩ : ∃ ub : Kˣ, ub = b * ϖ ^ (-β) := ⟨_, rfl⟩
  have hua : valuation K (ua : K) = 1 := hunit ua (by
    rw [hua_def, normalizedValuation_mul, normalizedValuation_zpow, hϖ]; ring)
  have hub : valuation K (ub : K) = 1 := hunit ub (by
    rw [hub_def, normalizedValuation_mul, normalizedValuation_zpow, hϖ]; ring)
  have ha : a = ua * ϖ ^ α := by
    rw [hua_def, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  have hb : b = ub * ϖ ^ β := by
    rw [hub_def, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
  -- (A) a unit against a uniformizer: the power residue symbol
  have hA : ∀ u ϖ' : Kˣ, valuation K (u : K) = 1 → normalizedValuation K ϖ' = 1 →
      (h u ϖ')⁻¹ * u ^ k ∈ U := fun u ϖ' hu hϖ' =>
    (hcong _ _ (hval u ϖ')).mp
      (localHilbertSymbol_unit_uniformizer K hh hn hmu (dvd_card_residueField_sub_one K hn hmu) u
        hu ϖ' hϖ')
  -- (B) two units: trivial
  have hB : ∀ u u' : Kˣ, valuation K (u : K) = 1 → valuation K (u' : K) = 1 → h u u' ∈ U := by
    intro u u' hu hu'
    have h1 := hA u ϖ hu hϖ
    have h2 := hA u (ϖ * u') hu (by
      rw [normalizedValuation_mul, hϖ, normalizedValuation_eq_zero_of_valuation_eq_one K u' hu',
        add_zero])
    have h3 : h u u' = ((h u ϖ)⁻¹ * u ^ k) * ((h u (ϖ * u'))⁻¹ * u ^ k)⁻¹ := by
      rw [IsLocalHilbertSymbol.mul_right hh hn0]
      have hx := (h u ϖ).ne_zero
      have hy := (h u u').ne_zero
      have hz := u.ne_zero
      ext
      push_cast
      field_simp
    rw [h3]
    exact U.mul_mem h1 (U.inv_mem h2)
  -- (C) a uniformizer against a unit: the inverse power residue symbol, by skew-symmetry
  have hC : ∀ u ϖ' : Kˣ, valuation K (u : K) = 1 → normalizedValuation K ϖ' = 1 →
      (h ϖ' u)⁻¹ * (u ^ k)⁻¹ ∈ U := by
    intro u ϖ' hu hϖ'
    have hs := IsLocalHilbertSymbol.skew hh hn0 hmu ϖ' u
    have h1 := hA u ϖ' hu hϖ'
    have h3 : (h ϖ' u)⁻¹ * (u ^ k)⁻¹ = ((h u ϖ')⁻¹ * u ^ k)⁻¹ := by
      rw [eq_inv_of_mul_eq_one_left hs, mul_inv]
    rw [h3]
    exact U.inv_mem h1
  -- (D) a uniformizer against itself: `(ϖ, ϖ) = (-1, ϖ)`
  have hD : ∀ ϖ' : Kˣ, normalizedValuation K ϖ' = 1 → (h ϖ' ϖ')⁻¹ * (-1 : Kˣ) ^ k ∈ U := by
    intro ϖ' hϖ'
    have hneg := IsLocalHilbertSymbol.neg_self hh hn0 hmu ϖ'
    have hs := IsLocalHilbertSymbol.skew hh hn0 hmu ϖ' (-1)
    have h1 := hA (-1) ϖ' (by simp) hϖ'
    have e1 : h ϖ' (-ϖ') = h ϖ' ϖ' * h ϖ' (-1) := by
      rw [show -ϖ' = ϖ' * (-1) by simp, IsLocalHilbertSymbol.mul_right hh hn0]
    rw [hneg] at e1
    have e2 : h ϖ' ϖ' = (h ϖ' (-1))⁻¹ := eq_inv_of_mul_eq_one_left e1.symm
    have e3 : h (-1) ϖ' = (h ϖ' (-1))⁻¹ := eq_inv_of_mul_eq_one_right hs
    rw [e2, ← e3]
    exact h1
  -- assemble
  rw [hcong _ _ (hval a b)]
  have hpz : ∀ (x : Kˣ) (m : ℤ), (x ^ m) ^ k = (x ^ k) ^ m := fun x m => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  have e1 : h a b = h ua ub * h ua ϖ ^ β * h ϖ ub ^ α * h ϖ ϖ ^ (α * β) := by
    conv_lhs => rw [ha, hb]
    simp only [IsLocalHilbertSymbol.mul_left hh hn0, IsLocalHilbertSymbol.mul_right hh hn0, hR, hL,
      ← zpow_mul]
    ac_rfl
  have hbase : (-1 : Kˣ) ^ (α * β) * a ^ β * b ^ (-α)
      = (-1 : Kˣ) ^ (α * β) * ua ^ β * (ub ^ α)⁻¹ := by
    rw [ha, hb, mul_zpow, mul_zpow, ← zpow_mul, ← zpow_mul, show β * -α = -(α * β) by ring,
      zpow_neg, zpow_neg]
    rw [show (-1 : Kˣ) ^ (α * β) * (ua ^ β * ϖ ^ (α * β)) * ((ub ^ α)⁻¹ * (ϖ ^ (α * β))⁻¹)
        = (-1 : Kˣ) ^ (α * β) * ua ^ β * (ub ^ α)⁻¹ * (ϖ ^ (α * β) * (ϖ ^ (α * β))⁻¹) by ac_rfl,
      mul_inv_cancel, mul_one]
  have e2 : ((-1 : Kˣ) ^ (α * β) * a ^ β * b ^ (-α)) ^ k
      = ((-1 : Kˣ) ^ k) ^ (α * β) * (ua ^ k) ^ β * ((ub ^ k) ^ α)⁻¹ := by
    rw [hbase, mul_pow, mul_pow, hpz, hpz, inv_pow, hpz]
  rw [e1, e2]
  have m1 : (h ua ub)⁻¹ * 1 ∈ U := by
    rw [mul_one]
    exact U.inv_mem (hB ua ub hua hub)
  have m2 : (h ua ϖ ^ β)⁻¹ * (ua ^ k) ^ β ∈ U := by
    have := U.zpow_mem (hA ua ϖ hua hϖ) β
    rwa [mul_zpow, inv_zpow] at this
  have m3 : (h ϖ ub ^ α)⁻¹ * ((ub ^ k) ^ α)⁻¹ ∈ U := by
    have := U.zpow_mem (hC ub ϖ hub hϖ) α
    rwa [mul_zpow, inv_zpow, inv_zpow] at this
  have m4 : (h ϖ ϖ ^ (α * β))⁻¹ * ((-1 : Kˣ) ^ k) ^ (α * β) ∈ U := by
    have := U.zpow_mem (hD ϖ hϖ) (α * β)
    rwa [mul_zpow, inv_zpow] at this
  have e3 : (h ua ub * h ua ϖ ^ β * h ϖ ub ^ α * h ϖ ϖ ^ (α * β))⁻¹ *
      (((-1 : Kˣ) ^ k) ^ (α * β) * (ua ^ k) ^ β * ((ub ^ k) ^ α)⁻¹)
      = ((h ua ub)⁻¹ * 1) * ((h ua ϖ ^ β)⁻¹ * (ua ^ k) ^ β) *
        ((h ϖ ub ^ α)⁻¹ * ((ub ^ k) ^ α)⁻¹) *
        ((h ϖ ϖ ^ (α * β))⁻¹ * ((-1 : Kˣ) ^ k) ^ (α * β)) := by
    simp only [mul_inv, mul_one]
    ac_rfl
  rw [e3]
  exact U.mul_mem (U.mul_mem (U.mul_mem m1 m2) m3) m4

end Atlas.Knowledge
