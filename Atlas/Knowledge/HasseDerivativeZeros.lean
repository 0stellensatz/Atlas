import Mathlib

/-!
# zeros of the Hasse derivatives

Over an algebraically closed field whose norm is ultrametric, a ball that contains every zero of
a monic polynomial `f` almost contains a zero of each Hasse derivative of `f`: this is the
nonarchimedean replacement for the Gauss–Lucas theorem, and the two lemmas below are the exact
form it takes. Which lemma applies is decided by the exact degree. When the degree is
`p ^ δ * d₁` with `d₁` prime to `p` and larger than `1`, the `p ^ δ`th Hasse derivative already
has a zero inside the ball, at no cost. When the degree is a bare power `p ^ δ`, no such lemma
is available—`f = X ^ (p ^ δ)` has all its zeros at the center while every intermediate Hasse
derivative is a monomial—and the `p ^ (δ - 1)`th Hasse derivative is only guaranteed a zero in
the ball enlarged by the `(p ^ δ - p ^ (δ - 1))`th root of `‖(p : C)‖⁻¹`. That enlargement is
where the ramification of the tower enters the Ax–Sen–Tate estimate.

The derivatives are the divided ones throughout. The iterated derivative satisfies
`j ! • f.hasseDeriv j = (derivative^[j]) f`, so in residue characteristic `p` the factorial is
not invertible and only the divided form keeps its coefficients where the argument needs them:
the `j`th coefficient of the translate of `f` is the value of `f.hasseDeriv j` at the new center
(`Polynomial.taylor_coeff`), and that is the identity both proofs run on.

Two arithmetic facts about binomial coefficients carry the whole difference between the two
lemmas. `(p ^ δ * d₁).choose (p ^ δ)` is prime to `p`—by Lucas's theorem, the base-`p` digits of
`p ^ δ` being a single `1`—so the leading coefficient of the derivative is a unit and costs
nothing. The `p`-adic valuation of `(p ^ δ).choose (p ^ (δ - 1))` is exactly `1`, so the leading
coefficient of the derivative is `p` up to a unit and the ball has to grow by that much.

The consumer is `Atlas.Knowledge.conjugateDiameterBound`, whose induction alternates the two
lemmas to walk a cluster of conjugates down to the fixed field: at each step the exact degree
decides which one applies, and only the second contributes to the loss of precision that the
bound's constant records.

## Main statements

* `HasseDerivativeZeros.norm_coeff_le` — the coefficients of a monic polynomial whose zeros all
  lie in the ball of radius `r` about `0` are bounded by the powers of `r`.
* `HasseDerivativeZeros.exists_isRoot_hasseDeriv` — Ax's Lemma 2: at exact degree `p ^ δ * d₁`
  with `d₁` prime to `p` and larger than `1`, the `p ^ δ`th Hasse derivative has a zero within
  the same distance of the center.
* `HasseDerivativeZeros.exists_isRoot_hasseDeriv_pow` — Ax's Lemma 3: at exact degree `p ^ δ`,
  the `p ^ (δ - 1)`th Hasse derivative has a zero within the distance enlarged by the norm of
  `p`.

## Implementation notes

The signature is abstract: any algebraically closed normed field of characteristic zero whose
metric is ultrametric. The residue characteristic cannot be read off such a field, so the two
facts the argument needs about `p` are carried as explicit hypotheses—`hp`, that `p` is prime,
and `hunit`, that every natural number prime to `p` has norm one. Both hold in the intended
instance, the completion of an algebraic closure of a `p`-adic field, and neither is available
from the norm alone.

The conclusion of Lemma 3 is stated with the integer power `p ^ δ - p ^ (δ - 1)` on both sides
rather than with a fractional root of `‖(p : C)‖⁻¹`, so that no real exponent appears here. The
consumer, which already works with real exponents, takes the root itself; stating it this way
keeps the file free of `Real.rpow` and its side conditions.

The reduction to the center is by `Polynomial.taylor`, not by a change of variable in the
statement: `Polynomial.taylor c f` is monic of the same degree, its zeros are the zeros of `f`
translated, and `HasseDerivativeZeros.hasseDeriv_taylor` transports the Hasse derivative across
the translation—the source's property (c), which Mathlib does not carry. That last lemma is the
only piece of Ax's list of properties of the divided derivative that had to be proved here;
(a), (b) and (d) are `Polynomial.hasseDeriv_coeff`, `Polynomial.factorial_smul_hasseDeriv` and
`Polynomial.hasseDeriv_comp`.

## References

* [Ax1970] J. Ax, *Zeros of polynomials over local fields—The Galois action*, J. Algebra **15**
  (1970), 417–428.
-/

open Polynomial

namespace Atlas.Knowledge

namespace HasseDerivativeZeros

variable {C : Type*} [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C]
variable {p : ℕ} (hp : p.Prime)
variable (hunit : ∀ m : ℕ, ¬ p ∣ m → ‖(m : C)‖ = 1)

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] in
/-- scaffolding: a product of elements of norm at most `r` has norm at most `r` raised to the
number of factors. -/
theorem norm_multiset_prod_le_pow {r : ℝ} (hr : 0 ≤ r) :
    ∀ t : Multiset C, (∀ z ∈ t, ‖z‖ ≤ r) → ‖t.prod‖ ≤ r ^ Multiset.card t := by
  intro t
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
      intro h
      rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, mul_comm (r ^ _) r]
      exact mul_le_mul (h a (Multiset.mem_cons_self a s))
        (ih fun z hz => h z (Multiset.mem_cons_of_mem hz)) (norm_nonneg _) hr

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] in
/-- scaffolding: a product of elements of norm at least `s` has norm at least `s` raised to the
number of factors. -/
theorem pow_card_le_norm_multiset_prod {s : ℝ} (hs : 0 ≤ s) :
    ∀ t : Multiset C, (∀ z ∈ t, s ≤ ‖z‖) → s ^ Multiset.card t ≤ ‖t.prod‖ := by
  intro t
  induction t using Multiset.induction_on with
  | empty => simp
  | cons a u ih =>
      intro h
      rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, mul_comm (s ^ _) s]
      exact mul_le_mul (h a (Multiset.mem_cons_self a u))
        (ih fun z hz => h z (Multiset.mem_cons_of_mem hz)) (by positivity) (norm_nonneg _)

omit [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] in
/-- The Hasse derivative commutes with translation of the variable: the `k`th Hasse derivative
of `Polynomial.taylor c f` is the translate of the `k`th Hasse derivative of `f`
([Ax 1970, §1, (c), p.419][Ax1970]). -/
theorem hasseDeriv_taylor (k : ℕ) (c : C) (f : C[X]) :
    (taylor c f).hasseDeriv k = taylor c (f.hasseDeriv k) := by
  ext n
  rw [hasseDeriv_coeff, taylor_coeff, taylor_coeff, ← LinearMap.comp_apply, hasseDeriv_comp]
  simp [Nat.choose_symm_add]

omit [CharZero C] in
/-- scaffolding: every coefficient of a monic polynomial whose roots all lie within `r` of
`0` is bounded by the corresponding power of `r` (Ax's Lemma 1 in the crude form the two
zero-location lemmas need) ([Ax 1970, §1, Lemma 1, p.418][Ax1970]). -/
theorem norm_coeff_le (f : Polynomial C) (hf : f.Monic) {r : ℝ} (hr : 0 ≤ r)
    (hroots : ∀ z : C, f.IsRoot z → ‖z‖ ≤ r) {i : ℕ} (hi : i ≤ f.natDegree) :
    ‖f.coeff i‖ ≤ r ^ (f.natDegree - i) := by
  have hsplits : f.Splits := IsAlgClosed.splits f
  have hcard : f.roots.card = f.natDegree := splits_iff_card_roots.mp hsplits
  have hi' : i ≤ f.roots.card := hcard ▸ hi
  -- the coefficient is, up to sign, an elementary symmetric function of the roots
  have key : f.coeff i = (-1) ^ (f.roots.card - i) * f.roots.esymm (f.roots.card - i) := by
    conv_lhs => rw [hsplits.eq_prod_roots_of_monic hf]
    exact Multiset.prod_X_sub_C_coeff _ hi'
  rw [key, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, hcard, Multiset.esymm]
  set n := f.natDegree - i with hn
  by_cases hemp : Multiset.powersetCard n f.roots = 0
  · rw [hemp]
    simpa using by positivity
  · -- the ultrametric bounds the sum by its largest term, a product of `n` roots
    obtain ⟨u, hu, hle⟩ :=
      IsUltrametricDist.exists_norm_multiset_sum_le (M := C)
        (Multiset.powersetCard n f.roots) (f := Multiset.prod)
    refine hle.trans ?_
    obtain ⟨hsub, hcu⟩ := Multiset.mem_powersetCard.mp (hu hemp)
    rw [← hcu]
    exact norm_multiset_prod_le_pow hr u fun z hz =>
      hroots z (isRoot_of_mem_roots (Multiset.mem_of_le hsub hz))

/-- scaffolding, the common skeleton of the two zero-location lemmas: below the exact degree,
the `q`th Hasse derivative has a zero whose distance to the center, raised to the drop in
degree and weighted by the norm of the binomial coefficient that leads the derivative, is at
most `r` raised to the same power. The two lemmas differ only in how that binomial coefficient
is valued ([Ax 1970, §1, proof of Lemma 2, pp.419–420][Ax1970]). -/
theorem exists_isRoot_hasseDeriv_norm_choose_le (f : Polynomial C) (hf : f.Monic) {q : ℕ}
    (hq : q < f.natDegree) (c : C) {r : ℝ} (hr : 0 ≤ r)
    (hroots : ∀ z : C, f.IsRoot z → ‖z - c‖ ≤ r) :
    ∃ β : C, (f.hasseDeriv q).IsRoot β ∧
      ‖β - c‖ ^ (f.natDegree - q) * ‖((f.natDegree.choose q : ℕ) : C)‖
        ≤ r ^ (f.natDegree - q) := by
  classical
  set d := f.natDegree with hdd
  set e := d - q with hee
  have he : e + q = d := by omega
  -- translate the center to `0`
  set F := taylor c f with hF
  have hFd : F.natDegree = d := natDegree_taylor f c
  have hFm : F.Monic := by rw [hF, taylor_apply]; exact hf.comp_X_add_C c
  have hFroots : ∀ z : C, F.IsRoot z → ‖z‖ ≤ r := by
    intro z hz
    have hzc : f.IsRoot (z + c) := by rw [IsRoot, ← taylor_eval]; exact hz
    simpa using hroots (z + c) hzc
  -- the derivative has exact degree `e`, with the binomial coefficient leading it
  set g := F.hasseDeriv q with hg
  have hge : g.coeff e = ((d.choose q : ℕ) : C) := by
    rw [hg, hasseDeriv_coeff, he, ← hFd, hFm.coeff_natDegree, mul_one, hFd]
  have hne : ((d.choose q : ℕ) : C) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hq.le).ne'
  have hgne : g ≠ 0 := fun h => hne (by rw [← hge, h, coeff_zero])
  have hgdeg : g.natDegree = e := by
    refine le_antisymm ?_ (le_natDegree_of_ne_zero (by rw [hge]; exact hne))
    have hle := natDegree_hasseDeriv_le F q
    rw [hFd] at hle
    exact hle
  have hglead : g.leadingCoeff = ((d.choose q : ℕ) : C) := by rw [leadingCoeff, hgdeg, hge]
  have hg0 : ‖g.coeff 0‖ ≤ r ^ e := by
    have hcq : g.coeff 0 = F.coeff q := by
      rw [hg, hasseDeriv_coeff, zero_add, Nat.choose_self, Nat.cast_one, one_mul]
    rw [hcq]
    have hb := norm_coeff_le F hFm hr hFroots (i := q) (by omega)
    rwa [hFd] at hb
  -- the product of the roots of the derivative, read off its constant coefficient
  have hlead0 : g.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hgne
  have hprod : ‖g.roots.prod‖ * ‖g.leadingCoeff‖ = ‖g.coeff 0‖ := by
    have hhm : (g * Polynomial.C g.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hgne
    have hz := (IsAlgClosed.splits
      (g * Polynomial.C g.leadingCoeff⁻¹)).coeff_zero_eq_prod_roots_of_monic hhm
    rw [mul_comm g, roots_C_mul _ (inv_ne_zero hlead0), natDegree_C_mul (inv_ne_zero hlead0),
      coeff_C_mul] at hz
    have hn := congrArg norm hz
    simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, norm_inv] at hn
    rw [← hn]
    field_simp
  have hcard : g.roots.card = e := by
    rw [← hgdeg]
    exact splits_iff_card_roots.mp (IsAlgClosed.splits g)
  have hrne : g.roots ≠ 0 := by
    intro h0
    rw [h0] at hcard
    simp only [Multiset.card_zero] at hcard
    omega
  -- the root of least norm is the one the bound is about
  obtain ⟨β, hβmem, hβmin⟩ :=
    Finset.exists_min_image g.roots.toFinset (fun z => ‖z‖) (Multiset.toFinset_nonempty.mpr hrne)
  have hβpow : ‖β‖ ^ e ≤ ‖g.roots.prod‖ := by
    have hb := pow_card_le_norm_multiset_prod (norm_nonneg β) g.roots
      fun z hz => hβmin z (Multiset.mem_toFinset.mpr hz)
    rwa [hcard] at hb
  refine ⟨β + c, ?_, ?_⟩
  · have hgt : g = taylor c (f.hasseDeriv q) := by rw [hg, hF, hasseDeriv_taylor]
    have hβ : g.IsRoot β := isRoot_of_mem_roots (Multiset.mem_toFinset.mp hβmem)
    rw [hgt, IsRoot, taylor_eval] at hβ
    exact hβ
  · rw [add_sub_cancel_right, ← hglead]
    calc ‖β‖ ^ e * ‖g.leadingCoeff‖ ≤ ‖g.roots.prod‖ * ‖g.leadingCoeff‖ :=
          mul_le_mul_of_nonneg_right hβpow (norm_nonneg _)
      _ = ‖g.coeff 0‖ := hprod
      _ ≤ r ^ e := hg0

include hp hunit in
/-- **Ax's Lemma 2**: if the exact degree is `p ^ δ * d₁` with `d₁ > 1` prime to `p`, the
`p ^ δ`th Hasse derivative has a root within the same distance of the center
([Ax 1970, §1, Lemma 2, p.419][Ax1970]). -/
theorem exists_isRoot_hasseDeriv (f : Polynomial C) (hf : f.Monic) {δ d₁ : ℕ}
    (hd : f.natDegree = p ^ δ * d₁) (hd₁ : ¬ p ∣ d₁) (hd₁1 : 1 < d₁) (c : C)
    {r : ℝ} (hr : 0 ≤ r) (hroots : ∀ z : C, f.IsRoot z → ‖z - c‖ ≤ r) :
    ∃ β : C, (f.hasseDeriv (p ^ δ)).IsRoot β ∧ ‖β - c‖ ≤ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpos : 0 < p ^ δ := Nat.pow_pos hp.pos
  have hq : p ^ δ < f.natDegree := by
    rw [hd]
    nlinarith [hpos, hd₁1]
  obtain ⟨β, hβ, hle⟩ := exists_isRoot_hasseDeriv_norm_choose_le f hf hq c hr hroots
  refine ⟨β, hβ, ?_⟩
  -- Lucas's theorem: the binomial coefficient is congruent to `d₁` modulo `p`
  have hchoose : ¬ p ∣ f.natDegree.choose (p ^ δ) := by
    rw [hd]
    intro hdvd
    refine hd₁ ?_
    have hmod : (p ^ δ * d₁).choose (p ^ δ * 1) ≡ d₁.choose 1 [MOD p] :=
      Choose.choose_pow_mul_pow_mul_modEq_choose_nat
    rw [mul_one, Nat.choose_one_right] at hmod
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))
  rw [hunit _ hchoose, mul_one] at hle
  exact le_of_pow_le_pow_left₀ (by omega) hr hle

include hp hunit in
/-- **Ax's Lemma 3**: if the exact degree is `p ^ δ` with `δ ≥ 1`, the `p ^ (δ - 1)`th Hasse
derivative has a root within the distance enlarged by the `(p ^ δ - p ^ (δ - 1))`th root of
`‖(p : C)‖⁻¹`—stated with integer powers, the enlargement priced on the power
([Ax 1970, §1, Lemma 3, pp.420–421][Ax1970]). -/
theorem exists_isRoot_hasseDeriv_pow (f : Polynomial C) (hf : f.Monic) {δ : ℕ} (hδ : 0 < δ)
    (hd : f.natDegree = p ^ δ) (c : C)
    {r : ℝ} (hr : 0 ≤ r) (hroots : ∀ z : C, f.IsRoot z → ‖z - c‖ ≤ r) :
    ∃ β : C, (f.hasseDeriv (p ^ (δ - 1))).IsRoot β ∧
      ‖β - c‖ ^ (p ^ δ - p ^ (δ - 1)) ≤ r ^ (p ^ δ - p ^ (δ - 1)) * ‖(p : C)‖⁻¹ := by
  have hq : p ^ (δ - 1) < f.natDegree := by
    rw [hd]
    exact Nat.pow_lt_pow_right hp.one_lt (by omega)
  obtain ⟨β, hβ, hle⟩ := exists_isRoot_hasseDeriv_norm_choose_le f hf hq c hr hroots
  refine ⟨β, hβ, ?_⟩
  have hN : f.natDegree.choose (p ^ (δ - 1)) ≠ 0 := (Nat.choose_pos hq.le).ne'
  -- the binomial coefficient has `p`-adic valuation exactly one
  have hfact : (f.natDegree.choose (p ^ (δ - 1))).factorization p = 1 := by
    rw [hd, Nat.factorization_choose_prime_pow hp (Nat.pow_le_pow_right hp.pos (by omega))
      (Nat.pow_pos hp.pos).ne', Nat.Prime.factorization_pow hp, Finsupp.single_eq_same]
    omega
  have hnorm : ‖((f.natDegree.choose (p ^ (δ - 1)) : ℕ) : C)‖ = ‖(p : C)‖ := by
    obtain ⟨m, hm, hNm⟩ : ∃ m, ¬ p ∣ m ∧ f.natDegree.choose (p ^ (δ - 1)) = p * m := by
      refine ⟨ordCompl[p] (f.natDegree.choose (p ^ (δ - 1))), Nat.not_dvd_ordCompl hp hN, ?_⟩
      conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self (f.natDegree.choose (p ^ (δ - 1))) p]
      rw [hfact, pow_one]
    rw [hNm]
    push_cast
    rw [norm_mul, hunit m hm, mul_one]
  rw [hnorm, hd] at hle
  have hppos : 0 < ‖(p : C)‖ := by
    rw [norm_pos_iff]
    exact Nat.cast_ne_zero.mpr hp.pos.ne'
  rw [← div_eq_mul_inv, le_div_iff₀ hppos]
  exact hle

end HasseDerivativeZeros

end Atlas.Knowledge
