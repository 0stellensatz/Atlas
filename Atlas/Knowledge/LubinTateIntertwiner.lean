import Mathlib
import Atlas.Knowledge.LubinTateSeries

/-!
# Lubin–Tate intertwiner

The fundamental lemma of Lubin–Tate theory, fully proved: for two Lubin–Tate series
`e`, `ē` with the same linear coefficient `π` over a discrete valuation ring with finite
residue field, and any prescribed linear form `∑ Lᵢ Xᵢ`, there is a unique multivariable
power series `H` with that linear term satisfying the intertwining equation
`e(H(X)) = H(ē(X₁), …, ē(Xₙ))`. The construction is Milne's own induction: the defect of
an approximation is divisible by `π` because reduction turns both sides into the same
`q`-power Frobenius substitution, and the degree-`m` correction divides by the unit
`1 − π^{m−1}`; corrections in degree `m` change nothing below `m`, so the coefficients
stabilize into the intertwiner. Uniqueness runs the same computation in reverse.

## Main definitions

* `lubinTateLinearForm`, `LubinTateHasLinearTerm` — the prescribed-linear-term interface.
* `lubinTateInVariable`, `LubinTateIntertwines` — the intertwining equation.
* `lubinTateIntertwiner` — the recursive solution.

## Main statements

* `lubinTateIntertwiner_hasLinearTerm`, `lubinTateIntertwiner_intertwines` — the
  construction solves the problem.
* `LubinTateIntertwines.eq_of_hasLinearTerm` — two solutions with one linear term agree.
* `existsUnique_lubinTateIntertwiner` — the fundamental lemma.
* `le_order_finset_sum` — order of a finite sum against a common bound; the utility the
  formal-group files share.

## Implementation notes

The recursion follows Milne's proof shape — a whole homogeneous degree is corrected at
once — rather than the source's monomial-by-monomial list folds
(`LubinTate/FormalModule/RecursiveIntertwiner.lean`, with its correction step in
`RecursiveCorrection.lean` and stabilization in `DegreeStabilization.lean`; 4172 lines
across the `FormalModule/` directory). Three pillars carry the argument: a first-order
perturbation formula for substitution *into* a one-variable series, its mirror for
substitution *of* the intertwining family, and the `q`-power Frobenius identity
`H ^ q = H(X₁^q, …, Xₙ^q)` over the residue field, proved by dense-extension uniqueness
(`MvPowerSeries.eval₂_unique`) from the polynomial case. Completeness of the coefficient
ring is nowhere used — the ambient is the layer's abstract discrete valuation ring — and
this is the deliberate generalization recorded in `Atlas.Knowledge.LubinTateSeries`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open MvPowerSeries

namespace Atlas.Knowledge

section LinearTerm

variable {A : Type*} [CommRing A] {σ : Type*} [Fintype σ]

/-- The multivariable linear form `∑ i, Lᵢ Xᵢ`
([Milne 2020, Chap. I, §2, Lem. 2.11, p.32][MilneCFT];
Yamaguchi 2026,
`LubinTate/FormalModule/LinearTerm.lean:20`). -/
noncomputable def lubinTateLinearForm (L : σ → A) : MvPowerSeries σ A :=
  ∑ i, MvPowerSeries.C (L i) * MvPowerSeries.X i

/-- A series **has linear term** `L` when its difference from `∑ i, Lᵢ Xᵢ` has order at
least two ([Milne 2020, Chap. I, §2, Lem. 2.11, p.32][MilneCFT]; Yamaguchi 2026,
`LubinTate/FormalModule/LinearTerm.lean:31`). -/
def LubinTateHasLinearTerm (H : MvPowerSeries σ A) (L : σ → A) : Prop :=
  (2 : ℕ∞) ≤ (H - lubinTateLinearForm L).order

@[simp]
theorem constantCoeff_lubinTateLinearForm (L : σ → A) :
    constantCoeff (lubinTateLinearForm L) = 0 := by
  simp [lubinTateLinearForm]

private theorem one_le_order_of_constantCoeff_eq_zero {τ : Type*} {f : MvPowerSeries τ A}
    (hf : constantCoeff f = 0) : (1 : ℕ∞) ≤ f.order :=
  Order.one_le_iff_ne_zero.mpr (f.order_ne_zero_iff_constCoeff_eq_zero.mpr hf)

theorem one_le_order_lubinTateLinearForm (L : σ → A) :
    (1 : ℕ∞) ≤ (lubinTateLinearForm L).order :=
  one_le_order_of_constantCoeff_eq_zero (constantCoeff_lubinTateLinearForm L)

theorem coeff_lubinTateLinearForm_single (L : σ → A) (i : σ) :
    coeff (Finsupp.single i 1) (lubinTateLinearForm L) = L i := by
  classical
  rw [lubinTateLinearForm, map_sum]
  rw [Finset.sum_eq_single i]
  · rw [show (MvPowerSeries.X i : MvPowerSeries σ A) = monomial (Finsupp.single i 1) 1 by
      simpa using X_pow_eq (R := A) i 1]
    simp [coeff_C_mul]
  · intro j _ hj
    rw [show (MvPowerSeries.X j : MvPowerSeries σ A) = monomial (Finsupp.single j 1) 1 by
      simpa using X_pow_eq (R := A) j 1]
    rw [coeff_C_mul, coeff_monomial, if_neg, mul_zero]
    intro hij
    exact hj ((Finsupp.single_left_injective one_ne_zero) hij).symm
  · simp

namespace LubinTateHasLinearTerm

variable {H : MvPowerSeries σ A} {L : σ → A}

theorem coeff_eq_of_degree_lt_two (h : LubinTateHasLinearTerm H L) {d : σ →₀ ℕ}
    (hd : (d.degree : ℕ∞) < 2) :
    coeff d H = coeff d (lubinTateLinearForm L) := by
  have := coeff_of_lt_order (f := H - lubinTateLinearForm L) (d := d) (lt_of_lt_of_le hd h)
  rw [map_sub, sub_eq_zero] at this
  exact this

theorem constantCoeff_eq_zero (h : LubinTateHasLinearTerm H L) : constantCoeff H = 0 := by
  have h0 := h.coeff_eq_of_degree_lt_two (d := 0) (by simp)
  simpa using h0

theorem one_le_order (h : LubinTateHasLinearTerm H L) : (1 : ℕ∞) ≤ H.order :=
  one_le_order_of_constantCoeff_eq_zero h.constantCoeff_eq_zero

theorem coeff_single (h : LubinTateHasLinearTerm H L) (i : σ) :
    coeff (Finsupp.single i 1) H = L i := by
  rw [h.coeff_eq_of_degree_lt_two (by simp [Finsupp.degree_single]),
    coeff_lubinTateLinearForm_single]

end LubinTateHasLinearTerm

theorem lubinTateLinearForm_hasLinearTerm (L : σ → A) :
    LubinTateHasLinearTerm (lubinTateLinearForm L) L := by
  rw [LubinTateHasLinearTerm, sub_self, order_zero]
  exact le_top

end LinearTerm

section Intertwines

variable {A : Type*} [CommRing A] [IsLocalRing A] {π : A} {σ : Type*}

/-- The Lubin–Tate series `e` inserted into the variable `Xᵢ`
(Yamaguchi 2026,
`LubinTate/FormalModule/Intertwiner.lean:26`). -/
noncomputable def lubinTateInVariable (e : LubinTateSeries A π) (i : σ) :
    MvPowerSeries σ A :=
  PowerSeries.subst (MvPowerSeries.X i) e.toPowerSeries

@[simp]
theorem constantCoeff_lubinTateInVariable (e : LubinTateSeries A π) (i : σ) :
    constantCoeff (lubinTateInVariable e i) = 0 := by
  classical
  rw [lubinTateInVariable, ← coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_subst (PowerSeries.HasSubst.X i)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro k
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  · rw [X_pow_eq, coeff_monomial, if_neg, smul_zero]
    intro h0
    have := congrArg Finsupp.degree h0
    simp [Finsupp.degree_single] at this
    omega

theorem hasSubst_lubinTateInVariable [Finite σ] (e : LubinTateSeries A π) :
    MvPowerSeries.HasSubst (fun i : σ => lubinTateInVariable e i) :=
  hasSubst_of_constantCoeff_zero fun i => constantCoeff_lubinTateInVariable e i

private theorem order_X_mv (i : σ) :
    (MvPowerSeries.X i : MvPowerSeries σ A).order = 1 := by
  rw [show (MvPowerSeries.X i : MvPowerSeries σ A) = monomial (Finsupp.single i 1) 1 by
    simpa using X_pow_eq (R := A) i 1]
  rw [order_monomial_of_ne_zero one_ne_zero]
  simp [Finsupp.degree_single]

/-- The insertion differs from `π • Xᵢ` only in order at least two. -/
theorem two_le_order_lubinTateInVariable_sub (e : LubinTateSeries A π) (i : σ) :
    (2 : ℕ∞) ≤ ((lubinTateInVariable e i) - π • MvPowerSeries.X i).order := by
  have hX : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries σ A) :=
    PowerSeries.HasSubst.X i
  have hsplit : lubinTateInVariable e i - π • MvPowerSeries.X i =
      PowerSeries.subst (MvPowerSeries.X i)
        (e.toPowerSeries - π • PowerSeries.X) := by
    rw [lubinTateInVariable,
      PowerSeries.subst_sub hX, PowerSeries.subst_smul hX, PowerSeries.subst_X hX]
  rw [hsplit]
  have horder : (2 : ℕ∞) ≤ (e.toPowerSeries - π • PowerSeries.X).order := by
    apply PowerSeries.le_order
    intro k hk
    have hk2 : k < 2 := by exact_mod_cast hk
    interval_cases k
    · simp
    · simp
  calc (2 : ℕ∞) = (MvPowerSeries.X i : MvPowerSeries σ A).order * 2 := by
        rw [order_X_mv, one_mul]
      _ ≤ (MvPowerSeries.X i : MvPowerSeries σ A).order *
          (e.toPowerSeries - π • PowerSeries.X).order := mul_le_mul' le_rfl horder
      _ ≤ _ := PowerSeries.le_order_subst _ hX _

/-- The **intertwining equation** `e(H(X)) = H(ē(X₁), …, ē(Xₙ))`
([Milne 2020, Chap. I, §2, Lem. 2.11, p.32][MilneCFT];
Yamaguchi 2026, `LubinTate/FormalModule/Intertwiner.lean:47`). -/
def LubinTateIntertwines (e ebar : LubinTateSeries A π)
    (H : MvPowerSeries σ A) : Prop :=
  PowerSeries.subst H e.toPowerSeries =
    MvPowerSeries.subst (fun i : σ => lubinTateInVariable ebar i) H

end Intertwines

section Perturbation

variable {A : Type*} [CommRing A] {σ : Type*}

/-- The order of a finite sum is at least any common lower bound of the summands'
orders — the sum-shaped face of `MvPowerSeries.min_order_le_add`, absent from Mathlib. -/
theorem le_order_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries σ A) (n : ℕ∞) (h : ∀ i ∈ s, n ≤ (f i).order) :
    n ≤ (∑ i ∈ s, f i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha IH =>
    rw [Finset.sum_insert ha]
    refine le_trans (le_min (h a (Finset.mem_insert_self a s))
      (IH fun i hi => h i (Finset.mem_insert_of_mem hi))) min_order_le_add

private theorem le_order_pow_of_one_le {f : MvPowerSeries σ A} (hf : (1 : ℕ∞) ≤ f.order)
    (k : ℕ) : (k : ℕ∞) ≤ (f ^ k).order := by
  refine le_trans ?_ (le_order_pow k)
  calc (k : ℕ∞) = k • (1 : ℕ∞) := by simp
    _ ≤ k • f.order := nsmul_le_nsmul_right hf k

/-- The first-order perturbation of substitution into a one-variable series: below and
at the order of the difference, only the linear coefficient sees it. -/
private theorem coeff_powerSeries_subst_sub {H H' : MvPowerSeries σ A}
    (hH : constantCoeff H = 0) (hH' : constantCoeff H' = 0)
    (e : PowerSeries A) {d : σ →₀ ℕ}
    (hord : (d.degree : ℕ∞) ≤ (H - H').order) :
    coeff d (PowerSeries.subst H e) - coeff d (PowerSeries.subst H' e) =
      PowerSeries.coeff 1 e * coeff d (H - H') := by
  have hsH := PowerSeries.HasSubst.of_constantCoeff_zero hH
  have hsH' := PowerSeries.HasSubst.of_constantCoeff_zero hH'
  rw [PowerSeries.coeff_subst hsH, PowerSeries.coeff_subst hsH',
    ← finsum_sub_distrib (PowerSeries.coeff_subst_finite hsH e d)
      (PowerSeries.coeff_subst_finite hsH' e d)]
  rw [finsum_eq_single _ 1]
  · rw [pow_one, pow_one, smul_eq_mul, smul_eq_mul, ← mul_sub, ← map_sub]
  · intro k hk
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp
    · have hk2 : 2 ≤ k := by omega
      have hcoeff : coeff d (H ^ k) = coeff d (H' ^ k) := by
        have hfactor : H ^ k - H' ^ k =
            (∑ i ∈ Finset.range k, H ^ i * H' ^ (k - 1 - i)) * (H - H') :=
          (geom_sum₂_mul H H' k).symm
        have hgeom : (((k - 1 : ℕ)) : ℕ∞) ≤
            (∑ i ∈ Finset.range k, H ^ i * H' ^ (k - 1 - i)).order := by
          apply le_order_finset_sum
          intro i hi
          rw [Finset.mem_range] at hi
          calc (((k - 1 : ℕ)) : ℕ∞) = ((i : ℕ∞)) + (((k - 1 - i : ℕ)) : ℕ∞) := by
                rw [← Nat.cast_add]
                congr 1
                omega
            _ ≤ (H ^ i).order + (H' ^ (k - 1 - i)).order :=
                add_le_add
                  (le_order_pow_of_one_le
                    (one_le_order_of_constantCoeff_eq_zero hH) i)
                  (le_order_pow_of_one_le
                    (one_le_order_of_constantCoeff_eq_zero hH') (k - 1 - i))
            _ ≤ _ := le_order_mul
        have horder : (d.degree : ℕ∞) < (H ^ k - H' ^ k).order := by
          rw [hfactor]
          refine lt_of_lt_of_le ?_ le_order_mul
          calc (d.degree : ℕ∞) < 1 + (d.degree : ℕ∞) := by
                exact_mod_cast (by omega : d.degree < 1 + d.degree)
            _ ≤ (((k - 1 : ℕ)) : ℕ∞) + (H - H').order := by
                refine add_le_add ?_ hord
                exact_mod_cast (by omega : 1 ≤ k - 1)
            _ ≤ _ := add_le_add hgeom le_rfl
        have := coeff_of_lt_order horder
        rw [map_sub, sub_eq_zero] at this
        exact this
      simp [hcoeff]

end Perturbation

section MvPerturbation

variable {A : Type*} [CommRing A] [IsLocalRing A] {π : A} {σ : Type*}

omit [IsLocalRing A] in
private theorem smul_monomial' (a : A) (d : σ →₀ ℕ) (b : A) :
    a • (monomial d b : MvPowerSeries σ A) = monomial d (a * b) := by
  classical
  ext e
  rw [coeff_smul, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

omit [IsLocalRing A] in
private theorem prod_monomial {ι : Type*} (s : Finset ι) (v : ι → σ →₀ ℕ) (c : ι → A) :
    (∏ i ∈ s, (monomial (v i) (c i) : MvPowerSeries σ A)) =
      monomial (∑ i ∈ s, v i) (∏ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha IH =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha, IH,
      monomial_mul_monomial]

omit [IsLocalRing A] in
private theorem le_order_finset_prod {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries σ A) (n : ι → ℕ) (h : ∀ i ∈ s, ((n i : ℕ∞)) ≤ (f i).order) :
    ((∑ i ∈ s, n i : ℕ) : ℕ∞) ≤ (∏ i ∈ s, f i).order := by
  refine le_trans ?_ (le_weightedOrder_prod _ f s)
  rw [Nat.cast_sum]
  exact Finset.sum_le_sum h

omit [IsLocalRing A] in
private theorem le_order_pow_sub_pow {a b : MvPowerSeries σ A}
    (ha : (1 : ℕ∞) ≤ a.order) (hb : (2 : ℕ∞) ≤ b.order) (k : ℕ) :
    ((k : ℕ∞)) + 1 ≤ ((a + b) ^ k - a ^ k).order := by
  rw [add_pow, Finset.sum_range_succ]
  simp only [Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
    add_sub_cancel_right]
  apply le_order_finset_sum
  intro m hm
  rw [Finset.mem_range] at hm
  calc ((k : ℕ∞)) + 1 = (((k + 1 : ℕ)) : ℕ∞) := by push_cast; rfl
    _ ≤ (((m + 2 * (k - m) : ℕ)) : ℕ∞) := by
        exact_mod_cast (by omega : k + 1 ≤ m + 2 * (k - m))
    _ = ((m : ℕ∞)) + (((2 * (k - m) : ℕ)) : ℕ∞) := by push_cast; rfl
    _ ≤ (a ^ m).order + (b ^ (k - m)).order := by
        refine add_le_add (le_order_pow_of_one_le ha m) ?_
        calc (((2 * (k - m) : ℕ)) : ℕ∞) = (k - m) • (2 : ℕ∞) := by
              rw [nsmul_eq_mul]
              exact_mod_cast (by ring : 2 * (k - m) = (k - m) * 2)
          _ ≤ (k - m) • b.order := nsmul_le_nsmul_right hb (k - m)
          _ ≤ _ := le_order_pow (k - m)
    _ ≤ (a ^ m * b ^ (k - m)).order := le_order_mul
    _ ≤ (a ^ m * b ^ (k - m) * ((k.choose m : ℕ) : MvPowerSeries σ A)).order :=
        le_trans le_self_add le_order_mul

omit [IsLocalRing A] in
private theorem le_order_smul' (a : A) (f : MvPowerSeries σ A) :
    f.order ≤ (a • f).order :=
  le_weightedOrder_smul _

omit [IsLocalRing A] in
private theorem le_order_prod_sub_prod {ι : Type*} (s : Finset ι)
    (f g : ι → MvPowerSeries σ A) (n : ι → ℕ)
    (hg : ∀ i ∈ s, ((n i : ℕ∞)) ≤ (g i).order)
    (hfg : ∀ i ∈ s, ((n i : ℕ∞)) + 1 ≤ (f i - g i).order) :
    ((∑ i ∈ s, n i : ℕ) : ℕ∞) + 1 ≤ (∏ i ∈ s, f i - ∏ i ∈ s, g i).order := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t ha IH =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha]
    have hf : ∀ i ∈ insert a t, ((n i : ℕ∞)) ≤ (f i).order := by
      intro i hi
      have hsplit : f i = g i + (f i - g i) := by abel
      rw [hsplit]
      exact le_trans (le_min (hg i hi) (le_trans le_self_add (hfg i hi))) min_order_le_add
    have key : f a * ∏ i ∈ t, f i - g a * ∏ i ∈ t, g i =
        (f a - g a) * ∏ i ∈ t, f i + g a * (∏ i ∈ t, f i - ∏ i ∈ t, g i) := by ring
    rw [key]
    refine le_trans (le_min ?_ ?_) min_order_le_add
    · calc (((n a + ∑ i ∈ t, n i : ℕ)) : ℕ∞) + 1
          = ((((n a : ℕ)) : ℕ∞) + 1) + (((∑ i ∈ t, n i : ℕ)) : ℕ∞) := by push_cast; ring
        _ ≤ (f a - g a).order + (∏ i ∈ t, f i).order :=
            add_le_add (hfg a (Finset.mem_insert_self a t))
              (le_order_finset_prod t f n fun i hi => hf i (Finset.mem_insert_of_mem hi))
        _ ≤ _ := le_order_mul
    · calc (((n a + ∑ i ∈ t, n i : ℕ)) : ℕ∞) + 1
          = (((n a : ℕ)) : ℕ∞) + ((((∑ i ∈ t, n i : ℕ)) : ℕ∞) + 1) := by push_cast; ring
        _ ≤ (g a).order + (∏ i ∈ t, f i - ∏ i ∈ t, g i).order :=
            add_le_add (hg a (Finset.mem_insert_self a t))
              (IH (fun i hi => hg i (Finset.mem_insert_of_mem hi))
                (fun i hi => hfg i (Finset.mem_insert_of_mem hi)))
        _ ≤ _ := le_order_mul

open scoped Classical in
/-- The coefficient of the substituted monomial family in the critical degree: only the
matching exponent survives, weighted by `π` to the degree. -/
private theorem coeff_finsuppProd_lubinTateInVariable (ebar : LubinTateSeries A π)
    (u d : σ →₀ ℕ) (hdeg : d.degree ≤ u.degree) :
    coeff d (u.prod fun i k => (lubinTateInVariable ebar i) ^ k) =
      if u = d then π ^ u.degree else 0 := by
  classical
  rw [Finsupp.prod]
  have hgprod : (∏ i ∈ u.support, (π • MvPowerSeries.X i : MvPowerSeries σ A) ^ u i) =
      monomial u (π ^ u.degree) := by
    have : ∀ i ∈ u.support, (π • MvPowerSeries.X i : MvPowerSeries σ A) ^ u i =
        monomial (Finsupp.single i (u i)) (π ^ u i) := by
      intro i _
      rw [smul_pow, X_pow_eq, smul_monomial', mul_one]
    rw [Finset.prod_congr rfl this, prod_monomial]
    have h1 : (∑ i ∈ u.support, Finsupp.single i (u i)) = u := u.sum_single
    have h2 : (∏ i ∈ u.support, π ^ u i) = π ^ u.degree := by
      rw [Finset.prod_pow_eq_pow_sum, Finsupp.degree_apply]
    rw [h1, h2]
  have hdiff : ((u.degree : ℕ∞)) + 1 ≤
      ((∏ i ∈ u.support, (lubinTateInVariable ebar i) ^ u i) -
        ∏ i ∈ u.support, (π • MvPowerSeries.X i : MvPowerSeries σ A) ^ u i).order := by
    have := le_order_prod_sub_prod u.support
      (fun i => (lubinTateInVariable ebar i) ^ u i)
      (fun i => (π • MvPowerSeries.X i : MvPowerSeries σ A) ^ u i)
      (fun i => u i) ?_ ?_
    · rw [← Finsupp.degree_apply] at this
      exact this
    · intro i _
      refine le_order_pow_of_one_le ?_ (u i)
      exact le_trans (by rw [order_X_mv]) (le_order_smul' π (MvPowerSeries.X i))
    · intro i _
      have hsplit : lubinTateInVariable ebar i =
          π • MvPowerSeries.X i +
            (lubinTateInVariable ebar i - π • MvPowerSeries.X i) := by abel
      rw [hsplit]
      exact le_order_pow_sub_pow
        (le_trans (by rw [order_X_mv]) (le_order_smul' π (MvPowerSeries.X i)))
        (two_le_order_lubinTateInVariable_sub ebar i) (u i)
  have hsplit2 : (∏ i ∈ u.support, (lubinTateInVariable ebar i) ^ u i) =
      monomial u (π ^ u.degree) +
        ((∏ i ∈ u.support, (lubinTateInVariable ebar i) ^ u i) -
          ∏ i ∈ u.support, (π • MvPowerSeries.X i : MvPowerSeries σ A) ^ u i) := by
    rw [hgprod.symm]
    abel
  rw [hsplit2, map_add, coeff_monomial]
  have hzero : coeff d
      ((∏ i ∈ u.support, (lubinTateInVariable ebar i) ^ u i) -
        ∏ i ∈ u.support, (π • MvPowerSeries.X i : MvPowerSeries σ A) ^ u i) = 0 := by
    apply coeff_of_lt_order
    refine lt_of_lt_of_le ?_ hdiff
    exact_mod_cast (by omega : d.degree < u.degree + 1)
  rw [hzero, add_zero]
  by_cases h : d = u
  · subst h
    simp
  · rw [if_neg h, if_neg (Ne.symm h)]



/-- The mirror perturbation: substituting the intertwining family into a series, the
critical-degree coefficient is scaled by `π` to the degree. -/
private theorem coeff_subst_lubinTateInVariable [Finite σ] (ebar : LubinTateSeries A π)
    {E : MvPowerSeries σ A} {d : σ →₀ ℕ} (hord : (d.degree : ℕ∞) ≤ E.order) :
    coeff d (MvPowerSeries.subst (fun i => lubinTateInVariable ebar i) E) =
      π ^ d.degree * coeff d E := by
  classical
  rw [MvPowerSeries.coeff_subst (hasSubst_lubinTateInVariable ebar)]
  rw [finsum_eq_single _ d]
  · rw [coeff_finsuppProd_lubinTateInVariable ebar d d le_rfl, if_pos rfl,
      smul_eq_mul, mul_comm]
  · intro u hu
    rcases lt_or_ge u.degree d.degree with hlt | hge
    · rw [coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast hlt) hord), zero_smul]
    · rw [coeff_finsuppProd_lubinTateInVariable ebar u d hge, if_neg hu, smul_zero]

end MvPerturbation

section Frobenius

open scoped WithPiTopology

variable {k : Type*} [Field k] [Fintype k] {σ : Type*}

/-- The `q`-power Frobenius identity over a finite field: raising to the field
cardinality is substitution of `Xᵢ ^ q`, by dense-extension uniqueness from the
polynomial case. -/
private theorem pow_card_eq_subst (H : MvPowerSeries σ k) :
    H ^ (Fintype.card k) =
      MvPowerSeries.subst (fun i => (X i : MvPowerSeries σ k) ^ (Fintype.card k)) H := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists k
  obtain ⟨n, hpn, hcard⟩ := FiniteField.card k p
  haveI : Fact p.Prime := ⟨hpn⟩
  haveI : CharP (MvPowerSeries σ k) p :=
    charP_of_injective_ringHom (f := (MvPowerSeries.C : k →+* MvPowerSeries σ k))
      (fun a b hab => by
        simpa using congrArg (MvPowerSeries.constantCoeff) hab) p
  have hq0 : Fintype.card k ≠ 0 := Fintype.card_ne_zero
  have hs : MvPowerSeries.HasSubst
      (fun i : σ => (X i : MvPowerSeries σ k) ^ (Fintype.card k)) :=
    MvPowerSeries.HasSubst.X_pow hq0
  letI : UniformSpace k := ⊥
  haveI : DiscreteUniformity k := ⟨rfl⟩
  have key : (fun H : MvPowerSeries σ k => H ^ Fintype.card k) =
      eval₂ (algebraMap k (MvPowerSeries σ k))
        (fun i => (X i : MvPowerSeries σ k) ^ (Fintype.card k)) := by
    apply eval₂_unique
    · exact continuous_of_discreteTopology
    · exact hs.hasEval
    · exact continuous_pow _
    · intro P
      induction P using MvPolynomial.induction_on with
      | C a =>
        rw [MvPolynomial.eval₂_C, MvPolynomial.coe_C, ← map_pow, FiniteField.pow_card]
        rfl
      | add P Q hP hQ =>
        rw [MvPolynomial.coe_add, MvPolynomial.eval₂_add, ← hP, ← hQ, hcard]
        exact add_pow_char_pow _ _ p n
      | mul_X P i hP =>
        rw [MvPolynomial.coe_mul, MvPolynomial.eval₂_mul, ← hP,
          MvPolynomial.eval₂_X, MvPolynomial.coe_X, mul_pow]
  rw [subst_eq_eval₂, ← key]

end Frobenius

section Divisibility

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)] {π : A} {σ : Type*}

omit [Finite (IsLocalRing.ResidueField A)] in
private theorem residue_eq_zero_of_irreducible {π : A} (hπ : Irreducible π) :
    IsLocalRing.residue A π = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq]
  exact Ideal.mem_span_singleton_self π

omit [Finite (IsLocalRing.ResidueField A)] in
private theorem dvd_of_residue_eq_zero (hπ : Irreducible π) {a : A}
    (ha : IsLocalRing.residue A a = 0) : π ∣ a := by
  rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq,
    Ideal.mem_span_singleton] at ha
  exact ha

/-- Every coefficient of the intertwining defect is divisible by `π`: reduction turns
both sides into the same `q`-power Frobenius substitution. -/
private theorem dvd_coeff_defect [Finite σ] (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) {H : MvPowerSeries σ A}
    (hH : constantCoeff H = 0) (d : σ →₀ ℕ) :
    π ∣ coeff d (PowerSeries.subst H e.toPowerSeries -
      MvPowerSeries.subst (fun i => lubinTateInVariable ebar i) H) := by
  classical
  letI : Fintype (IsLocalRing.ResidueField A) := Fintype.ofFinite _
  set res := IsLocalRing.residue A with hres
  apply dvd_of_residue_eq_zero hπ
  have hcard : Nat.card (IsLocalRing.ResidueField A) =
      Fintype.card (IsLocalRing.ResidueField A) := Nat.card_eq_fintype_card
  -- move the residue inside the coefficient
  rw [show res (coeff d (PowerSeries.subst H e.toPowerSeries -
      MvPowerSeries.subst (fun i => lubinTateInVariable ebar i) H)) =
      coeff d (MvPowerSeries.map res (PowerSeries.subst H e.toPowerSeries -
        MvPowerSeries.subst (fun i => lubinTateInVariable ebar i) H)) from
    (coeff_map res d _).symm]
  rw [map_sub]
  have hsH := PowerSeries.HasSubst.of_constantCoeff_zero hH
  -- the e-side becomes H̄ ^ q
  have he : MvPowerSeries.map res (PowerSeries.subst H e.toPowerSeries) =
      (MvPowerSeries.map res H) ^ Nat.card (IsLocalRing.ResidueField A) := by
    rw [PowerSeries.map_subst hsH, e.map_residue_eq_frobenius]
    have hsH' : PowerSeries.HasSubst (MvPowerSeries.map res H) :=
      PowerSeries.HasSubst.of_constantCoeff_zero (by
        rw [MvPowerSeries.constantCoeff_map, hH, map_zero])
    rw [PowerSeries.subst_pow hsH', PowerSeries.subst_X hsH']
  -- the ē-side becomes H̄ (X₁^q, …, Xₙ^q)
  have hebar : MvPowerSeries.map res
      (MvPowerSeries.subst (fun i => lubinTateInVariable ebar i) H) =
      MvPowerSeries.subst
        (fun i => (X i : MvPowerSeries σ (IsLocalRing.ResidueField A)) ^
          Nat.card (IsLocalRing.ResidueField A))
        (MvPowerSeries.map res H) := by
    rw [MvPowerSeries.map_subst (hasSubst_lubinTateInVariable ebar)]
    congr 1
    funext i
    rw [lubinTateInVariable, PowerSeries.map_subst (PowerSeries.HasSubst.X i),
      ebar.map_residue_eq_frobenius]
    have hsX : PowerSeries.HasSubst
        (MvPowerSeries.map res (MvPowerSeries.X i) :
          MvPowerSeries σ (IsLocalRing.ResidueField A)) := by
      apply PowerSeries.HasSubst.of_constantCoeff_zero
      rw [MvPowerSeries.constantCoeff_map]
      simp
    rw [PowerSeries.subst_pow hsX, PowerSeries.subst_X hsX, MvPowerSeries.map_X]
  rw [he, hebar, hcard, pow_card_eq_subst, sub_self, map_zero]

end Divisibility

section Recursion

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)] {π : A} {σ : Type*} [Fintype σ]

omit [Finite (IsLocalRing.ResidueField A)] in
private theorem isUnit_one_sub_uniformizer_pow (hπ : Irreducible π) {r : ℕ} (hr : r ≠ 0) :
    IsUnit (1 - π ^ r) := by
  apply IsLocalRing.isUnit_one_sub_self_of_mem_nonunits
  refine (IsLocalRing.mem_maximalIdeal _).mp ?_
  rw [hπ.maximalIdeal_eq]
  exact Ideal.mem_span_singleton.mpr (dvd_pow_self π hr)

private noncomputable def lubinTateDefect (e ebar : LubinTateSeries A π)
    (H : MvPowerSeries σ A) : MvPowerSeries σ A :=
  PowerSeries.subst H e.toPowerSeries -
    MvPowerSeries.subst (fun i => lubinTateInVariable ebar i) H

omit [Finite (IsLocalRing.ResidueField A)] [Fintype σ] in
/-- The defect shift under a perturbation supported at or above the critical degree. -/
private theorem coeff_lubinTateDefect_add [Finite σ] (e ebar : LubinTateSeries A π)
    {H E : MvPowerSeries σ A} (hH : constantCoeff H = 0) (hE : constantCoeff E = 0)
    {d : σ →₀ ℕ} (hordE : (d.degree : ℕ∞) ≤ E.order) :
    coeff d (lubinTateDefect e ebar (H + E)) =
      coeff d (lubinTateDefect e ebar H) +
        π * coeff d E - π ^ d.degree * coeff d E := by
  have hHE : constantCoeff (H + E) = 0 := by rw [map_add, hH, hE, add_zero]
  have heside : coeff d (PowerSeries.subst (H + E) e.toPowerSeries) -
      coeff d (PowerSeries.subst H e.toPowerSeries) = π * coeff d E := by
    have := coeff_powerSeries_subst_sub hHE hH e.toPowerSeries (d := d)
      (by rw [add_sub_cancel_left]; exact hordE)
    rw [add_sub_cancel_left] at this
    rw [this, e.coeff_one_eq]
  have hmside : coeff d (MvPowerSeries.subst
        (fun i => lubinTateInVariable ebar i) (H + E)) =
      coeff d (MvPowerSeries.subst (fun i => lubinTateInVariable ebar i) H) +
        π ^ d.degree * coeff d E := by
    rw [subst_add (hasSubst_lubinTateInVariable ebar), map_add,
      coeff_subst_lubinTateInVariable ebar hordE]
  rw [lubinTateDefect, lubinTateDefect, map_sub, map_sub, hmside,
    eq_add_of_sub_eq heside]
  ring

open Classical in
private noncomputable def lubinTateCorrection (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) (H : MvPowerSeries σ A) (r : ℕ) :
    MvPowerSeries σ A :=
  fun d =>
    if h : constantCoeff H = 0 ∧ d.degree = r + 2 then
      (((isUnit_one_sub_uniformizer_pow hπ (show r + 1 ≠ 0 by omega)).unit⁻¹ : Aˣ) : A) *
        (- Classical.choose (dvd_coeff_defect hπ e ebar h.1 d))
    else 0

open Classical in
private theorem coeff_lubinTateCorrection (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) (H : MvPowerSeries σ A) (r : ℕ) (d : σ →₀ ℕ) :
    coeff d (lubinTateCorrection hπ e ebar H r) =
      if h : constantCoeff H = 0 ∧ d.degree = r + 2 then
        (((isUnit_one_sub_uniformizer_pow hπ (show r + 1 ≠ 0 by omega)).unit⁻¹ : Aˣ) : A) *
          (- Classical.choose (dvd_coeff_defect hπ e ebar h.1 d))
      else 0 :=
  rfl

private theorem le_order_lubinTateCorrection (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) (H : MvPowerSeries σ A) (r : ℕ) :
    (((r + 2 : ℕ)) : ℕ∞) ≤ (lubinTateCorrection hπ e ebar H r).order := by
  apply le_order
  intro d hd
  rw [coeff_lubinTateCorrection, dif_neg]
  rintro ⟨-, hdeg⟩
  have : d.degree < r + 2 := by exact_mod_cast hd
  omega

private theorem constantCoeff_lubinTateCorrection (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) (H : MvPowerSeries σ A) (r : ℕ) :
    constantCoeff (lubinTateCorrection hπ e ebar H r) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_lubinTateCorrection, dif_neg]
  rintro ⟨-, hdeg⟩
  simp at hdeg

private noncomputable def lubinTateApprox (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) (L : σ → A) : ℕ → MvPowerSeries σ A
  | 0 => lubinTateLinearForm L
  | r + 1 => lubinTateApprox hπ e ebar L r +
      lubinTateCorrection hπ e ebar (lubinTateApprox hπ e ebar L r) r

private theorem hasLinearTerm_lubinTateApprox (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) (L : σ → A) (r : ℕ) :
    LubinTateHasLinearTerm (lubinTateApprox hπ e ebar L r) L := by
  induction r with
  | zero => exact lubinTateLinearForm_hasLinearTerm L
  | succ r IH =>
    rw [LubinTateHasLinearTerm, lubinTateApprox, add_sub_right_comm]
    refine le_trans (le_min IH ?_) min_order_le_add
    exact le_trans (by exact_mod_cast (by omega : 2 ≤ r + 2))
      (le_order_lubinTateCorrection hπ e ebar _ r)

private theorem le_order_defect_lubinTateApprox (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) (L : σ → A) (r : ℕ) :
    (((r + 2 : ℕ)) : ℕ∞) ≤
      (lubinTateDefect e ebar (lubinTateApprox hπ e ebar L r)).order := by
  induction r with
  | zero =>
    apply le_order
    intro d hd
    have hd2 : d.degree < 2 := by exact_mod_cast hd
    have hdeg1 : (d.degree : ℕ∞) ≤ (lubinTateLinearForm L).order := by
      refine le_trans ?_ (one_le_order_lubinTateLinearForm L)
      exact_mod_cast (by omega : d.degree ≤ 1)
    have hzero : PowerSeries.subst (0 : MvPowerSeries σ A) e.toPowerSeries = 0 := by
      ext u
      rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero (map_zero _))]
      rw [map_zero]
      apply finsum_eq_zero_of_forall_eq_zero
      intro k
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp
      · rw [zero_pow (by omega), map_zero, smul_zero]
    have heside : coeff d (PowerSeries.subst (lubinTateLinearForm L) e.toPowerSeries) =
        π * coeff d (lubinTateLinearForm L) := by
      have := coeff_powerSeries_subst_sub (H := lubinTateLinearForm L)
        (H' := (0 : MvPowerSeries σ A)) (constantCoeff_lubinTateLinearForm L)
        (map_zero _) e.toPowerSeries (d := d) (by rw [sub_zero]; exact hdeg1)
      rw [sub_zero, hzero, map_zero, sub_zero] at this
      rw [this, e.coeff_one_eq]
    rw [lubinTateApprox, lubinTateDefect, map_sub, heside,
      coeff_subst_lubinTateInVariable ebar hdeg1]
    interval_cases hdd : d.degree
    · have hd0 : d = 0 := by rwa [← Finsupp.degree_eq_zero_iff (d := d)]
      rw [hd0, coeff_zero_eq_constantCoeff_apply, constantCoeff_lubinTateLinearForm]
      ring
    · rw [pow_one]
      ring
  | succ r IH =>
    apply le_order
    intro d hd
    have hdr : d.degree < r + 3 := by exact_mod_cast hd
    have hH0 : constantCoeff (lubinTateApprox hπ e ebar L r) = 0 :=
      (hasLinearTerm_lubinTateApprox hπ e ebar L r).constantCoeff_eq_zero
    have hE0 : constantCoeff
        (lubinTateCorrection hπ e ebar (lubinTateApprox hπ e ebar L r) r) = 0 :=
      constantCoeff_lubinTateCorrection hπ e ebar _ r
    have hordE : (d.degree : ℕ∞) ≤
        (lubinTateCorrection hπ e ebar (lubinTateApprox hπ e ebar L r) r).order := by
      refine le_trans ?_ (le_order_lubinTateCorrection hπ e ebar _ r)
      exact_mod_cast (by omega : d.degree ≤ r + 2)
    rw [lubinTateApprox, coeff_lubinTateDefect_add e ebar hH0 hE0 hordE]
    rcases Nat.lt_or_ge d.degree (r + 2) with hlt | hge
    · have h1 : coeff d (lubinTateDefect e ebar (lubinTateApprox hπ e ebar L r)) = 0 := by
        apply coeff_of_lt_order
        refine lt_of_lt_of_le ?_ IH
        exact_mod_cast hlt
      have h2 : coeff d
          (lubinTateCorrection hπ e ebar (lubinTateApprox hπ e ebar L r) r) = 0 := by
        rw [coeff_lubinTateCorrection, dif_neg]
        rintro ⟨-, hdeg⟩
        omega
      rw [h1, h2]
      ring
    · have hdeg : d.degree = r + 2 := by omega
      set H := lubinTateApprox hπ e ebar L r with hHdef
      have hspec := Classical.choose_spec (dvd_coeff_defect hπ e ebar hH0 d)
      set nd := Classical.choose (dvd_coeff_defect hπ e ebar hH0 d) with hnd
      have hu := isUnit_one_sub_uniformizer_pow (π := π) hπ (show r + 1 ≠ 0 by omega)
      have hcoeffE : coeff d (lubinTateCorrection hπ e ebar H r) =
          ((hu.unit⁻¹ : Aˣ) : A) * (- nd) := by
        rw [coeff_lubinTateCorrection, dif_pos ⟨hH0, hdeg⟩]
      have hdefect : coeff d (lubinTateDefect e ebar H) = π * nd := hspec
      rw [hcoeffE, hdefect, hdeg]
      have hcancel : (1 - π ^ (r + 1)) * (((hu.unit⁻¹ : Aˣ) : A) * (- nd)) = - nd := by
        have hval : (hu.unit : A) = 1 - π ^ (r + 1) := hu.unit_spec
        calc (1 - π ^ (r + 1)) * (((hu.unit⁻¹ : Aˣ) : A) * (- nd))
            = ((hu.unit : A) * ((hu.unit⁻¹ : Aˣ) : A)) * (- nd) := by
              rw [hval]; ring
          _ = - nd := by
              rw [← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
      linear_combination π * hcancel

private theorem coeff_lubinTateApprox_stable (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) (L : σ → A) {d : σ →₀ ℕ} {r s : ℕ}
    (hr : d.degree ≤ r + 1) (hrs : r ≤ s) :
    coeff d (lubinTateApprox hπ e ebar L s) =
      coeff d (lubinTateApprox hπ e ebar L r) := by
  induction s with
  | zero =>
    have : r = 0 := by omega
    subst this
    rfl
  | succ s IH =>
    rcases Nat.eq_or_lt_of_le hrs with rfl | hlt
    · rfl
    · have hrs' : r ≤ s := by omega
      rw [lubinTateApprox, map_add, IH hrs']
      have hzero : coeff d (lubinTateCorrection hπ e ebar
          (lubinTateApprox hπ e ebar L s) s) = 0 := by
        rw [coeff_lubinTateCorrection, dif_neg]
        rintro ⟨-, hdeg⟩
        omega
      rw [hzero, add_zero]

/-- The **Lubin–Tate intertwiner**: the unique multivariable series with prescribed
linear term `L` intertwining `e` with `ē`, built degree by degree — Milne's induction
read off at the stabilized stage
([Milne 2020, Chap. I, §2, Lem. 2.11, p.32][MilneCFT]; Yamaguchi 2026,
`LubinTate/FormalModule/RecursiveIntertwiner.lean:382`). -/
noncomputable def lubinTateIntertwiner (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) (L : σ → A) : MvPowerSeries σ A :=
  fun d => coeff d (lubinTateApprox hπ e ebar L d.degree)

private theorem coeff_lubinTateIntertwiner_eq (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) (L : σ → A) {d : σ →₀ ℕ} {r : ℕ}
    (hr : d.degree ≤ r + 1) :
    coeff d (lubinTateIntertwiner hπ e ebar L) =
      coeff d (lubinTateApprox hπ e ebar L r) := by
  rw [show coeff d (lubinTateIntertwiner hπ e ebar L) =
      coeff d (lubinTateApprox hπ e ebar L d.degree) from coeff_apply _ d]
  rcases le_total d.degree r with hdr | hrd
  · exact (coeff_lubinTateApprox_stable hπ e ebar L (by omega) hdr).symm
  · exact coeff_lubinTateApprox_stable hπ e ebar L hr hrd

/-- The intertwiner carries the prescribed linear term
([Milne 2020, Chap. I, §2, Lem. 2.11, p.32][MilneCFT];
Yamaguchi 2026,
`LubinTate/FormalModule/RecursiveIntertwiner.lean:419`). -/
theorem lubinTateIntertwiner_hasLinearTerm (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) (L : σ → A) :
    LubinTateHasLinearTerm (lubinTateIntertwiner hπ e ebar L) L := by
  rw [LubinTateHasLinearTerm]
  apply le_order
  intro d hd
  rw [map_sub, coeff_lubinTateIntertwiner_eq hπ e ebar L (r := d.degree) (by omega),
    (hasLinearTerm_lubinTateApprox hπ e ebar L d.degree).coeff_eq_of_degree_lt_two hd,
    sub_self]

/-- The intertwiner solves the intertwining equation
([Milne 2020, Chap. I, §2, Lem. 2.11, p.32][MilneCFT];
Yamaguchi 2026,
`LubinTate/FormalModule/RecursiveIntertwiner.lean:485`). -/
theorem lubinTateIntertwiner_intertwines (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) (L : σ → A) :
    LubinTateIntertwines e ebar (lubinTateIntertwiner hπ e ebar L) := by
  set F := lubinTateIntertwiner hπ e ebar L with hF
  have hdefect : ∀ d : σ →₀ ℕ, coeff d (lubinTateDefect e ebar F) = 0 := by
    intro d
    set r := d.degree with hrdef
    have hordD : (((d.degree + 1 : ℕ)) : ℕ∞) ≤
        (F - lubinTateApprox hπ e ebar L r).order := by
      apply le_order
      intro u hu
      have hu' : u.degree ≤ d.degree := by exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast hu)
      rw [map_sub, coeff_lubinTateIntertwiner_eq hπ e ebar L (r := r) (by omega), sub_self]
    have h0 : constantCoeff (lubinTateApprox hπ e ebar L r) = 0 :=
      (hasLinearTerm_lubinTateApprox hπ e ebar L r).constantCoeff_eq_zero
    have hD0 : constantCoeff (F - lubinTateApprox hπ e ebar L r) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      apply coeff_of_lt_order
      refine lt_of_lt_of_le ?_ hordD
      simp
    have hsum : lubinTateApprox hπ e ebar L r +
        (F - lubinTateApprox hπ e ebar L r) = F := by abel
    have hkey := coeff_lubinTateDefect_add e ebar h0 hD0
      (E := F - lubinTateApprox hπ e ebar L r) (d := d)
      (le_trans (by exact_mod_cast (by omega : d.degree ≤ d.degree + 1)) hordD)
    rw [hsum] at hkey
    have hz1 : coeff d (lubinTateDefect e ebar (lubinTateApprox hπ e ebar L r)) = 0 := by
      apply coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (le_order_defect_lubinTateApprox hπ e ebar L r)
      exact_mod_cast (by omega : d.degree < r + 2)
    have hz2 : coeff d (F - lubinTateApprox hπ e ebar L r) = 0 := by
      rw [map_sub, coeff_lubinTateIntertwiner_eq hπ e ebar L (r := r) (by omega), sub_self]
    rw [hkey, hz1, hz2]
    ring
  rw [LubinTateIntertwines]
  ext d
  have := hdefect d
  rw [lubinTateDefect, map_sub, sub_eq_zero] at this
  exact this

omit [Finite (IsLocalRing.ResidueField A)] in
/-- Uniqueness: two intertwiners with the same linear term agree
([Milne 2020, Chap. I, §2, Lem. 2.11, p.32][MilneCFT];
Yamaguchi 2026,
`LubinTate/FormalModule/RecursiveIntertwiner.lean:996`). -/
theorem LubinTateIntertwines.eq_of_hasLinearTerm (hπ : Irreducible π)
    {e ebar : LubinTateSeries A π} {H H' : MvPowerSeries σ A} {L : σ → A}
    (hH : LubinTateHasLinearTerm H L) (hI : LubinTateIntertwines e ebar H)
    (hH' : LubinTateHasLinearTerm H' L) (hI' : LubinTateIntertwines e ebar H') : H = H' := by
  have key : ∀ n : ℕ, ∀ u : σ →₀ ℕ, u.degree = n → coeff u H = coeff u H' := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n IH =>
      intro u hu
      rcases Nat.lt_or_ge n 2 with hn2 | hn2
      · rw [hH.coeff_eq_of_degree_lt_two (by rw [hu]; exact_mod_cast hn2),
          hH'.coeff_eq_of_degree_lt_two (by rw [hu]; exact_mod_cast hn2)]
      · have hord : ((n : ℕ) : ℕ∞) ≤ (H' - H).order := by
          apply le_order
          intro v hv
          have hv' : v.degree < n := by exact_mod_cast hv
          rw [map_sub, IH v.degree hv' v rfl, sub_self]
        have hDc : constantCoeff (H' - H) = 0 := by
          rw [map_sub, hH.constantCoeff_eq_zero, hH'.constantCoeff_eq_zero, sub_zero]
        have hsum : H + (H' - H) = H' := by abel
        have hkey := coeff_lubinTateDefect_add e ebar hH.constantCoeff_eq_zero hDc
          (E := H' - H) (d := u) (by rw [hu]; exact hord)
        rw [hsum] at hkey
        have hz1 : coeff u (lubinTateDefect e ebar H) = 0 := by
          rw [lubinTateDefect, hI, sub_self, map_zero]
        have hz2 : coeff u (lubinTateDefect e ebar H') = 0 := by
          rw [lubinTateDefect, hI', sub_self, map_zero]
        rw [hz1, hz2, hu] at hkey
        have hfactor : π * ((1 - π ^ (n - 1)) * coeff u (H' - H)) = 0 := by
          have hn1 : π ^ n = π * π ^ (n - 1) := by
            rw [← pow_succ']
            congr 1
            omega
          linear_combination -hkey + (coeff u (H' - H)) * hn1
        have hu1 : IsUnit (1 - π ^ (n - 1)) :=
          isUnit_one_sub_uniformizer_pow hπ (show n - 1 ≠ 0 by omega)
        have hπ0 : π ≠ 0 := hπ.ne_zero
        have hc : coeff u (H' - H) = 0 := by
          rcases mul_eq_zero.mp hfactor with h | h
          · exact absurd h hπ0
          · rcases mul_eq_zero.mp h with h' | h'
            · exact absurd h' hu1.ne_zero
            · exact h'
        rw [map_sub, sub_eq_zero] at hc
        exact hc.symm
  ext u
  exact key u.degree u rfl

/-- **Lubin–Tate's fundamental lemma**: a unique intertwiner with any prescribed linear
term ([Milne 2020, Chap. I, §2, Lem. 2.11, p.32][MilneCFT]; Yamaguchi 2026,
`LubinTate/FormalModule/RecursiveIntertwiner.lean:1011`). -/
theorem existsUnique_lubinTateIntertwiner (hπ : Irreducible π)
    (e ebar : LubinTateSeries A π) (L : σ → A) :
    ∃! H : MvPowerSeries σ A,
      LubinTateHasLinearTerm H L ∧ LubinTateIntertwines e ebar H :=
  ⟨lubinTateIntertwiner hπ e ebar L,
    ⟨lubinTateIntertwiner_hasLinearTerm hπ e ebar L,
      lubinTateIntertwiner_intertwines hπ e ebar L⟩,
    fun _ h => LubinTateIntertwines.eq_of_hasLinearTerm hπ h.1 h.2
      (lubinTateIntertwiner_hasLinearTerm hπ e ebar L)
      (lubinTateIntertwiner_intertwines hπ e ebar L)⟩

end Recursion

end Atlas.Knowledge
