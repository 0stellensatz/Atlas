import Mathlib
import Atlas.Knowledge.HasseDerivativeZeros
import Atlas.Knowledge.PadicComplexGaloisAction

/-!
# conjugate diameter bound

Ax's descent estimate: an algebraic element whose conjugates over an intermediate field all
lie within `Δ` of it, lies within `Δ * p ^ (p / (p - 1) ^ 2)` of the intermediate field
itself. This is the quantitative heart of the Ax–Sen–Tate theorem: almost-invariance under
the Galois group is almost-membership in the fixed field, with a loss depending only on `p`.
`Atlas.Knowledge.axSenTate` consumes it after the Krull correspondence turns almost-invariance
into a conjugate-diameter bound.

## Main statements

* `conjugateDiameterBound` — Ax's Proposition 1: an element of the algebraic closure lies
  within `Δ * p ^ (p / (p - 1) ^ 2)` of `F` whenever its conjugates over `F` lie within `Δ`
  of it.

## Implementation notes

The proof is Ax's induction on the degree `n` of the minimal polynomial, walking the
conjugate cluster down through zeros of Hasse derivatives
(`Atlas.Knowledge.HasseDerivativeZeros`). When `n = p ^ δ * d₁` with `d₁ > 1` prime to `p`,
the `p ^ δ`th Hasse derivative of the minimal polynomial has a zero `β` inside the cluster at
no cost; when `n = p ^ δ` is a full `p`-power the cluster grows by
`p ^ (1 / (p ^ δ - p ^ (δ - 1)))`, and these charges sum over the tower of `p`-powers below
`n` to less than `p / (p - 1) ^ 2`. The zero `β` has degree at most `n` minus the order of
the derivative, its own conjugate cluster is no wider than the one it came from—conjugating
by an automorphism over `F` is an isometry, because the norm of the algebraic closure is the
spectral norm—and induction produces the fixed-field element near `β`, hence near `α`.

The accumulated charge is bookkept additively in a real exponent: `chargeSum p n` is the sum
of `(p ^ i - p ^ (i - 1))⁻¹` over `1 ≤ i ≤ Nat.log p n`, the bound of Ax's Lemma 4, and the
headline relaxes it to the geometric-series bound `p / (p - 1) ^ 2` of his Proposition 1.
Real powers of `p` carry it multiplicatively.

## References

* [Ax1970] J. Ax, *Zeros of polynomials over local fields—The Galois action*, J. Algebra
  **15** (1970), 417–428.
-/

open Polynomial

namespace Atlas.Knowledge

namespace ConjugateDiameterBound

/-- The accumulated charge of Ax's induction: the sum of `(p ^ i - p ^ (i - 1))⁻¹` over the
`p`-power levels `1 ≤ i ≤ log_p n` ([Ax 1970, §2, Lemma 4, p.421][Ax1970], the sum
`∑ (p^i - p^(i-1))⁻¹ ord p`). -/
noncomputable def chargeSum (p n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 (Nat.log p n), ((p : ℝ) ^ i - (p : ℝ) ^ (i - 1))⁻¹

variable {p : ℕ}

/-- The accumulated charge is nonnegative. -/
theorem chargeSum_nonneg (hp : 2 ≤ p) (n : ℕ) : 0 ≤ chargeSum p n := by
  refine Finset.sum_nonneg fun i hi => ?_
  rw [Finset.mem_Icc] at hi
  have h1 : (p : ℝ) ^ (i - 1) < (p : ℝ) ^ i := by
    refine pow_lt_pow_right₀ (by exact_mod_cast hp.trans_lt' one_lt_two) ?_
    omega
  positivity

/-- The accumulated charge is monotone in the degree. -/
theorem chargeSum_mono (hp : 2 ≤ p) {m n : ℕ} (hmn : m ≤ n) :
    chargeSum p m ≤ chargeSum p n := by
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.Icc_subset_Icc_right (Nat.log_mono_right hmn)) fun i hi _ => ?_
  rw [Finset.mem_Icc] at hi
  have h1 : (p : ℝ) ^ (i - 1) < (p : ℝ) ^ i := by
    refine pow_lt_pow_right₀ (by exact_mod_cast hp.trans_lt' one_lt_two) ?_
    omega
  positivity

/-- The inductive charge step: below a full `p`-power, the charge of the derivative's degree
plus the new level's charge stays within the charge of `p ^ δ`. -/
theorem chargeSum_step (hp : 2 ≤ p) {δ m : ℕ} (hδ : 0 < δ)
    (hm : m ≤ p ^ δ - p ^ (δ - 1)) :
    chargeSum p m + ((p : ℝ) ^ δ - (p : ℝ) ^ (δ - 1))⁻¹ ≤ chargeSum p (p ^ δ) := by
  have hp0 : 0 < p := by omega
  have hlogm : Nat.log p m ≤ δ - 1 := by
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · have hlt : m < p ^ δ := lt_of_le_of_lt hm (by
        have : 0 < p ^ (δ - 1) := Nat.pow_pos hp0
        omega)
      have := Nat.log_lt_of_lt_pow (by omega) hlt
      omega
  have hlogp : Nat.log p (p ^ δ) = δ := Nat.log_pow (by omega) δ
  have hsub : chargeSum p m ≤ ∑ i ∈ Finset.Icc 1 (δ - 1),
      ((p : ℝ) ^ i - (p : ℝ) ^ (i - 1))⁻¹ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right hlogm) fun i hi _ => ?_
    rw [Finset.mem_Icc] at hi
    have h1 : (p : ℝ) ^ (i - 1) < (p : ℝ) ^ i := by
      refine pow_lt_pow_right₀ (by exact_mod_cast hp.trans_lt' one_lt_two) ?_
      omega
    positivity
  have hsplit : ∑ i ∈ Finset.Icc 1 δ, ((p : ℝ) ^ i - (p : ℝ) ^ (i - 1))⁻¹
      = (∑ i ∈ Finset.Icc 1 (δ - 1), ((p : ℝ) ^ i - (p : ℝ) ^ (i - 1))⁻¹)
        + ((p : ℝ) ^ δ - (p : ℝ) ^ (δ - 1))⁻¹ := by
    rw [show δ = (δ - 1) + 1 by omega, Finset.sum_Icc_succ_top (by omega)]
    congr 2
  simp only [chargeSum] at hsub ⊢
  rw [hlogp, hsplit]
  linarith

/-- The geometric-series relaxation: the accumulated charge never exceeds `p / (p - 1) ^ 2`
([Ax 1970, §2, Prop. 1, p.422][Ax1970]). -/
theorem chargeSum_le (hp : 2 ≤ p) (n : ℕ) :
    chargeSum p n ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hterm : ∀ i ∈ Finset.Icc 1 (Nat.log p n),
      ((p : ℝ) ^ i - (p : ℝ) ^ (i - 1))⁻¹ = ((p : ℝ) - 1)⁻¹ * ((p : ℝ)⁻¹) ^ (i - 1) := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    have h1 : (p : ℝ) ^ i = (p : ℝ) ^ (i - 1) * p := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h1, show (p : ℝ) ^ (i - 1) * p - (p : ℝ) ^ (i - 1)
      = (p : ℝ) ^ (i - 1) * ((p : ℝ) - 1) by ring, mul_inv, inv_pow]
    ring
  rw [chargeSum, Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have hx0 : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  have hx1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have hgeom : ∑ i ∈ Finset.Icc 1 (Nat.log p n), ((p : ℝ)⁻¹) ^ (i - 1)
      ≤ (1 - (p : ℝ)⁻¹)⁻¹ := by
    have hre : ∑ i ∈ Finset.Icc 1 (Nat.log p n), ((p : ℝ)⁻¹) ^ (i - 1)
        = ∑ j ∈ Finset.range (Nat.log p n), ((p : ℝ)⁻¹) ^ j := by
      rw [show Finset.Icc 1 (Nat.log p n) = Finset.Ico 1 (Nat.log p n + 1) by
          ext x; simp, Finset.sum_Ico_eq_sum_range]
      refine Finset.sum_congr (by congr 1) fun j _ => by congr 1; omega
    rw [hre]
    calc ∑ j ∈ Finset.range (Nat.log p n), ((p : ℝ)⁻¹) ^ j
        ≤ ∑' j : ℕ, ((p : ℝ)⁻¹) ^ j :=
          (summable_geometric_of_lt_one hx0 hx1).sum_le_tsum _ fun i _ => by positivity
      _ = (1 - (p : ℝ)⁻¹)⁻¹ := tsum_geometric_of_lt_one hx0 hx1
  calc ((p : ℝ) - 1)⁻¹ * ∑ i ∈ Finset.Icc 1 (Nat.log p n), ((p : ℝ)⁻¹) ^ (i - 1)
      ≤ ((p : ℝ) - 1)⁻¹ * (1 - (p : ℝ)⁻¹)⁻¹ :=
        mul_le_mul_of_nonneg_left hgeom (by positivity)
    _ = (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
        rw [show (1 - (p : ℝ)⁻¹) = ((p : ℝ) - 1) / p by field_simp]
        field_simp

variable [Fact p.Prime]

/-- Natural numbers prime to `p` have norm one in the algebraic closure: the spectral norm
extends the `p`-adic one. -/
theorem norm_natCast_eq_one {m : ℕ} (hm : ¬ p ∣ m) : ‖(m : PadicAlgCl p)‖ = 1 := by
  have hcast : ((m : ℚ_[p]) : PadicAlgCl p) = (m : PadicAlgCl p) := by push_cast; rfl
  rw [← hcast, PadicAlgCl.norm_extends, Padic.norm_natCast_eq_one_iff]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hm

/-- The norm of `p` in the algebraic closure is `p⁻¹`. -/
theorem norm_natCast_self : ‖(p : PadicAlgCl p)‖ = ((p : ℝ))⁻¹ := by
  have hcast : ((p : ℚ_[p]) : PadicAlgCl p) = (p : PadicAlgCl p) := by push_cast; rfl
  rw [← hcast, PadicAlgCl.norm_extends, Padic.norm_p]

/-- Every `ℚ_[p]`-algebra automorphism of the algebraic closure preserves the norm: the
spectral norm is invariant. -/
theorem norm_algEquiv (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p) :
    ‖σ x‖ = ‖x‖ := by
  have h := (PadicComplexGaloisAction.isometry (p := p) σ).dist_eq x 0
  simpa [PadicComplexGaloisAction.toAlgEquiv, dist_eq_norm] using h

/-- Passing the diameter bound down a descent step: if `β` lies within `Δ` of `α` and the
conjugates of `α` over `F` lie within `Δ` of `α`, the conjugates of `β` over `F` lie within
`Δ` of `β`—conjugation over `F` is an isometry, and both legs of the detour through `α` are
short. -/
theorem conjugates_le (F : IntermediateField ℚ_[p] (PadicAlgCl p)) {α β : PadicAlgCl p}
    {Δ : ℝ} (hβα : ‖β - α‖ ≤ Δ)
    (hαconj : ∀ γ : PadicAlgCl p, (Polynomial.aeval γ) (minpoly ↥F α) = 0 → ‖γ - α‖ ≤ Δ) :
    ∀ γ : PadicAlgCl p, (Polynomial.aeval γ) (minpoly ↥F β) = 0 → ‖γ - β‖ ≤ Δ := by
  intro γ hγ
  obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
    (Algebra.IsAlgebraic.isAlgebraic (R := ↥F) β) hγ
  have hiso : ∀ x : PadicAlgCl p, ‖σ x‖ = ‖x‖ := fun x =>
    norm_algEquiv (AlgEquiv.restrictScalars ℚ_[p] σ) x
  have hσα : ‖σ α - α‖ ≤ Δ := by
    refine hαconj (σ α) ?_
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hdecomp : γ - β = σ (β - α) + ((σ α - α) + (α - β)) := by
    rw [← hσ, map_sub]
    ring
  rw [hdecomp]
  refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_
    (le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hσα ?_)))
  · rw [hiso]
    exact hβα
  · rw [norm_sub_rev]
    exact hβα

/-- The descent: at minimal-polynomial degree `n` the loss is `p` raised to the accumulated
charge `chargeSum p n`—strong induction on `n`, alternating the two zero-location lemmas of
`Atlas.Knowledge.HasseDerivativeZeros` ([Ax 1970, §2, proof of Prop. 1, pp.421–422][Ax1970]). -/
private theorem descent (n : ℕ) :
    ∀ (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (α : PadicAlgCl p) (Δ : ℝ), 0 ≤ Δ →
      (minpoly ↥F α).natDegree = n →
      (∀ β : PadicAlgCl p, (Polynomial.aeval β) (minpoly ↥F α) = 0 → ‖β - α‖ ≤ Δ) →
      ∃ a ∈ F, ‖α - a‖ ≤ Δ * (p : ℝ) ^ chargeSum p n := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro F α Δ hΔ0 hdeg hconj
  have hp' : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp'.two_le
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.one_lt.le
  have hint : IsIntegral ↥F α := (Algebra.IsAlgebraic.isAlgebraic (R := ↥F) α).isIntegral
  have hn0 : 0 < n := hdeg ▸ minpoly.natDegree_pos hint
  have hRHS0 : 0 ≤ Δ * (p : ℝ) ^ chargeSum p n :=
    mul_nonneg hΔ0 (Real.rpow_nonneg (by positivity) _)
  have hn1 : 1 ≤ n := hn0
  rcases eq_or_lt_of_le hn1 with h1 | h1
  · -- degree one: `α` already lies in `F`
    have hd1 : (minpoly ↥F α).natDegree = 1 := by rw [hdeg, ← h1]
    rw [minpoly.natDegree_eq_one_iff] at hd1
    obtain ⟨a, ha⟩ := hd1
    refine ⟨a, a.2, ?_⟩
    rw [← ha]
    simpa using hRHS0
  -- shared bookkeeping: the mapped minimal polynomial and its root cluster
  set P := minpoly ↥F α with hP
  haveI : CharZero ↥F := charZero_of_injective_algebraMap (algebraMap ℚ_[p] ↥F).injective
  have hPmonic : P.Monic := minpoly.monic hint
  have hfmonic : (P.map (algebraMap ↥F (PadicAlgCl p))).Monic := hPmonic.map _
  have hfdeg : (P.map (algebraMap ↥F (PadicAlgCl p))).natDegree = n := by
    rw [hPmonic.natDegree_map]
    exact hdeg
  have hfroots : ∀ z : PadicAlgCl p,
      (P.map (algebraMap ↥F (PadicAlgCl p))).IsRoot z → ‖z - α‖ ≤ Δ := by
    intro z hz
    refine hconj z ?_
    rwa [Polynomial.IsRoot, Polynomial.eval_map_algebraMap] at hz
  -- the shared descent step: a zero `β` of the `q`th Hasse derivative inside the (possibly
  -- enlarged) cluster hands the induction to a smaller degree
  have step : ∀ q : ℕ, 1 ≤ q → q ≤ n → ∀ β : PadicAlgCl p, ∀ Δ' : ℝ, 0 ≤ Δ' → Δ ≤ Δ' →
      ((P.map (algebraMap ↥F (PadicAlgCl p))).hasseDeriv q).IsRoot β → ‖β - α‖ ≤ Δ' →
      Δ' * (p : ℝ) ^ chargeSum p (n - q) ≤ Δ * (p : ℝ) ^ chargeSum p n →
      ∃ a ∈ F, ‖α - a‖ ≤ Δ * (p : ℝ) ^ chargeSum p n := by
    intro q hq1 hqn β Δ' hΔ'0 hΔΔ' hβroot hβα hkey
    -- the Hasse derivative commutes with the coefficient map
    have hcomm : (P.map (algebraMap ↥F (PadicAlgCl p))).hasseDeriv q
        = (P.hasseDeriv q).map (algebraMap ↥F (PadicAlgCl p)) := by
      ext k
      simp [Polynomial.hasseDeriv_coeff, Polynomial.coeff_map]
    have hβaeval : (Polynomial.aeval β) (P.hasseDeriv q) = 0 := by
      rw [← Polynomial.eval_map_algebraMap, ← hcomm]
      exact hβroot
    have hdvd : minpoly ↥F β ∣ P.hasseDeriv q := minpoly.dvd _ _ hβaeval
    -- the derivative is nonzero: its `(n - q)`th coefficient is a binomial coefficient
    have hge : (P.hasseDeriv q).coeff (n - q) = ((n.choose q : ℕ) : ↥F) := by
      rw [Polynomial.hasseDeriv_coeff, show n - q + q = n by omega, ← hdeg,
        hPmonic.coeff_natDegree, mul_one, hdeg]
    have hne : ((n.choose q : ℕ) : ↥F) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.choose_pos hqn).ne'
    have hgne : P.hasseDeriv q ≠ 0 := fun h0 =>
      hne (by rw [← hge, h0, Polynomial.coeff_zero])
    have hm_le : (minpoly ↥F β).natDegree ≤ n - q := by
      refine le_trans (Polynomial.natDegree_le_of_dvd hdvd hgne) ?_
      have h := Polynomial.natDegree_hasseDeriv_le P q
      omega
    have hm_lt : (minpoly ↥F β).natDegree < n := by omega
    -- the conjugates of `β` cluster within the enlarged diameter, and induction descends
    have hβconj : ∀ γ : PadicAlgCl p, (Polynomial.aeval γ) (minpoly ↥F β) = 0 → ‖γ - β‖ ≤ Δ' :=
      conjugates_le F hβα fun γ hγ => (hconj γ hγ).trans hΔΔ'
    obtain ⟨a, haF, ha⟩ := IH _ hm_lt F β Δ' hΔ'0 rfl hβconj
    refine ⟨a, haF, ?_⟩
    have hchain : Δ' * (p : ℝ) ^ chargeSum p (minpoly ↥F β).natDegree
        ≤ Δ * (p : ℝ) ^ chargeSum p n :=
      le_trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hp1R (chargeSum_mono hp2 hm_le)) hΔ'0) hkey
    have hβa : ‖β - a‖ ≤ Δ * (p : ℝ) ^ chargeSum p n := le_trans ha hchain
    have hαβ : ‖α - β‖ ≤ Δ * (p : ℝ) ^ chargeSum p n := by
      rw [norm_sub_rev]
      refine le_trans hβα (le_trans ?_ hkey)
      nth_rewrite 1 [← mul_one Δ']
      exact mul_le_mul_of_nonneg_left
        (Real.one_le_rpow hp1R (chargeSum_nonneg hp2 _)) hΔ'0
    rw [show α - a = (α - β) + (β - a) by ring]
    exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le hαβ hβa)
  -- split off the `p`-part of the degree to decide which zero-location lemma applies
  obtain ⟨δ, d₁, hd₁, hn_eq⟩ : ∃ δ d₁, ¬ p ∣ d₁ ∧ n = p ^ δ * d₁ :=
    ⟨n.factorization p, ordCompl[p] n, Nat.not_dvd_ordCompl hp' (by omega),
      (Nat.ordProj_mul_ordCompl_eq_self n p).symm⟩
  rcases Nat.lt_or_ge 1 d₁ with hd₁1 | hd₁le
  · -- the degree is not a `p`-power: Ax's Lemma 2 finds a zero at no cost
    obtain ⟨β, hβroot, hβα⟩ := HasseDerivativeZeros.exists_isRoot_hasseDeriv hp'
      (fun m hm => norm_natCast_eq_one hm) _ hfmonic (by rw [hfdeg, hn_eq]) hd₁ hd₁1 α hΔ0
      hfroots
    refine step (p ^ δ) (Nat.one_le_pow _ _ hp'.pos) ?_ β Δ hΔ0 le_rfl hβroot hβα ?_
    · rw [hn_eq]
      exact Nat.le_mul_of_pos_right _ (by omega)
    · exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hp1R (chargeSum_mono hp2 (Nat.sub_le _ _))) hΔ0
  · -- the degree is a full `p`-power: Ax's Lemma 3 enlarges the cluster by the charge
    have hd₁eq : d₁ = 1 := by
      have : d₁ ≠ 0 := by
        rintro rfl
        omega
      omega
    subst hd₁eq
    rw [mul_one] at hn_eq
    have hδpos : 0 < δ := by
      rcases Nat.eq_zero_or_pos δ with rfl | h
      · rw [pow_zero] at hn_eq
        omega
      · exact h
    set e := p ^ δ - p ^ (δ - 1) with he
    have hple : p ^ (δ - 1) ≤ p ^ δ := Nat.pow_le_pow_right hp'.pos (by omega)
    have hepos : 0 < e := by
      have := Nat.pow_lt_pow_right hp'.one_lt (show δ - 1 < δ by omega)
      omega
    obtain ⟨β, hβroot, hβpow⟩ := HasseDerivativeZeros.exists_isRoot_hasseDeriv_pow hp'
      (fun m hm => norm_natCast_eq_one hm) _ hfmonic hδpos (by rw [hfdeg, hn_eq]) α hΔ0
      hfroots
    rw [← he, norm_natCast_self, inv_inv] at hβpow
    -- take `e`th roots: the zero lies within the cluster enlarged by `p ^ e⁻¹`
    have hβα : ‖β - α‖ ≤ Δ * (p : ℝ) ^ ((e : ℝ)⁻¹) := by
      have hroot : ‖β - α‖ = (‖β - α‖ ^ (e : ℕ)) ^ ((e : ℝ)⁻¹) := by
        rw [← Real.rpow_natCast (‖β - α‖) e, ← Real.rpow_mul (norm_nonneg _),
          mul_inv_cancel₀ (by exact_mod_cast hepos.ne' : (e : ℝ) ≠ 0), Real.rpow_one]
      rw [hroot]
      calc (‖β - α‖ ^ (e : ℕ)) ^ ((e : ℝ)⁻¹)
          ≤ (Δ ^ (e : ℕ) * (p : ℝ)) ^ ((e : ℝ)⁻¹) :=
            Real.rpow_le_rpow (by positivity) hβpow (by positivity)
        _ = Δ * (p : ℝ) ^ ((e : ℝ)⁻¹) := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast Δ e,
              ← Real.rpow_mul hΔ0, mul_inv_cancel₀ (by exact_mod_cast hepos.ne'),
              Real.rpow_one]
    -- the enlargement is priced by the charge step
    have hcaste : (e : ℝ) = (p : ℝ) ^ δ - (p : ℝ) ^ (δ - 1) := by
      rw [he, Nat.cast_sub hple]
      push_cast
      ring
    have hkey : (Δ * (p : ℝ) ^ ((e : ℝ)⁻¹)) * (p : ℝ) ^ chargeSum p (n - p ^ (δ - 1))
        ≤ Δ * (p : ℝ) ^ chargeSum p n := by
      have hsub : n - p ^ (δ - 1) = e := by rw [hn_eq, he]
      rw [hsub, mul_assoc, ← Real.rpow_add (by positivity : (0 : ℝ) < p), hn_eq]
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1R ?_) hΔ0
      have hstep := chargeSum_step hp2 hδpos (le_refl e)
      rw [hcaste]
      linarith
    exact step (p ^ (δ - 1)) (Nat.one_le_pow _ _ hp'.pos) (hn_eq ▸ hple) β
      (Δ * (p : ℝ) ^ ((e : ℝ)⁻¹)) (by positivity)
      (le_mul_of_one_le_right hΔ0 (Real.one_le_rpow hp1R (by positivity))) hβroot hβα hkey

end ConjugateDiameterBound

/-- The **conjugate diameter bound**, Ax's Proposition 1: if every conjugate of `α` over an
intermediate field `F` of the algebraic closure of `ℚ_[p]` lies within `Δ` of `α`, then `α`
lies within `Δ * p ^ (p / (p - 1) ^ 2)` of `F` itself
([Ax 1970, §2, Prop. 1, p.422][Ax1970]). -/
theorem conjugateDiameterBound {p : ℕ} [Fact p.Prime]
    (F : IntermediateField ℚ_[p] (PadicAlgCl p)) (α : PadicAlgCl p) {Δ : ℝ} (hΔ0 : 0 ≤ Δ)
    (hΔ : ∀ β : PadicAlgCl p, (Polynomial.aeval β) (minpoly ↥F α) = 0 → ‖β - α‖ ≤ Δ) :
    ∃ a ∈ F, ‖α - a‖ ≤ Δ * (‖(p : PadicAlgCl p)‖⁻¹) ^ ((p : ℝ) / ((p : ℝ) - 1) ^ 2) := by
  have hp' : p.Prime := Fact.out
  have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.one_lt.le
  obtain ⟨a, haF, ha⟩ :=
    ConjugateDiameterBound.descent (minpoly ↥F α).natDegree F α Δ hΔ0 rfl hΔ
  refine ⟨a, haF, le_trans ha ?_⟩
  rw [ConjugateDiameterBound.norm_natCast_self, inv_inv]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hp1R
      (ConjugateDiameterBound.chargeSum_le hp'.two_le _)) hΔ0

end Atlas.Knowledge
