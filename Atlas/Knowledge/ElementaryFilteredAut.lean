import Mathlib
import Atlas.Knowledge.FiltAut
import Atlas.Knowledge.JumpSetVector
import Atlas.Knowledge.JumpSetExtremal

/-!
# elementary filtered automorphisms

The working members of the filtered automorphism group of a free model: the transvections
adding a multiple of one coordinate to another. Such a move is a linear automorphism outright;
it is *filtered* exactly when the multiplier raises the standard weight of the source level to
that of the target level, and for a multiplier `π^d` that is the inequality between the levels
that the jump order `Atlas.Knowledge.JumpOrder` packages. Composing such moves is how the
source conjugates an arbitrary vector of the free model into the normal form
`Atlas.Knowledge.JumpSetVector` of the `≤_ρ`-minimal points of its coordinate graph—the
normal-form theorem recorded here, with the finite composition argument as its intended proof.

## Main definitions

* `elementaryAut` — the transvection adding `c` times one coordinate to another.

## Main statements

* `elementaryAut_mem_filtAut` — the filteredness criterion for the multiplier.
* `standardWeight_pi_pow_mul_le` — the criterion holds for `π^d` when the target level reaches
  the source level in `d` steps of `ρ`.
* `exists_filtAut_eq_jumpSetVector`, `exists_filtAut_eq_jumpSetVector_star` — every vector of
  `π M_ρ^f` (resp. of `π (M_ρ^{f - 1} ⊕ M_ρ^*)`) is conjugate under the filtered automorphism
  group to the jump-set vector of the minimal points of its coordinate graph. Claims recorded
  ahead of their proofs.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {D : Finset (ℕ+ × ℕ)}

/-- The **elementary automorphism** adding `c` times the `b`-th coordinate to the `a`-th: the
linear transvection out of which the source composes its normal-form reductions
([Pagano 2022, Prop. 3.33, p.431][Pagano2022]). -/
def elementaryAut (a b : ↥D) (hab : a ≠ b) (c : R) : (↥D → R) ≃ₗ[R] (↥D → R) where
  toFun x := fun h => x h + if h = a then c * x b else 0
  invFun x := fun h => x h - if h = a then c * x b else 0
  map_add' x y := by
    funext h
    by_cases hh : h = a
    · simp [hh]
      ring
    · simp [hh]
  map_smul' r x := by
    funext h
    by_cases hh : h = a
    · simp [hh]
      ring
    · simp [hh]
  left_inv x := by
    funext h
    have hb : b ≠ a := fun hba => hab hba.symm
    by_cases hh : h = a
    · simp [hh, hb]
    · simp [hh]
  right_inv x := by
    funext h
    have hb : b ≠ a := fun hba => hab hba.symm
    by_cases hh : h = a
    · simp [hh, hb]
    · simp [hh]

omit [IsDomain R] [IsDiscreteValuationRing R] in
theorem elementaryAut_apply (a b : ↥D) (hab : a ≠ b) (c : R) (x : ↥D → R) (h : ↥D) :
    elementaryAut a b hab c x h = x h + if h = a then c * x b else 0 :=
  rfl

/-- The filteredness criterion for an elementary automorphism: it lies in `Aut_filt` of the
free model as soon as multiplication by `c` raises the standard weight of the source level to
that of the target level ([Pagano 2022, Prop. 3.33, p.431][Pagano2022]). -/
theorem elementaryAut_mem_filtAut {ρ : Shift} {a b : ↥D} (hab : a ≠ b) {c : R}
    (hc : ∀ y : R, standardWeight ρ b.1.1 y ≤ standardWeight (R := R) ρ a.1.1 (c * y)) :
    elementaryAut a b hab c ∈ (freeFiltered (R := R) ρ D).filtAut := by
  have key : ∀ (c' : R), (∀ y : R, standardWeight ρ b.1.1 y
      ≤ standardWeight (R := R) ρ a.1.1 (c' * y)) →
      IsFilteredHom (freeFiltered (R := R) ρ D) (freeFiltered ρ D)
        ((elementaryAut a b hab c' : (↥D → R) ≃ₗ[R] (↥D → R)) : (↥D → R) →ₗ[R] (↥D → R)) := by
    intro c' hc' i x hx
    rw [mem_freeFiltered_filt] at hx ⊢
    intro h
    rw [show ((elementaryAut a b hab c' : (↥D → R) ≃ₗ[R] (↥D → R)) :
        (↥D → R) →ₗ[R] (↥D → R)) x h = x h + if h = a then c' * x b else 0 from rfl]
    split_ifs with hh
    · subst hh
      have h1 : (i : WithTop ℕ+) ≤ (standardFiltered (R := R) ρ h.1.1).weight (x h) := by
        rw [weight_standardFiltered]
        exact hx h
      have h2 : (i : WithTop ℕ+) ≤ (standardFiltered (R := R) ρ h.1.1).weight (c' * x b) := by
        rw [weight_standardFiltered]
        exact le_trans (hx b) (hc' (x b))
      have h3 := (standardFiltered (R := R) ρ h.1.1).min_weight_le_add (x h) (c' * x b)
      rw [← weight_standardFiltered]
      exact le_trans (le_min h1 h2) h3
    · rw [add_zero]
      exact hx h
  refine FilteredModule.mem_filtAut_of_isFilteredHom (key c hc) ?_
  have hsymm : ((elementaryAut a b hab c).symm : (↥D → R) →ₗ[R] (↥D → R))
      = ((elementaryAut a b hab (-c) : (↥D → R) ≃ₗ[R] (↥D → R)) : (↥D → R) →ₗ[R] (↥D → R)) := by
    refine LinearMap.ext fun x => ?_
    funext h
    change x h - (if h = a then c * x b else 0) = x h + if h = a then -c * x b else 0
    split_ifs with hh
    · ring
    · ring
  rw [hsymm]
  refine key (-c) fun y => ?_
  have h1 : -c * y = -(c * y) := by ring
  have hneg : standardWeight (R := R) ρ a.1.1 (-(c * y)) = standardWeight ρ a.1.1 (c * y) := by
    rcases eq_or_ne (c * y) 0 with h0 | h0
    · rw [h0, neg_zero]
    · simp only [standardWeight, if_neg (neg_ne_zero.mpr h0), if_neg h0, (addVal R).map_neg]
  rw [h1, hneg]
  exact hc y

/-- The weight criterion holds for the multiplier `π^d` as soon as the target level reaches the
source level within `d` steps of the shift—the inequality the jump order supplies in the
source's reduction ([Pagano 2022, Prop. 3.33, p.431][Pagano2022]). -/
theorem standardWeight_pi_pow_mul_le {ρ : Shift} {π : R} (hπ : Irreducible π) {i j : ℕ+}
    {d : ℕ} (h : j ≤ (⇑ρ)^[d] i) (y : R) :
    standardWeight ρ j y ≤ standardWeight (R := R) ρ i (π ^ d * y) := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [mul_zero]
    have h1 : standardWeight (R := R) ρ j (0 : R) = ⊤ := by simp [standardWeight]
    have h2 : standardWeight (R := R) ρ i (0 : R) = ⊤ := by simp [standardWeight]
    rw [h1, h2]
  have hπy : π ^ d * y ≠ 0 := mul_ne_zero (pow_ne_zero d hπ.ne_zero) hy
  rw [standardWeight, standardWeight, if_neg hy, if_neg hπy, WithTop.coe_le_coe]
  have hval : (addVal R (π ^ d * y)).toNat = d + (addVal R y).toNat := by
    rw [addVal_mul, (addVal R).map_pow, addVal_uniformizer hπ, nsmul_eq_mul, mul_one,
      ENat.toNat_add (by simp) fun ht => hy (addVal_eq_top_iff.mp ht)]
    simp
  rw [hval, add_comm d, Function.iterate_add_apply]
  exact (ρ.strict_mono.iterate _).monotone h

/-- Every vector of `π M_ρ^f` is conjugate, under the filtered automorphism group, to the
jump-set vector of the `≤_ρ`-minimal points of its coordinate graph. Claim recorded ahead of
its proof, which composes finitely many elementary automorphisms
([Pagano 2022, Prop. 3.33, p.431][Pagano2022]). -/
theorem exists_filtAut_eq_jumpSetVector {ρ : Shift} (hρ : (Shift.T ρ).Finite) (f : ℕ+) {π : R}
    (hπ : Irreducible π) {v : ↥(Shift.freeIndex hρ f) → R}
    (hv : v ∈ Ideal.span {π} • (⊤ : Submodule R (↥(Shift.freeIndex hρ f) → R))) :
    ∃ e ∈ (freeFiltered (R := R) ρ (Shift.freeIndex hρ f)).filtAut,
      e v = jumpSetVector π (Shift.freeIndex hρ f) (jumpMin ρ (coordGraph v)) := by
  sorry

/-- The extended version of the normal-form theorem, over the presenting module
`M_ρ^{f - 1} ⊕ M_ρ^*`. Claim recorded ahead of its proof
([Pagano 2022, Prop. 3.33, p.431][Pagano2022]). -/
theorem exists_filtAut_eq_jumpSetVector_star {ρ : Shift} (hρ : (Shift.T ρ).Finite) (f : ℕ+)
    {π : R} (hπ : Irreducible π) {v : ↥(Shift.starIndex hρ f) → R}
    (hv : v ∈ Ideal.span {π} • (⊤ : Submodule R (↥(Shift.starIndex hρ f) → R))) :
    ∃ e ∈ (freeFiltered (R := R) ρ (Shift.starIndex hρ f)).filtAut,
      e v = jumpSetVector π (Shift.starIndex hρ f) (jumpMin ρ (coordGraph v)) := by
  sorry

end Atlas.Knowledge
