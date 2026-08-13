import Mathlib
import Atlas.Knowledge.ShiftEStar
import Atlas.Knowledge.ShiftRhoEP

/-!
# T of rho-e-p

What `Atlas.Knowledge.ShiftT` and `Atlas.Knowledge.ShiftEStar` come to for the shift
`Atlas.Knowledge.ShiftRhoEP`: `T (ρ_ep e p hp)` has exactly `e` elements—so in particular it is
finite, which is what makes `e_star` available at all—and `e_star` of it is
`⌈(p * e / (p - 1) : ℚ)⌉₊`.

Both rest on the characterization `mem_T_ρ_ep`: writing `m` for the floor division
`(e : ℕ) / ((p : ℕ) - 1)`, the set `T (ρ_ep e p hp)` consists of the `n ≤ m + e` with
`¬ (p : ℕ) ∣ n`, because `ρ_ep e p hp` sends `i ≤ m` to `p * i` and `i > m` to `i + e`.

## Main statements

* `T_ρ_ep_ncard_eq_e` — `T (ρ_ep e p hp)` has exactly `e` elements.
* `T_ρ_ep_finite` — hence it is finite.
* `e_star_ρ_ep_eq` — `e_star` of it is `⌈(p * e / (p - 1) : ℚ)⌉₊`.

## Implementation notes

The helper lemmas carry `m` as an abstract variable constrained by `(p - 1) * m ≤ e` and
`e < (p - 1) * (m + 1)` rather than as the floor division itself, which keeps their arithmetic
within `omega`'s reach.

The `e_star` computation splits on whether `p - 1` divides `e`, because that decides where the
maximum of `T (ρ_ep e p hp)` sits: when it divides, `m + e` is itself `p * m` and so is missing
from the set, and the maximum is one below; when it does not, `m + e` is the maximum.

The last of the three is named `e_star_ρ_ep_eq` rather than `e_star_eq`, which is what it was
called where this came from: in a library that will hold the `e_star` of more than one shift, a
name that does not say which shift is a name that will have to be changed later.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open Set
open Shift

/-- `p * i = i + (p - 1) * i` in `ℕ`, the expansion every counting argument below runs on. -/
private lemma succ_pred_mul {p : ℕ} (hp : 1 < p) (i : ℕ) : p * i = i + (p - 1) * i := by
  have h1 := Nat.sub_mul p 1 i
  have h2 : 1 * i = i := one_mul i
  have h3 : i ≤ p * i := Nat.le_mul_of_pos_left i (by omega)
  omega

private lemma ρ_ep_apply_of_le {e p : ℕ+} (hp : 1 < p) {i : ℕ+}
    (h : ((p : ℕ) - 1) * (i : ℕ) ≤ (e : ℕ)) : ρ_ep e p hp i = p * i := by
  have hp' : 1 < (p : ℕ) := by exact_mod_cast hp
  change min (p * i) (i + e) = p * i
  apply min_eq_left
  rw [← PNat.coe_le_coe]
  push_cast
  have h3 := succ_pred_mul hp' (i : ℕ)
  omega

private lemma ρ_ep_apply_of_gt {e p : ℕ+} (hp : 1 < p) {i : ℕ+}
    (h : (e : ℕ) < ((p : ℕ) - 1) * (i : ℕ)) : ρ_ep e p hp i = i + e := by
  have hp' : 1 < (p : ℕ) := by exact_mod_cast hp
  change min (p * i) (i + e) = i + e
  apply min_eq_right
  rw [← PNat.coe_le_coe]
  push_cast
  have h3 := succ_pred_mul hp' (i : ℕ)
  omega

/-- For any `m` with `(p - 1) * m ≤ e` and `e < (p - 1) * (m + 1)`—that is, for `m` the floor
division `(e : ℕ) / ((p : ℕ) - 1)`—the set `T (ρ_ep e p hp)` consists of the `n ≤ m + e` not
divisible by `p` ([Pagano 2022, Example 2.1, p.415][Pagano2022]). -/
private lemma mem_T_ρ_ep {e p : ℕ+} (hp : 1 < p) {m : ℕ}
    (hle : ((p : ℕ) - 1) * m ≤ (e : ℕ)) (hlt : (e : ℕ) < ((p : ℕ) - 1) * (m + 1)) (n : ℕ+) :
    n ∈ T (ρ_ep e p hp) ↔ (n : ℕ) ≤ m + (e : ℕ) ∧ ¬ (p : ℕ) ∣ (n : ℕ) := by
  have hp' : 1 < (p : ℕ) := by exact_mod_cast hp
  simp only [mem_sdiff, mem_univ, image_univ, mem_range, true_and, not_exists]
  constructor
  · intro hn
    have hub : (n : ℕ) ≤ m + (e : ℕ) := by
      by_contra hgt
      have hstep : ((p : ℕ) - 1) * (m + 1) ≤ ((p : ℕ) - 1) * ((n : ℕ) - (e : ℕ)) :=
        Nat.mul_le_mul_left _ (by omega)
      have hkey : (e : ℕ) < ((p : ℕ) - 1) * ((n : ℕ) - (e : ℕ)) := by omega
      refine hn ⟨(n : ℕ) - (e : ℕ), by omega⟩
        ((ρ_ep_apply_of_gt hp (i := ⟨(n : ℕ) - (e : ℕ), by omega⟩) hkey).trans ?_)
      rw [← PNat.coe_inj, PNat.add_coe, PNat.mk_coe]
      omega
    refine ⟨hub, ?_⟩
    rintro ⟨k, hk⟩
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with rfl | hk0
      · have := n.pos
        omega
      · exact hk0
    rcases Nat.lt_or_ge (e : ℕ) (((p : ℕ) - 1) * k) with hgtk | hlek
    · have hkm : m + 1 ≤ k := by
        by_contra h'
        have h1 : ((p : ℕ) - 1) * k ≤ ((p : ℕ) - 1) * m := Nat.mul_le_mul_left _ (by omega)
        omega
      have h2 := succ_pred_mul hp' k
      omega
    · refine hn ⟨k, hk0⟩ ((ρ_ep_apply_of_le hp (i := ⟨k, hk0⟩) hlek).trans ?_)
      rw [← PNat.coe_inj, PNat.mul_coe, PNat.mk_coe]
      omega
  · rintro ⟨hub, hnd⟩ i hi
    rcases Nat.lt_or_ge (e : ℕ) (((p : ℕ) - 1) * (i : ℕ)) with hgt | hle'
    · have hie := (ρ_ep_apply_of_gt hp hgt).symm.trans hi
      have hie' : (i : ℕ) + (e : ℕ) = (n : ℕ) := by exact_mod_cast hie
      have hkm : m + 1 ≤ (i : ℕ) := by
        by_contra h'
        have h1 : ((p : ℕ) - 1) * (i : ℕ) ≤ ((p : ℕ) - 1) * m := Nat.mul_le_mul_left _ (by omega)
        omega
      omega
    · refine hnd ⟨(i : ℕ), ?_⟩
      have hpi := (ρ_ep_apply_of_le hp hle').symm.trans hi
      exact_mod_cast hpi.symm

/-- `T (ρ_ep e p hp)` has exactly `e` elements
([Pagano 2022, Example 2.1, p.415][Pagano2022]). -/
theorem T_ρ_ep_ncard_eq_e (e : ℕ+) (p : ℕ+) (hp : 1 < p) : (T (ρ_ep e p hp)).ncard = e := by
  have hp' : 1 < (p : ℕ) := by exact_mod_cast hp
  obtain ⟨m, hle, hlt⟩ :
      ∃ m : ℕ, ((p : ℕ) - 1) * m ≤ (e : ℕ) ∧ (e : ℕ) < ((p : ℕ) - 1) * (m + 1) := by
    refine ⟨(e : ℕ) / ((p : ℕ) - 1), Nat.mul_div_le _ _, ?_⟩
    rw [Nat.mul_comm]
    exact (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)
  have himg : PNat.val '' T (ρ_ep e p hp) =
      ↑((Finset.Ioc 0 (m + (e : ℕ))).filter fun k => ¬ (p : ℕ) ∣ k) := by
    ext k
    simp only [Set.mem_image, Finset.mem_coe, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨h1, h2⟩ := (mem_T_ρ_ep hp hle hlt x).mp hx
      exact ⟨⟨x.pos, h1⟩, h2⟩
    · rintro ⟨⟨hk0, hk1⟩, hk2⟩
      exact ⟨⟨k, hk0⟩, (mem_T_ρ_ep hp hle hlt _).mpr ⟨hk1, hk2⟩, rfl⟩
  have hinj := Set.ncard_image_of_injective (T (ρ_ep e p hp)) PNat.coe_injective
  rw [← hinj, himg, Set.ncard_coe_finset, Finset.filter_not, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.filter_subset _ _), Nat.card_Ioc,
    Nat.Ioc_filter_dvd_card_eq_div]
  have hdiv : (m + (e : ℕ)) / (p : ℕ) = m := by
    apply Nat.div_eq_of_lt_le
    · have hc := Nat.mul_comm m (p : ℕ)
      have hx := succ_pred_mul hp' m
      omega
    · have hc := Nat.mul_comm (m + 1) (p : ℕ)
      have hx := succ_pred_mul hp' (m + 1)
      omega
  rw [hdiv]
  omega

/-- `T (ρ_ep e p hp)` is finite, having `e` elements
([Pagano 2022, Example 2.1, p.415][Pagano2022]). -/
theorem T_ρ_ep_finite (e : ℕ+) (p : ℕ+) (hp : 1 < p) : (T (ρ_ep e p hp)).Finite := by
  apply finite_of_ncard_ne_zero
  rw [T_ρ_ep_ncard_eq_e]
  exact PNat.ne_zero e

/-- `e_star` of `ρ_ep e p hp` is `⌈(p * e / (p - 1) : ℚ)⌉₊`
([Pagano 2022, Example 2.1, p.415][Pagano2022]). -/
theorem e_star_ρ_ep_eq (e : ℕ+) (p : ℕ+) (hp : 1 < p) :
    e_star (ρ_ep e p hp) (by exact T_ρ_ep_finite e p hp)
    = Nat.ceil (p * e / (p - 1) : ℚ) := by
  have hp' : 1 < (p : ℕ) := by exact_mod_cast hp
  have he : 0 < (e : ℕ) := e.pos
  obtain ⟨m, hle, hlt⟩ :
      ∃ m : ℕ, ((p : ℕ) - 1) * m ≤ (e : ℕ) ∧ (e : ℕ) < ((p : ℕ) - 1) * (m + 1) := by
    refine ⟨(e : ℕ) / ((p : ℕ) - 1), Nat.mul_div_le _ _, ?_⟩
    rw [Nat.mul_comm]
    exact (Nat.div_lt_iff_lt_mul (by omega)).mp (by omega)
  have hden : (0 : ℚ) < ((p : ℕ) : ℚ) - 1 := by
    rw [sub_pos]
    exact_mod_cast hp'
  have hpc : (((p : ℕ) - 1 : ℕ) : ℚ) = ((p : ℕ) : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have hsp := succ_pred_mul hp' (e : ℕ)
  by_cases hdvd : ((p : ℕ) - 1) ∣ (e : ℕ)
  · -- `p - 1` divides `e`, so `m + e` itself is `p * m`, and the maximum of `T (ρ_ep e p hp)`
    -- sits one below it
    obtain ⟨c, hc⟩ := hdvd
    have hm_eq : m = c := by
      have h1 : m ≤ c := Nat.le_of_mul_le_mul_left (by omega) (show 0 < (p : ℕ) - 1 by omega)
      have h2 : c < m + 1 := Nat.lt_of_mul_lt_mul_left (a := (p : ℕ) - 1) (by omega)
      omega
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with rfl | hc0
      · rw [Nat.mul_zero] at hc
        omega
      · exact hc0
    have hexp := succ_pred_mul hp' c
    have hmax : ∀ hne,
        (Set.Finite.toFinset (T_ρ_ep_finite e p hp)).max' hne
          = (⟨m + (e : ℕ) - 1, by omega⟩ : ℕ+) := by
      intro hne
      apply le_antisymm
      · apply Finset.max'_le
        intro y hy
        rw [Set.Finite.mem_toFinset] at hy
        obtain ⟨hy1, hy2⟩ := (mem_T_ρ_ep hp hle hlt y).mp hy
        rw [← PNat.coe_le_coe, PNat.mk_coe]
        rcases Nat.lt_or_ge (y : ℕ) (m + (e : ℕ)) with hylt | hyge
        · omega
        · exact absurd ⟨c, by omega⟩ hy2
      · apply Finset.le_max'
        rw [Set.Finite.mem_toFinset]
        refine (mem_T_ρ_ep hp hle hlt _).mpr ⟨?_, ?_⟩
        · rw [PNat.mk_coe]
          omega
        · rw [PNat.mk_coe]
          rintro ⟨d, hd⟩
          have hdc : d < c := by
            by_contra hcd
            have h1 := Nat.mul_le_mul_left (p : ℕ) (show c ≤ d by omega)
            omega
          have h2 := Nat.mul_le_mul_left (p : ℕ) (show d + 1 ≤ c by omega)
          have h3 : (p : ℕ) * (d + 1) = (p : ℕ) * d + (p : ℕ) := by ring
          omega
    simp only [e_star, hmax]
    push_cast [PNat.mk_coe]
    symm
    rw [Nat.ceil_eq_iff (by omega)]
    have hs := Nat.sub_mul (m + (e : ℕ)) 1 ((p : ℕ) - 1)
    have h1m : 1 * ((p : ℕ) - 1) = (p : ℕ) - 1 := one_mul _
    have hexpand : (m + (e : ℕ)) * ((p : ℕ) - 1)
        = ((p : ℕ) - 1) * m + ((p : ℕ) - 1) * (e : ℕ) := by ring
    have hEc : ((p : ℕ) - 1) * m = (e : ℕ) := by rw [hm_eq, ← hc]
    have hb : (m + (e : ℕ) - 1 + 1) * ((p : ℕ) - 1) = (m + (e : ℕ)) * ((p : ℕ) - 1) := by
      congr 1
      omega
    constructor
    · simp only [Nat.add_sub_cancel]
      rw [lt_div_iff₀ hden, ← hpc]
      exact_mod_cast (show (m + (e : ℕ) - 1) * ((p : ℕ) - 1) < (p : ℕ) * (e : ℕ) by omega)
    · rw [div_le_iff₀ hden, ← hpc]
      exact_mod_cast (show (p : ℕ) * (e : ℕ) ≤ (m + (e : ℕ) - 1 + 1) * ((p : ℕ) - 1) by omega)
  · -- `p - 1` does not divide `e`: the maximum of `T (ρ_ep e p hp)` is `m + e` itself
    have hstrict : ((p : ℕ) - 1) * m < (e : ℕ) := by
      rcases Nat.lt_or_ge (((p : ℕ) - 1) * m) (e : ℕ) with h | h
      · exact h
      · exact absurd ⟨m, by omega⟩ hdvd
    have hmax : ∀ hne,
        (Set.Finite.toFinset (T_ρ_ep_finite e p hp)).max' hne
          = (⟨m + (e : ℕ), by omega⟩ : ℕ+) := by
      intro hne
      apply le_antisymm
      · apply Finset.max'_le
        intro y hy
        rw [Set.Finite.mem_toFinset] at hy
        obtain ⟨hy1, hy2⟩ := (mem_T_ρ_ep hp hle hlt y).mp hy
        rw [← PNat.coe_le_coe, PNat.mk_coe]
        exact hy1
      · apply Finset.le_max'
        rw [Set.Finite.mem_toFinset]
        refine (mem_T_ρ_ep hp hle hlt _).mpr ⟨?_, ?_⟩
        · rw [PNat.mk_coe]
        · rw [PNat.mk_coe]
          rintro ⟨d, hd⟩
          rcases Nat.lt_or_ge m d with hdm | hdm
          · have h1 : ((p : ℕ) - 1) * (m + 1) ≤ ((p : ℕ) - 1) * d :=
              Nat.mul_le_mul_left _ (by omega)
            have h2 := succ_pred_mul hp' d
            omega
          · have h1 : ((p : ℕ) - 1) * d ≤ ((p : ℕ) - 1) * m := Nat.mul_le_mul_left _ (by omega)
            have h2 := succ_pred_mul hp' d
            omega
    simp only [e_star, hmax]
    push_cast [PNat.mk_coe]
    symm
    rw [Nat.ceil_eq_iff (by omega)]
    have hexpand : (m + (e : ℕ)) * ((p : ℕ) - 1)
        = ((p : ℕ) - 1) * m + ((p : ℕ) - 1) * (e : ℕ) := by ring
    have hexpand2 : (m + (e : ℕ) + 1) * ((p : ℕ) - 1)
        = ((p : ℕ) - 1) * (m + 1) + ((p : ℕ) - 1) * (e : ℕ) := by ring
    constructor
    · simp only [Nat.add_sub_cancel]
      rw [lt_div_iff₀ hden, ← hpc]
      exact_mod_cast (show (m + (e : ℕ)) * ((p : ℕ) - 1) < (p : ℕ) * (e : ℕ) by omega)
    · rw [div_le_iff₀ hden, ← hpc]
      exact_mod_cast (show (p : ℕ) * (e : ℕ) ≤ (m + (e : ℕ) + 1) * ((p : ℕ) - 1) by omega)

end Atlas.Knowledge
