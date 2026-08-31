import Mathlib
import Atlas.Knowledge.HerbrandPhi
import Atlas.Knowledge.HerbrandPsi
import Atlas.Knowledge.StandardLubinTateLowerRamification

/-!
# standard Lubin–Tate Herbrand values

The Herbrand function of a level field at the lower breaks: `φ(qᵏ − 1) = k` and,
inverted, `ψ(k) = qᵏ − 1` for `k ≤ n + 1`. Each unit of upper index consumes exactly
one power interval of the lower filtration — over `[qᵏ, q^(k+1))` the group has
constant order `q^(n−k)`, so the interval's `(q−1)qᵏ` summands contribute one full
`|G_0| = (q−1)qⁿ` to the partial sums of `Atlas.Knowledge.herbrandPhi_natCast`. These
are the two identities the upper-numbering description of the level tower reads off:
the upper jumps are the integers `1, …, n + 1`.

## Main statements

* `standardLubinTateHerbrandPhi_pow_sub_one` — `φ(qᵏ − 1) = k`; proved.
* `standardLubinTateHerbrandPsi_natCast` — `ψ(k) = qᵏ − 1`; proved.

## Implementation notes

The sum identity is an induction over the power intervals, each step a constant sum by
`Atlas.Knowledge.standardLubinTateLowerRamification_natCard` with the base
`Atlas.Knowledge.standardLubinTateLowerRamification_zero_natCard`; the `φ` value then
falls out of `Atlas.Knowledge.herbrandPhi_natCast` by one division, and `ψ` is the
inverse law `Atlas.Knowledge.herbrandPsi_herbrandPhi` applied to the `φ` value. The
statements are phrased at the hypothesized local-field structure on the level field —
consumers obtain it from `Atlas.Knowledge.exists_extension_isMixedCharLocalField` — as
in `Atlas.Knowledge.StandardLubinTateLowerRamification`.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer
  New York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section Herbrand

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable {π : ↥𝒪[K]} (hπ : Irreducible π) (n : ℕ)
variable [ValuativeRel ↥(standardLubinTateLevelField K hπ n)]
  [TopologicalSpace ↥(standardLubinTateLevelField K hπ n)]
  [ValuativeExtension K ↥(standardLubinTateLevelField K hπ n)]
  [IsMixedCharLocalField ↥(standardLubinTateLevelField K hπ n)]

/- The partial sums of the filtration cards: each power interval contributes one full
`|G_0|`. -/
private theorem sum_card_lowerRamificationGroup {k : ℕ} (hk : k ≤ n + 1) :
    (∑ i ∈ Finset.range (Nat.card 𝓀[K] ^ k),
      (Nat.card (lowerRamificationGroup K
        ↥(standardLubinTateLevelField K hπ n) (i : ℤ)) : ℝ)) =
      (k + 1) * ((Nat.card 𝓀[K] - 1 : ℕ) * Nat.card 𝓀[K] ^ n : ℕ) := by
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  induction k with
  | zero =>
    rw [pow_zero, Finset.sum_range_one]
    rw [show ((0 : ℕ) : ℤ) = (0 : ℤ) by norm_num,
      standardLubinTateLowerRamification_zero_natCard K hπ n]
    push_cast
    ring
  | succ k ih =>
    have hk' : k ≤ n + 1 := by omega
    have hle : Nat.card 𝓀[K] ^ k ≤ Nat.card 𝓀[K] ^ (k + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [← Finset.sum_range_add_sum_Ico _ hle, ih hk']
    have hconst : ∀ i ∈ Finset.Ico (Nat.card 𝓀[K] ^ k) (Nat.card 𝓀[K] ^ (k + 1)),
        (Nat.card (lowerRamificationGroup K
          ↥(standardLubinTateLevelField K hπ n) (i : ℤ)) : ℝ) =
        (Nat.card 𝓀[K] ^ (n + 1 - (k + 1)) : ℕ) := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      rw [standardLubinTateLowerRamification_natCard K hπ n
        (k := k + 1) (by omega) (by omega) (by simpa using hi.1) hi.2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Nat.card_Ico,
      nsmul_eq_mul]
    have hexp : n + 1 - (k + 1) = n - k := by omega
    have harith : ((Nat.card 𝓀[K] ^ (k + 1) - Nat.card 𝓀[K] ^ k : ℕ) : ℝ) *
        ((Nat.card 𝓀[K] ^ (n + 1 - (k + 1)) : ℕ) : ℝ) =
        (((Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n : ℕ) : ℝ) := by
      rw [hexp, Nat.cast_sub hle, Nat.cast_mul,
        Nat.cast_sub (by omega : 1 ≤ Nat.card 𝓀[K])]
      push_cast
      rw [pow_succ, show ((Nat.card 𝓀[K] : ℝ) ^ k * Nat.card 𝓀[K] -
          (Nat.card 𝓀[K] : ℝ) ^ k) * (Nat.card 𝓀[K] : ℝ) ^ (n - k) =
          ((Nat.card 𝓀[K] : ℝ) - 1) *
            ((Nat.card 𝓀[K] : ℝ) ^ k * (Nat.card 𝓀[K] : ℝ) ^ (n - k)) by ring,
        ← pow_add, show k + (n - k) = n by omega]
    rw [harith]
    push_cast
    ring

/-- **The Herbrand function at the lower breaks**: `φ(qᵏ − 1) = k` — each unit of upper
index consumes one power interval of the lower filtration
([Serre 1979, Chap. IV, §4, pp.78–79][Serre1979] — "`φ_{L/K}(pᵏ − 1) = k`, which is
easy", the line after Prop. 18's corollary, done here for the general tower;
[Yamaguchi 2026, `LubinTate/FiniteLevel/HerbrandFormula.lean:215`][Yamaguchi2026]). -/
theorem standardLubinTateHerbrandPhi_pow_sub_one {k : ℕ} (hk : k ≤ n + 1) :
    herbrandPhi K ↥(standardLubinTateLevelField K hπ n)
      ((Nat.card 𝓀[K] ^ k - 1 : ℕ) : ℝ) = k := by
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hpow1 : 1 ≤ Nat.card 𝓀[K] ^ k := Nat.one_le_pow _ _ (by omega)
  rw [herbrandPhi_natCast, show Nat.card 𝓀[K] ^ k - 1 + 1 = Nat.card 𝓀[K] ^ k
      by omega,
    sum_card_lowerRamificationGroup K hπ n hk,
    standardLubinTateLowerRamification_zero_natCard K hπ n]
  have h0 : ((Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n : ℕ) ≠ 0 :=
    Nat.mul_ne_zero (by omega) (Nat.pow_pos (by omega : 0 < Nat.card 𝓀[K])).ne'
  have h0' : (((Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast h0
  field_simp
  ring

/-- **The inverse Herbrand function at the integers**: `ψ(k) = qᵏ − 1` — the upper
jumps of the level tower sit at the integers, over the lower breaks
([Serre 1979, Chap. IV, §4, Cor. to Prop. 18, p.79][Serre1979] — "the jumps in the
filtration `(Gᵛ)` are integers";
[Yamaguchi 2026, `LubinTate/FiniteLevel/HerbrandFormula.lean:233`][Yamaguchi2026]). -/
theorem standardLubinTateHerbrandPsi_natCast {k : ℕ} (hk : k ≤ n + 1) :
    herbrandPsi K ↥(standardLubinTateLevelField K hπ n) (k : ℝ) =
      ((Nat.card 𝓀[K] ^ k - 1 : ℕ) : ℝ) := by
  have h := standardLubinTateHerbrandPhi_pow_sub_one K hπ n hk
  rw [← h, herbrandPsi_herbrandPhi]

end Herbrand

end Atlas.Knowledge
