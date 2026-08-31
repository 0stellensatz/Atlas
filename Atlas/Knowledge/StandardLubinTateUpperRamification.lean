import Mathlib
import Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.StandardLubinTateHerbrand
import Atlas.Knowledge.StandardLubinTateLevelField
import Atlas.Knowledge.StandardLubinTateLowerRamification
import Atlas.Knowledge.UpperRamificationGroup

/-!
# standard Lubin–Tate upper ramification

The upper ramification filtration of the level tower, in the knowledge layer's own
Phase 1 vocabulary: on the range visible at level `n + 1`, the real upper filtration of
`Atlas.Knowledge.upperRamificationGroup` is the natural-ceiling extension of its integer
values — the upper jumps of a level field are integers, the tower's instance of
Hasse–Arf — and the group at an integer `k ∈ [1, n+1]` has order `q^{n+1−k}`. Both are
the Herbrand computation of the tower's break structure, Serre's `ω(Uⁿ) = Gⁿ` read on
the concrete levels: the inverse Herbrand values of
`Atlas.Knowledge.standardLubinTateHerbrandPsi_natCast` trap the real index inside one
power interval, where the lower filtration of
`Atlas.Knowledge.standardLubinTateLowerRamification_eq` is constant.

## Main statements

* `standardLubinTateUpperRamification` — the natural-ceiling constancy on the visible
  range; proved.
* `standardLubinTateUpperRamification_natCard` — order `q^{n+1−k}` at integer `k`;
  proved.

## Implementation notes

The source packages per-level lower filtrations, Herbrand functions, and real upper
groups of its own (`LubinTate/FiniteLevel/UpperRamification.lean:38, :50, :73`); Atlas
does not clone them — the statement policy forbids duplicating what Phase 1's layer
already provides, so both computations are stated directly against
`Atlas.Knowledge.upperRamificationGroup` at the level field, and the proofs run
through the layer's own filtration items rather than the source's packaged
definitions. The exponent
convention matches the source's `standardLubinTateRealUpperRamificationGroup_natCard`
(`LubinTate/FiniteLevel/HerbrandFormula.lean:284`): at `k = n + 1` the group is trivial,
at `k = 1` it is the full wild part of order `qⁿ`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Serre1979] J.-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**,
  Springer New York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- On the range visible at level `n + 1`, the **upper filtration is the natural-ceiling
extension of its integer values** — the level tower's upper jumps are integers
([Serre 1979, Chap. XV, §2, Thm. 2 and Rem., p.228][Serre1979];
[Milne 2020, Chap. I, §4, p.47][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/HerbrandFormula.lean:315`,
`standardLubinTateRealUpperRamificationGroup_eq_natCeil`][Yamaguchi2026]). -/
theorem standardLubinTateUpperRamification {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ)
    (t : ℝ) (h1 : 1 ≤ ⌈t⌉₊) (hn : ⌈t⌉₊ ≤ n + 1) :
    upperRamificationGroup K (standardLubinTateLevelField K hπ n) t =
      upperRamificationGroup K (standardLubinTateLevelField K hπ n) (⌈t⌉₊ : ℝ) := by
  obtain ⟨vL, tL, hVE, _, hMCL⟩ :=
    exists_extension_isMixedCharLocalField K ↥(standardLubinTateLevelField K hπ n)
  letI := vL
  letI := tL
  haveI := hVE
  haveI := hMCL
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  set k := ⌈t⌉₊ with hkdef
  have hk1 : 1 ≤ k := h1
  have hpk1 : (1 : ℕ) ≤ Nat.card 𝓀[K] ^ (k - 1) := Nat.one_le_pow _ _ (by omega)
  have hpkk : Nat.card 𝓀[K] ^ (k - 1) ≤ Nat.card 𝓀[K] ^ k - 1 := by
    have hstep : Nat.card 𝓀[K] ^ (k - 1) * 2 ≤ Nat.card 𝓀[K] ^ k := by
      calc Nat.card 𝓀[K] ^ (k - 1) * 2 ≤
          Nat.card 𝓀[K] ^ (k - 1) * Nat.card 𝓀[K] :=
            Nat.mul_le_mul_left _ (by omega)
        _ = Nat.card 𝓀[K] ^ k := by
            rw [← pow_succ, show k - 1 + 1 = k by omega]
    omega
  have ht_le : t ≤ (k : ℝ) := Nat.le_ceil t
  have ht_gt : ((k - 1 : ℕ) : ℝ) < t := by
    have := Nat.lt_ceil (n := k - 1) (a := t) |>.mp (by omega)
    exact_mod_cast this
  have hψt_le : herbrandPsi K ↥(standardLubinTateLevelField K hπ n) t ≤
      ((Nat.card 𝓀[K] ^ k - 1 : ℕ) : ℝ) := by
    rw [← standardLubinTateHerbrandPsi_natCast K hπ n (by omega : k ≤ n + 1)]
    exact (herbrandPsi_strictMono K
      ↥(standardLubinTateLevelField K hπ n)).monotone ht_le
  have hψt_gt : ((Nat.card 𝓀[K] ^ (k - 1) - 1 : ℕ) : ℝ) <
      herbrandPsi K ↥(standardLubinTateLevelField K hπ n) t := by
    rw [← standardLubinTateHerbrandPsi_natCast K hπ n (by omega : k - 1 ≤ n + 1)]
    exact herbrandPsi_strictMono K
      ↥(standardLubinTateLevelField K hπ n) ht_gt
  have hceil_le : ⌈herbrandPsi K ↥(standardLubinTateLevelField K hπ n) t⌉ ≤
      ((Nat.card 𝓀[K] ^ k - 1 : ℕ) : ℤ) :=
    Int.ceil_le.mpr (by exact_mod_cast hψt_le)
  have hceil_gt : ((Nat.card 𝓀[K] ^ (k - 1) - 1 : ℕ) : ℤ) <
      ⌈herbrandPsi K ↥(standardLubinTateLevelField K hπ n) t⌉ :=
    Int.lt_ceil.mpr (by exact_mod_cast hψt_gt)
  rw [upperRamificationGroup, upperRamificationGroup, realLowerRamificationGroup,
    realLowerRamificationGroup,
    standardLubinTateHerbrandPsi_natCast K hπ n (by omega : k ≤ n + 1),
    Int.ceil_natCast]
  set m := ⌈herbrandPsi K ↥(standardLubinTateLevelField K hπ n) t⌉ with hmdef
  have hm0 : 0 ≤ m := by omega
  have hml : Nat.card 𝓀[K] ^ (k - 1) ≤ m.toNat := by omega
  have hmr : m.toNat < Nat.card 𝓀[K] ^ k := by omega
  rw [show m = ((m.toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg hm0).symm,
    standardLubinTateLowerRamification_eq K hπ n hk1 (by omega : k ≤ n + 1)
      hml hmr,
    standardLubinTateLowerRamification_eq K hπ n hk1 (by omega : k ≤ n + 1)
      hpkk (by omega : Nat.card 𝓀[K] ^ k - 1 < Nat.card 𝓀[K] ^ k)]

/-- At an integer `k ∈ [1, n+1]`, the upper group of the level field has order
`q^{n+1−k}`
([Serre 1979, Chap. XV, §2, Thm. 2, p.228][Serre1979];
[Yamaguchi 2026, `LubinTate/FiniteLevel/HerbrandFormula.lean:284`,
`standardLubinTateRealUpperRamificationGroup_natCard`][Yamaguchi2026]). -/
theorem standardLubinTateUpperRamification_natCard {π : 𝒪[K]} (hπ : Irreducible π)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    Nat.card (upperRamificationGroup K (standardLubinTateLevelField K hπ n)
        (k : ℝ)) =
      Nat.card (IsLocalRing.ResidueField 𝒪[K]) ^ (n + 1 - k) := by
  obtain ⟨vL, tL, hVE, _, hMCL⟩ :=
    exists_extension_isMixedCharLocalField K ↥(standardLubinTateLevelField K hπ n)
  letI := vL
  letI := tL
  haveI := hVE
  haveI := hMCL
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hpkk : Nat.card 𝓀[K] ^ (k - 1) ≤ Nat.card 𝓀[K] ^ k - 1 := by
    have hstep : Nat.card 𝓀[K] ^ (k - 1) * 2 ≤ Nat.card 𝓀[K] ^ k := by
      calc Nat.card 𝓀[K] ^ (k - 1) * 2 ≤
          Nat.card 𝓀[K] ^ (k - 1) * Nat.card 𝓀[K] :=
            Nat.mul_le_mul_left _ (by omega)
        _ = Nat.card 𝓀[K] ^ k := by
            rw [← pow_succ, show k - 1 + 1 = k by omega]
    omega
  have hp1 : 1 ≤ Nat.card 𝓀[K] ^ k := Nat.one_le_pow _ _ (by omega)
  rw [show ((k : ℕ) : ℝ) = ((⌈((k : ℕ) : ℝ)⌉₊ : ℕ) : ℝ) by rw [Nat.ceil_natCast]]
  rw [upperRamificationGroup, realLowerRamificationGroup, Nat.ceil_natCast,
    standardLubinTateHerbrandPsi_natCast K hπ n hkn, Int.ceil_natCast]
  exact standardLubinTateLowerRamification_natCard K hπ n hk hkn hpkk
    (by omega : Nat.card 𝓀[K] ^ k - 1 < Nat.card 𝓀[K] ^ k)

end Atlas.Knowledge
