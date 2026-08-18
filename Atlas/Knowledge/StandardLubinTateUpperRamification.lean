import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.StandardLubinTateLevelField
import Atlas.Knowledge.UpperRamificationGroup

/-!
# standard Lubin–Tate upper ramification

The upper ramification filtration of the level tower, in the knowledge layer's own
Phase 1 vocabulary: on the range visible at level `n + 1`, the real upper filtration of
`Atlas.Knowledge.upperRamificationGroup` is the natural-ceiling extension of its integer
values — the upper jumps of a level field are integers, the tower's instance of
Hasse–Arf — and the group at an integer `k ∈ [1, n+1]` has order `q^{n+1−k}`. Both are
recorded ahead of their proofs: they are the Herbrand computation of the tower's
break structure, Serre's `ω(Uⁿ) = Gⁿ` read on the concrete levels.

## Main statements

* `standardLubinTateUpperRamification` — the natural-ceiling constancy on the visible
  range; recorded ahead of its proof.
* `standardLubinTateUpperRamification_natCard` — order `q^{n+1−k}` at integer `k`;
  recorded ahead of its proof.

## Implementation notes

The source packages per-level lower filtrations, Herbrand functions, and real upper
groups of its own (`LubinTate/FiniteLevel/UpperRamification.lean:38, :50, :73`); Atlas
does not clone them — the statement policy forbids duplicating what Phase 1's layer
already provides, so both computations are stated directly against
`Atlas.Knowledge.upperRamificationGroup` at the level field, and the source's packaged
definitions are consumed by the future proofs, not by these statements. The exponent
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
extension of its integer values** — the level tower's upper jumps are integers. Claim
recorded ahead of its proof
([Serre 1979, Chap. XV, §2, Thm. 2 and Rem., p.228][Serre1979];
[Milne 2020, Chap. I, §4, p.47][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/HerbrandFormula.lean:315`,
`standardLubinTateRealUpperRamificationGroup_eq_natCeil`][Yamaguchi2026]). -/
theorem standardLubinTateUpperRamification {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ)
    (t : ℝ) (h1 : 1 ≤ ⌈t⌉₊) (hn : ⌈t⌉₊ ≤ n + 1) :
    upperRamificationGroup K (standardLubinTateLevelField K hπ n) t =
      upperRamificationGroup K (standardLubinTateLevelField K hπ n) (⌈t⌉₊ : ℝ) := by
  sorry

/-- At an integer `k ∈ [1, n+1]`, the upper group of the level field has order
`q^{n+1−k}`. Claim recorded ahead of its proof
([Serre 1979, Chap. XV, §2, Thm. 2, p.228][Serre1979];
[Milne 2020, Chap. I, §4, p.47][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/HerbrandFormula.lean:284`,
`standardLubinTateRealUpperRamificationGroup_natCard`][Yamaguchi2026]). -/
theorem standardLubinTateUpperRamification_natCard {π : 𝒪[K]} (hπ : Irreducible π)
    (n k : ℕ) (hk : 1 ≤ k) (hkn : k ≤ n + 1) :
    Nat.card (upperRamificationGroup K (standardLubinTateLevelField K hπ n)
        (k : ℝ)) =
      Nat.card (IsLocalRing.ResidueField 𝒪[K]) ^ (n + 1 - k) := by
  sorry

end Atlas.Knowledge
