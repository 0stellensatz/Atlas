import Mathlib
import Atlas.Knowledge.HigherUnitGroup

/-!
# real-indexed higher unit group

The unit filtration re-indexed by a real number, as the source's §2 sets it up for comparison
with the upper-numbering ramification filtration: `U^v (K) = 1 + 𝓂[K] ^ n` for `n` the unique
integer with `n - 1 < v ≤ n`, that is, `n = ⌈v⌉`. The item is the wrapper itself—the group at
`v` is the higher unit group `Atlas.Knowledge.HigherUnitGroup` at `⌈v⌉`, never a second
filtration—together with the two facts that make it the source's object: the characterization
by `n - 1 < v ≤ n`, and antitonicity, which is what "filtration" means.

## Main definitions

* `realHigherUnitGroup` — `U^v (K) = U ⌈v⌉ (K)` as a `Subgroup Kˣ`.

## Main statements

* `realHigherUnitGroup_eq` — the source's characterization: `U^v (K) = U n (K)` for the unique
  integer `n` with `n - 1 < v ≤ n`.
* `realHigherUnitGroup_antitone` — the family decreases in `v`.
* `mem_realHigherUnitGroup_iff` — membership through the units of the integer ring at the
  `⌈t⌉₊` step, for `t > 0`: the bridge that pins the ceiling indexing against the
  literature read alongside.

## Implementation notes

Here `v` ranges over all of `ℝ` and the ceiling is clamped to `1`, so `U^v (K) = U 1 (K)` for
every `v ≤ 0`. At `v = 0` this *disagrees with the source*, which defines `U^0 (K)` to be the
full unit group: that group is not `1 + 𝓂[K] ^ n` for any `n`—at `n = 0` the translate is not
even a subgroup of `Kˣ`—so the `ℕ+`-indexed `Atlas.Knowledge.HigherUnitGroup` cannot carry it,
and the filtration the source's main theorem equips `Γ_K` with has index `> 0` and never asks
for it. The disagreement is confined to that one point; for `v < 0` the source defines nothing
and the value is junk; on `v > 0` the encoding is the source's.

## References

* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- The **real-indexed higher unit group** `U^v (K) = 1 + 𝓂[K] ^ ⌈v⌉`, the ceiling clamped to
`1`: the unit filtration in the indexing that matches the upper-numbering ramification
filtration ([Mochizuki 1997, §2, p.502][Mochizuki1997]). -/
noncomputable def realHigherUnitGroup (K : Type*) [Field K] [ValuativeRel K] (v : ℝ) :
    Subgroup Kˣ :=
  higherUnitGroup K ⌈v⌉.toNat.toPNat'

/-- The source's characterization of the re-indexing: `U^v (K)` is `U n (K)` for `n` the unique
integer with `n - 1 < v ≤ n` ([Mochizuki 1997, §2, p.502][Mochizuki1997]). -/
theorem realHigherUnitGroup_eq (K : Type*) [Field K] [ValuativeRel K] {v : ℝ} {n : ℕ+}
    (h1 : (n : ℝ) - 1 < v) (h2 : v ≤ (n : ℝ)) :
    realHigherUnitGroup K v = higherUnitGroup K n := by
  have hc : ⌈v⌉ = ((n : ℕ) : ℤ) := by
    rw [Int.ceil_eq_iff]
    push_cast
    exact ⟨h1, h2⟩
  rw [realHigherUnitGroup, hc]
  simp

/-- The real-indexed higher unit groups decrease in `v`—antitonicity being what makes the
family a filtration ([Mochizuki 1997, §2, p.502][Mochizuki1997]). -/
theorem realHigherUnitGroup_antitone (K : Type*) [Field K] [ValuativeRel K] :
    Antitone (realHigherUnitGroup K) := by
  intro v w h
  refine higherUnitGroup_antitone K ?_
  have hceil : ⌈v⌉.toNat ≤ ⌈w⌉.toNat := Int.toNat_le_toNat (Int.ceil_le_ceil h)
  rw [← PNat.coe_le_coe, Nat.toPNat'_coe, Nat.toPNat'_coe]
  split_ifs <;> omega

set_option synthInstance.maxHeartbeats 40000 in
-- The instance search on the subtype `↥(𝓂[K] ^ ⌈t⌉₊ : Ideal ↥𝒪[K])` is the expensive step
-- and does not fit the default budget.
/-- Membership in the real-indexed higher unit group through the units of the integer ring:
for `t > 0`, `x ∈ U^t (K)` iff some unit of `𝒪[K]` congruent to `1` modulo `𝓂[K] ^ ⌈t⌉₊`
maps to `x` — the `ℕ`-ceiling made explicit, so the `Int`-ceiling-then-clamp indexing of the
definition and the `⌈t⌉₊` stepping of the literature read alongside are pinned to agree on
`t > 0` ([Yamaguchi 2026, `RamificationTheory/Filtration.lean:23`][Yamaguchi2026]). -/
theorem mem_realHigherUnitGroup_iff (K : Type*) [Field K] [ValuativeRel K]
    {t : ℝ} (ht : 0 < t) (x : Kˣ) :
    x ∈ realHigherUnitGroup K t ↔
      ∃ u : (↥𝒪[K])ˣ,
        ((u : ↥𝒪[K]) - 1) ∈ (𝓂[K] ^ ⌈t⌉₊ : Ideal ↥𝒪[K]) ∧
          Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u = x := by
  have hidx : (⌈t⌉.toNat.toPNat' : ℕ) = ⌈t⌉₊ := by
    rw [← Int.ceil_toNat]
    have hpos : 0 < ⌈t⌉ := Int.ceil_pos.mpr ht
    rcases Nat.exists_eq_succ_of_ne_zero (n := ⌈t⌉.toNat) (by omega) with ⟨k, hk⟩
    simp [hk]
  rw [realHigherUnitGroup, mem_higherUnitGroup_iff, hidx]

end Atlas.Knowledge
