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

## Implementation notes

The source lets `v` range over `v ≥ 0`, with `U^0 (K) = U (K)` the full unit group; but the
filtration its main theorem equips `Γ_K` with is the one with index `> 0`, and only that part
is representable as `1 + 𝓂[K] ^ n`. Here `v` ranges over all of `ℝ` and the ceiling is clamped
to `1`, so `U^v (K) = U 1 (K)` for every `v ≤ 0`: junk values below the source's range, the
principal unit group on `(0, 1]` and beyond as in the source.

## References

* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- The **real-indexed higher unit group** `U^v (K) = 1 + 𝓂[K] ^ ⌈v⌉`, the unit filtration in
the indexing that matches the upper-numbering ramification filtration
([Mochizuki 1997, §2, p.502][Mochizuki1997]). -/
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

/-- The real-indexed higher unit groups decrease in `v`, so the family is a filtration in the
sense of `Atlas.Knowledge.FilteredProfiniteGroup`
([Mochizuki 1997, §2, p.502][Mochizuki1997]). -/
theorem realHigherUnitGroup_antitone (K : Type*) [Field K] [ValuativeRel K] :
    Antitone (realHigherUnitGroup K) := by
  intro v w h
  refine higherUnitGroup_antitone K ?_
  have hceil : ⌈v⌉.toNat ≤ ⌈w⌉.toNat := Int.toNat_le_toNat (Int.ceil_le_ceil h)
  rw [← PNat.coe_le_coe, Nat.toPNat'_coe, Nat.toPNat'_coe]
  split_ifs <;> omega

end Atlas.Knowledge
