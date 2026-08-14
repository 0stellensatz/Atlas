import Mathlib
import Atlas.Knowledge.LowerRamificationGroup

/-!
# real-indexed lower ramification group

The lower-numbering ramification filtration re-indexed by a real number, as the source sets it
up to define the Herbrand functions: `G_u = G_i` for `i` the smallest integer `≥ u`, that is,
`i = ⌈u⌉`. The item is the wrapper itself—the group at `u` is
`Atlas.Knowledge.lowerRamificationGroup` at `⌈u⌉`, never a second filtration—together with the
two facts that make it the source's object: the characterization by `i - 1 < u ≤ i`, and
antitonicity. `Atlas.Knowledge.HerbrandPhi` integrates through this family, and
`Atlas.Knowledge.UpperRamificationGroup` re-indexes it once more.

## Main definitions

* `realLowerRamificationGroup` — `G_u = G ⌈u⌉` as a subgroup of `L ≃ₐ[K] L`.

## Main statements

* `realLowerRamificationGroup_eq` — the characterization: `G_u = G_i` for the unique integer
  `i` with `i - 1 < u ≤ i`.
* `realLowerRamificationGroup_antitone` — the family decreases in `u`.

## Implementation notes

Here `u` ranges over all of `ℝ`, and the junk region of the integer-indexed family is
inherited unchanged: for `u ≤ -1` the ceiling is `≤ -1` and the group is all of `L ≃ₐ[K] L`,
which at `u = -1` is the source's `G_{-1} = G` and below it is junk. The source introduces
this re-indexing in passing at the head of its §3; the characterization by
`i - 1 < u ≤ i` is the form the definition of the Herbrand function `φ` consumes.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- The **real-indexed lower ramification group** `G_u = G ⌈u⌉`: the lower-numbering
filtration in the indexing under which the Herbrand functions renumber it
([Serre 1979, Chap. IV, §3, p.73][Serre1979]). -/
noncomputable def realLowerRamificationGroup (u : ℝ) : Subgroup (L ≃ₐ[K] L) :=
  lowerRamificationGroup K L ⌈u⌉

/-- The source's characterization of the re-indexing: `G_u` is `G_i` for `i` the unique
integer with `i - 1 < u ≤ i` ([Serre 1979, Chap. IV, §3, p.73][Serre1979]). -/
theorem realLowerRamificationGroup_eq {u : ℝ} {i : ℤ} (h1 : (i : ℝ) - 1 < u)
    (h2 : u ≤ (i : ℝ)) : realLowerRamificationGroup K L u = lowerRamificationGroup K L i := by
  have hc : ⌈u⌉ = i := by
    rw [Int.ceil_eq_iff]
    exact ⟨h1, h2⟩
  rw [realLowerRamificationGroup, hc]

/-- The real-indexed lower ramification groups decrease in `u`—the integer-indexed decrease of
the source, transported through the ceiling
([Serre 1979, Chap. IV, §1, Prop. 1, p.62][Serre1979]). -/
theorem realLowerRamificationGroup_antitone : Antitone (realLowerRamificationGroup K L) :=
  fun _ _ h => lowerRamificationGroup_antitone K L (Int.ceil_le_ceil h)

instance (u : ℝ) : (realLowerRamificationGroup K L u).Normal :=
  inferInstanceAs ((lowerRamificationGroup K L ⌈u⌉).Normal)

end Atlas.Knowledge
