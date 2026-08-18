import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.UpperRamificationGroup

/-!
# Hasse–Arf theorem

Every jump of the upper ramification filtration of a finite abelian extension of a
mixed-characteristic local field is an integer. The jump predicate — the group at `t`
differs from its right limit — is defined here; the integrality is recorded ahead of its
proof, which is the filtered local reciprocity identification: the Artin images of the
principal-unit filtration change only at natural indices, and filtered reciprocity says
they are the upper filtration. This is the campaign's stated want for the ramification
layer, and Phase 1's `map_upperRamificationGroup` and
`ramificationFiltration_eq_upperRamificationGroup` seam is what carries it from finite
floors to `Atlas.Knowledge.ramificationFiltration`.

## Main definitions

* `IsUpperRamificationJump` — the group at `t` differs from its right limit.

## Main statements

* `hasseArf` — every jump of a finite abelian extension is an integer; recorded ahead of
  its proof.

## References

* [Serre1979] J.-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**,
  Springer New York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- An **upper ramification jump**: the upper group at `t` differs from its right limit
([Serre 1979, Chap. IV, §3, Thm. (Hasse–Arf), p.76, "a jump in the filtration"]
[Serre1979];
[Yamaguchi 2026, `RamificationTheory/LocalField/Core.lean:773`,
`IsLocalUpperRamificationJump`][Yamaguchi2026]). -/
def IsUpperRamificationJump (t : ℝ) : Prop :=
  upperRamificationGroup K L t ≠
    ⨆ s : {s : ℝ // t < s}, upperRamificationGroup K L (s : ℝ)

/-- The **Hasse–Arf theorem**: every upper ramification jump of a finite abelian
extension of a mixed-characteristic local field is an integer. Claim recorded ahead of
its proof — the source derives it from filtered local reciprocity, Phase 2's engine
([Serre 1979, Chap. IV, §3, Thm. (Hasse–Arf), p.76, proof Chap. V, §7, p.93]
[Serre1979];
[Milne 2020, Chap. I, §4, p.47][MilneCFT];
[Yamaguchi 2026, `HasseArf.lean:120`, `isLocalUpperRamificationJump_int`]
[Yamaguchi2026]). -/
theorem hasseArf [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    {t : ℝ} (ht : IsUpperRamificationJump K L t) : ∃ z : ℤ, t = z := by
  sorry

end Atlas.Knowledge
