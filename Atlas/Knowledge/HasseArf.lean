import Mathlib
import Atlas.Knowledge.ArtinRamificationCompatibility
import Atlas.Knowledge.ArtinRestrictionAutCongr
import Atlas.Knowledge.HerbrandPhi
import Atlas.Knowledge.HerbrandPsi
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LowerRamificationGroup
import Atlas.Knowledge.RealHigherUnitGroup
import Atlas.Knowledge.RealLowerRamificationGroup
import Atlas.Knowledge.UpperRamificationGroup

/-!
# Hasse–Arf theorem

Every jump of the upper ramification filtration of a finite abelian extension of a
mixed-characteristic local field is an integer. The jump predicate — the group at `t` differs
from its right limit — is defined here; the integrality is proved by the filtered local
reciprocity identification `Atlas.Knowledge.artinRamificationCompatibility`: above `0` the
upper filtration is the Artin image of the unit filtration, which changes only at the
integers, and below `0` it is constant on `(-1, 0]` and equal to the whole group below `-1`,
so a jump is at an integer. This is the campaign's stated want for the ramification layer,
and Phase 1's `map_upperRamificationGroup` and
`ramificationFiltration_eq_upperRamificationGroup` seam is what carries it from finite floors
to `Atlas.Knowledge.ramificationFiltration`.

## Main definitions

* `IsUpperRamificationJump` — the group at `t` differs from its right limit.

## Main statements

* `hasseArf` — every jump of a finite abelian extension is an integer.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- An **upper ramification jump**: the upper group at `t` differs from its right limit
([Serre 1979, Chap. IV, §3, Thm. (Hasse–Arf), p.76, "a jump in the filtration"] [Serre1979];
Yamaguchi 2026, `RamificationTheory/LocalField/Core.lean:773`,
`IsLocalUpperRamificationJump`). -/
def IsUpperRamificationJump (t : ℝ) : Prop :=
  upperRamificationGroup K L t ≠
    ⨆ s : {s : ℝ // t < s}, upperRamificationGroup K L (s : ℝ)

/-- The **Hasse–Arf theorem**: every upper ramification jump of a finite abelian extension of
a mixed-characteristic local field is an integer — from filtered local reciprocity, as the
source derives it: an upper group at `t > 0` is the Artin image of `U^{⌈t⌉}`, constant on
`(⌈t⌉ − 1, ⌈t⌉]`, while at `t < -1` the group is everything and on `(-1, 0]` it is the
inertia group, so a jump can sit only at an integer
([Serre 1979, Chap. IV, §3, Thm. (Hasse–Arf), p.76, proof Chap. V, §7, p.93] [Serre1979];
[Milne 2020, Chap. I, §4, p.47][MilneCFT]; Yamaguchi 2026, `HasseArf.lean:120`,
`isLocalUpperRamificationJump_int`). -/
theorem hasseArf [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    {t : ℝ} (ht : IsUpperRamificationJump K L t) : ∃ z : ℤ, t = z := by
  letI : Algebra L (AlgebraicClosure K) :=
    (IsAlgClosed.lift : L →ₐ[K] AlgebraicClosure K).toRingHom.toAlgebra
  haveI : IsScalarTower K L (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq
      (fun x => ((IsAlgClosed.lift : L →ₐ[K] AlgebraicClosure K).commutes x).symm)
  obtain ⟨ρ, hρ⟩ := exists_isArtinRestriction_of_finiteDimensional K L
  by_contra hz
  push Not at hz
  apply ht
  -- a point just above `t` with the same group makes the right limit the group at `t`
  suffices h : ∃ s₀, t < s₀ ∧ upperRamificationGroup K L s₀ = upperRamificationGroup K L t by
    obtain ⟨s₀, hs₀, heq⟩ := h
    apply le_antisymm
    · exact le_iSup_of_le ⟨s₀, hs₀⟩ (le_of_eq heq.symm)
    · exact iSup_le fun s : {s : ℝ // t < s} => upperRamificationGroup_antitone K L s.2.le
  rcases lt_trichotomy t (-1) with h1 | h1 | h1
  · -- below `-1` the group is everything
    refine ⟨(t + (-1)) / 2, by linarith, ?_⟩
    have key : ∀ s, s < -1 → upperRamificationGroup K L s = ⊤ := by
      intro s hs
      unfold upperRamificationGroup realLowerRamificationGroup
      apply lowerRamificationGroup_eq_top
      rw [Int.ceil_le]
      have := herbrandPsi_strictMono K L hs
      rw [← herbrandPhi_neg_one K L, herbrandPsi_herbrandPhi] at this
      push_cast
      exact this.le
    rw [key _ (by linarith), key _ h1]
  · exact (hz (-1) (by rw [h1]; simp)).elim
  · rcases lt_trichotomy t 0 with h2 | h2 | h2
    · -- on `(-1, 0]` the group is the inertia group
      refine ⟨t / 2, by linarith, ?_⟩
      have key : ∀ s, -1 < s → s ≤ 0 →
          upperRamificationGroup K L s = lowerRamificationGroup K L 0 := by
        intro s hs1 hs2
        unfold upperRamificationGroup realLowerRamificationGroup
        congr 1
        rw [Int.ceil_eq_iff]
        push_cast
        constructor
        · have := herbrandPsi_strictMono K L hs1
          rw [← herbrandPhi_neg_one K L, herbrandPsi_herbrandPhi] at this
          linarith
        · have := (herbrandPsi_strictMono K L).monotone hs2
          rwa [herbrandPsi_zero] at this
      rw [key _ (by linarith) (by linarith), key _ h1 h2.le]
    · exact (hz 0 (by rw [h2]; simp)).elim
    · -- above `0` the group is the Artin image of the unit step at the ceiling
      have hne : t ≠ ⌈t⌉ := hz ⌈t⌉
      have hlt : t < ⌈t⌉ := lt_of_le_of_ne (Int.le_ceil t) hne
      refine ⟨(⌈t⌉ : ℝ), hlt, ?_⟩
      rw [← artinRamificationCompatibility K L ρ hρ (by linarith : (0 : ℝ) < ⌈t⌉),
        ← artinRamificationCompatibility K L ρ hρ h2]
      congr 1
      unfold realHigherUnitGroup
      rw [Int.ceil_intCast]

end Atlas.Knowledge
