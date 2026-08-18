import Mathlib
import Atlas.Knowledge.HerbrandPsi

/-!
# upper-numbering ramification group

The ramification filtration of a finite Galois extension of local fields in the upper
numbering: `G^v = G_{ψ (v)}`, the lower filtration read through the inverse Herbrand function
`Atlas.Knowledge.HerbrandPsi`. The lower numbering is adapted to subgroups—`H_i = G_i ∩ H`—and
the upper numbering to quotients: the ramification groups of a quotient are the images of the
`G^v`, which is the compatibility proved here and the reason the filtration of an infinite
Galois group, `Atlas.Knowledge.RamificationFiltration`, is defined in the upper numbering.

## Main definitions

* `upperRamificationGroup` — `G^v = G_{ψ (v)}` as a subgroup of `L ≃ₐ[K] L`.

## Main statements

* `upperRamificationGroup_zero` — `G^0 = G_0`, the inertia end of the filtration.
* `upperRamificationGroup_antitone` — the family decreases in `v`.
* `map_upperRamificationGroup` — compatibility with quotients.
* `herbrandPsi_eq_integral` — the source's direct description
  `ψ (v) = ∫ w in 0..v, (G^0 : G^w)`, recorded ahead of its proof.

## Implementation notes

`G^v` is `Atlas.Knowledge.realLowerRamificationGroup` at `ψ (v)` by definition, so the junk
regions of the two ingredients compose: below `v = -1` the value is the whole group, and
without `FiniteDimensional K L` the function `ψ` is junk and the numbering with it—the
statements beyond the definition assume finiteness. The quotient compatibility is stated over
an abstract tower `K ⊆ E ⊆ L`, with `ValuativeExtension K E` pinning the valuation of `E`, as
in `Atlas.Knowledge.HerbrandPhi`.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic
  local fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- The **upper-numbering ramification group** `G^v = G_{ψ (v)}`: the lower filtration
renumbered through the inverse Herbrand function
([Serre 1979, Chap. IV, §3, p.74][Serre1979]). -/
noncomputable def upperRamificationGroup (v : ℝ) : Subgroup (L ≃ₐ[K] L) :=
  realLowerRamificationGroup K L (herbrandPsi K L v)

instance (v : ℝ) : (upperRamificationGroup K L v).Normal :=
  inferInstanceAs ((realLowerRamificationGroup K L (herbrandPsi K L v)).Normal)

variable [FiniteDimensional K L]

/-- At `v = 0` the two numberings agree: `G^0 = G_0` is the inertia end of the filtration
([Serre 1979, Chap. IV, §3, p.74][Serre1979]). -/
theorem upperRamificationGroup_zero :
    upperRamificationGroup K L 0 = lowerRamificationGroup K L 0 := by
  rw [upperRamificationGroup, herbrandPsi_zero, realLowerRamificationGroup, Int.ceil_zero]

/-- The upper-numbering ramification groups decrease in `v`
([Serre 1979, Chap. IV, §3, p.74][Serre1979]). -/
theorem upperRamificationGroup_antitone : Antitone (upperRamificationGroup K L) :=
  fun _ _ h =>
    realLowerRamificationGroup_antitone K L ((herbrandPsi_strictMono K L).monotone h)

section Tower

variable (E : Type*) [Field E] [ValuativeRel E] [Algebra K E] [Algebra E L]
  [IsScalarTower K E L] [ValuativeExtension K E] [Algebra.IsAlgebraic E L]

/-- Compatibility of the upper numbering with quotients: for a normal subextension `E` of a
finite Galois extension `L` of a mixed-characteristic local field `K`, the image of `G^v`
under restriction to `E` is the `v`th upper-numbering ramification group of `E` over
`K`—same index, no renumbering; this is what the upper numbering is for. Herbrand's theorem
at `ψ_{L/K} (v)`, the index unwound by the transitivity of `ψ`
([Serre 1979, Chap. IV, §3, Prop. 14, p.74][Serre1979];
[Hyeon 2025, §2, (2), p.7][Hyeon2025]). -/
theorem map_upperRamificationGroup [TopologicalSpace K] [IsMixedCharLocalField K]
    [IsGalois K L] [Normal K E] (v : ℝ) :
    Subgroup.map (AlgEquiv.restrictNormalHom E) (upperRamificationGroup K L v) =
      upperRamificationGroup K E v := by
  haveI : FiniteDimensional K E := FiniteDimensional.left K E L
  haveI : FiniteDimensional E L := Module.Finite.right K E L
  rw [upperRamificationGroup, upperRamificationGroup, map_realLowerRamificationGroup K L E,
    herbrandPsi_comp K L E, herbrandPhi_herbrandPsi]

end Tower

/-- The source's direct description of the inverse Herbrand function through the upper
numbering: `ψ (v) = ∫ w in 0..v, (G^0 : G^w)`, the index rendered as a ratio of cardinalities.
Claim recorded ahead of its proof ([Serre 1979, Chap. IV, §3, p.74][Serre1979]). -/
theorem herbrandPsi_eq_integral (v : ℝ) :
    herbrandPsi K L v = ∫ w in (0 : ℝ)..v,
      (Nat.card (upperRamificationGroup K L 0) : ℝ) /
        (Nat.card (upperRamificationGroup K L w) : ℝ) := by
  sorry

end Atlas.Knowledge
