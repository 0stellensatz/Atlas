import Mathlib
import Atlas.Knowledge.ExistsValuativeExtension
import Atlas.Knowledge.IntermediateFieldRestrictNormalHom
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.UpperRamificationGroup

/-!
# upper ramification groups under subfloor restriction

Herbrand's compatibility of the upper numbering with quotients,
`Atlas.Knowledge.map_upperRamificationGroup`, read along the layer's restriction map
`Atlas.Knowledge.intermediateFieldRestrictNormalHom` between two subfields `E ≤ F` of the
algebraic closure of a mixed-characteristic local field: the image of `G^v (F/K)` is
`G^v (E/K)`, and so `G^v (F/K)` lies in the restriction kernel as soon as `G^v (E/K)` is
trivial. The second form is how the ramification arc places an upper group of a compositum
inside the kernel of restriction to its unramified factor.

## Main statements

* `map_upperRamificationGroup_intermediateFieldRestrictNormalHom` — the image is the
  subfloor's upper group.
* `upperRamificationGroup_le_ker_intermediateFieldRestrictNormalHom` — containment in the
  kernel when the subfloor's group vanishes.

## Implementation notes

The restriction map is defined by a `letI` on the inclusion algebra; the proof reinstalls it,
equips the subfloor with a compatible valuation by
`Atlas.Knowledge.exists_valuativeExtension`, and closes by the abstract-tower statement.
Stated over abstract intermediate fields for the same reason as its siblings: applied at the
concrete Lubin–Tate carriers, the direct pattern does not elaborate.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  {E F : IntermediateField K (AlgebraicClosure K)} (hEF : E ≤ F)

/-- **Upper ramification groups descend along the subfloor restriction**: the image of
`G^v (F/K)` under restriction to `E` is `G^v (E/K)`
([Serre 1979, Chap. IV, §3, Prop. 14, p.74][Serre1979]). -/
theorem map_upperRamificationGroup_intermediateFieldRestrictNormalHom [FiniteDimensional K F]
    [IsGalois K F] [Normal K E] (v : ℝ) :
    Subgroup.map (intermediateFieldRestrictNormalHom E F hEF) (upperRamificationGroup K F v) =
      upperRamificationGroup K E v := by
  letI : Algebra E F := RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  haveI : FiniteDimensional E F := Module.Finite.right K E F
  haveI : Algebra.IsAlgebraic E F := Algebra.IsAlgebraic.of_finite E F
  obtain ⟨vE, hvE⟩ := exists_valuativeExtension K E
  letI := vE
  haveI := hvE
  exact map_upperRamificationGroup K F E v

/-- An upper group of the floor lies in the restriction kernel once the subfloor's upper
group at the same index is trivial ([Serre 1979, Chap. IV, §3, Prop. 14, p.74][Serre1979]). -/
theorem upperRamificationGroup_le_ker_intermediateFieldRestrictNormalHom [FiniteDimensional K F]
    [IsGalois K F] [Normal K E] {v : ℝ} (h : upperRamificationGroup K E v = ⊥) :
    upperRamificationGroup K F v ≤ (intermediateFieldRestrictNormalHom E F hEF).ker := by
  rw [← Subgroup.map_eq_bot_iff,
    map_upperRamificationGroup_intermediateFieldRestrictNormalHom K hEF v]
  exact h

end Atlas.Knowledge
