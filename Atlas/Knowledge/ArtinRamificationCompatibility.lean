import Mathlib
import Atlas.Knowledge.FiniteAbelianRamificationDescent
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.RealHigherUnitGroup
import Atlas.Knowledge.UpperRamificationGroup

/-!
# ramification compatibility of the Artin map

The reciprocity map matches the unit filtration with the ramification filtration: for a
finite abelian extension `L` of a mixed-characteristic local field `K`, the Artin image of
the `t`th higher unit group is the `t`th upper-numbering ramification group, `t > 0`, and the
image of the full unit group `U⁰ = 𝒪[K]ˣ` is the inertia end `G⁰`. This is what the upper
numbering is for on the abelian side, and the real-indexed statement silently encodes
Hasse–Arf — between integers both filtrations are constant only because the extension is
abelian. Both statements are proved, by descent from the standard Lubin–Tate compositum every
finite abelian floor lies in.

## Main statements

* `artinRamificationCompatibility` — `Art (U^t) = G^t` for `t > 0`.
* `artinRamificationCompatibility_zero` — `Art (U^0) = G^0`, the inertia endpoint.

## Implementation notes

The split at `t = 0` is deliberate and load-bearing: `Atlas.Knowledge.realHigherUnitGroup`
clamps `t = 0` to `U^1` — its documented junk region — so the single statement over `t ≥ 0`
would be *false* at `0` for every ramified extension. The endpoint theorem instead renders
`U^0` as the range of `𝒪[K]ˣ` in `Kˣ`, and the two statements together cover the source's
exact `t ≥ 0` scope. The source proves this box in both residue characteristics; the
rendering here inherits mixed characteristic through the hypothesis
`Atlas.Knowledge.IsArtinRestriction`, whose absolute reciprocity lives over the algebraic
closure — the equal-characteristic generality would need a separable-closure vocabulary the
layer does not carry. The bridge between the unit filtration here and the source's
integer-level principal units is recorded on `Atlas.Knowledge.HigherUnitGroup` and
`Atlas.Knowledge.RealHigherUnitGroup`. The proofs are the descent of
`Atlas.Knowledge.FiniteAbelianRamificationDescent`: the statement is proved on the standard
compositum `Tₙ ⊔ K (μ_{q ^ d − 1})` of `Atlas.Knowledge.StandardCompositum`, where both sides
are the kernel of restriction to the unramified factor, carried down to the floor's range in
the closure by restriction, and to the floor itself by its structure map. Neither statement
mentions the level character: the Artin image of a unit step on a level is the image of a
lower level's norm subgroup, a restriction kernel, and the upper group is the same kernel by
its order.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic
  local fields*, J. London Math. Soc. **112** (2025), e70402.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  (L : Type*) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsAbelianGalois K L]
  [Algebra L (AlgebraicClosure K)] [IsScalarTower K L (AlgebraicClosure K)]

/-- **Ramification compatibility** of the Artin map: for a finite abelian extension of a
mixed-characteristic local field, the reciprocity image of the `t`th higher unit group is the
`t`th upper-numbering ramification group, `t > 0`
([Serre 1979, Chap. XV, §2, Thm. 2 and Remark, p.228][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/FiniteAbelian.lean:30`). -/
theorem artinRamificationCompatibility (ρ : Kˣ →* (L ≃ₐ[K] L))
    (hρ : IsArtinRestriction K L ρ) {t : ℝ} (ht : 0 < t) :
    Subgroup.map ρ (realHigherUnitGroup K t) = upperRamificationGroup K L t :=
  map_eq_upperRamificationGroup_of_algEquiv K L _ t
    (fun L' _ _ ρ' hρ' => map_realHigherUnitGroup_of_finiteAbelian K L' ρ' hρ' ht) ρ hρ

/-- The inertia endpoint of the ramification compatibility: the reciprocity image of the full
unit group `U^0 = 𝒪[K]ˣ` is `G^0`, the inertia group. Stated separately because
`Atlas.Knowledge.realHigherUnitGroup` clamps `t = 0` to `U^1`, where the compatibility would
be false for every ramified extension
([Serre 1979, Chap. XIII, §4, Cor. to Prop. 13, p.198][Serre1979];
[Hyeon 2025, §3, p.10][Hyeon2025]; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/FiniteAbelian.lean:30`). -/
theorem artinRamificationCompatibility_zero (ρ : Kˣ →* (L ≃ₐ[K] L))
    (hρ : IsArtinRestriction K L ρ) :
    Subgroup.map ρ (MonoidHom.range (Units.map (𝒪[K].subtype : ↥𝒪[K] →* K))) =
      upperRamificationGroup K L 0 :=
  map_eq_upperRamificationGroup_of_algEquiv K L _ 0
    (fun L' _ _ ρ' hρ' => map_units_of_finiteAbelian K L' ρ' hρ') ρ hρ

end Atlas.Knowledge
