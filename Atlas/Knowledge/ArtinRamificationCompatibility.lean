import Mathlib
import Atlas.Knowledge.RealHigherUnitGroup
import Atlas.Knowledge.UpperRamificationGroup
import Atlas.Knowledge.IsArtinRestriction

/-!
# ramification compatibility of the Artin map

The reciprocity map matches the unit filtration with the ramification filtration: for a
finite abelian extension `L` of a mixed-characteristic local field `K`, the Artin image of
the `t`th higher unit group is the `t`th upper-numbering ramification group, `t > 0`, and
the image of the full unit group `U⁰ = 𝒪[K]ˣ` is the inertia end `G⁰`. This is what the
upper numbering is for on the abelian side, and the real-indexed statement silently encodes
Hasse–Arf — between integers both filtrations are constant only because the extension is
abelian. Both statements are recorded ahead of their proofs.

## Main statements

* `artinRamificationCompatibility` — `Art (U^t) = G^t` for `t > 0`.
* `artinRamificationCompatibility_zero` — `Art (U^0) = G^0`, the inertia endpoint.

## Implementation notes

The split at `t = 0` is deliberate and load-bearing:
`Atlas.Knowledge.realHigherUnitGroup` clamps `t = 0` to `U^1` — its documented junk region —
so the single statement over `t ≥ 0` would be *false* at `0` for every ramified extension.
The endpoint theorem instead renders `U^0` as the range of `𝒪[K]ˣ` in `Kˣ`, and the two
statements together cover the source's exact `t ≥ 0` scope. The source proves this box in
both residue characteristics; the rendering here inherits mixed characteristic through the
hypothesis `Atlas.Knowledge.IsArtinRestriction`, whose absolute reciprocity lives over the
algebraic closure — the equal-characteristic generality would need a separable-closure
vocabulary the layer does not carry. The bridge between the unit filtration here and the
source's integer-level principal units is recorded on
`Atlas.Knowledge.HigherUnitGroup` and `Atlas.Knowledge.RealHigherUnitGroup`.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic
  local fields*, J. London Math. Soc. **112** (2025), e70402.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  (L : Type*) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsAbelianGalois K L]
  [Algebra L (AlgebraicClosure K)] [IsScalarTower K L (AlgebraicClosure K)]

/-- **Ramification compatibility** of the Artin map: for a finite abelian extension of a
mixed-characteristic local field, the reciprocity image of the `t`th higher unit group is
the `t`th upper-numbering ramification group, `t > 0`. Claim recorded ahead of its proof
([Serre 1979, Chap. XV, §2, Thm. 2 and Remark, p.228][Serre1979];
[Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/FiniteAbelian.lean:30`]
[Yamaguchi2026]). -/
theorem artinRamificationCompatibility (ρ : Kˣ →* (L ≃ₐ[K] L))
    (hρ : IsArtinRestriction K L ρ) {t : ℝ} (ht : 0 < t) :
    Subgroup.map ρ (realHigherUnitGroup K t) = upperRamificationGroup K L t := by
  sorry

/-- The inertia endpoint of the ramification compatibility: the reciprocity image of the
full unit group `U^0 = 𝒪[K]ˣ` is `G^0`, the inertia group. Stated separately because
`Atlas.Knowledge.realHigherUnitGroup` clamps `t = 0` to `U^1`, where the compatibility would
be false for every ramified extension. Claim recorded ahead of its proof
([Serre 1979, Chap. XIII, §4, Cor. to Prop. 13, p.198][Serre1979];
[Hyeon 2025, §3, p.10][Hyeon2025];
[Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/FiniteAbelian.lean:30`]
[Yamaguchi2026]). -/
theorem artinRamificationCompatibility_zero (ρ : Kˣ →* (L ≃ₐ[K] L))
    (hρ : IsArtinRestriction K L ρ) :
    Subgroup.map ρ (MonoidHom.range (Units.map (𝒪[K].subtype : ↥𝒪[K] →* K))) =
      upperRamificationGroup K L 0 := by
  sorry

end Atlas.Knowledge
