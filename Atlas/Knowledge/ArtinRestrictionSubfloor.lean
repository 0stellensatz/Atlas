import Mathlib
import Atlas.Knowledge.ArtinRestrictionNormQuotient
import Atlas.Knowledge.ArtinRestrictionTower
import Atlas.Knowledge.IntermediateFieldRestrictNormalHom
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# Artin restriction to a subfloor

The Artin restriction of a finite abelian subfield `F` of the closure, followed by the
restriction `Atlas.Knowledge.intermediateFieldRestrictNormalHom` to a normal subfield
`E ≤ F`, is the Artin restriction of `E`; and the Artin image of the norm subgroup of `E` is
exactly the kernel of that restriction. The second is the fact the level-field computation of
the ramification arc rests on: on a Lubin–Tate level the Artin image of a unit step is the
image of a lower level's norm subgroup, hence a restriction kernel, with no identification of
the reciprocity map with the level character.

## Main statements

* `IsArtinRestriction.intermediateFieldRestrict` — the restricted map is the subfloor's
  Artin restriction.
* `IsArtinRestriction.map_normRange_eq_ker` — the Artin image of the subfloor's norm subgroup
  is the restriction kernel.

## Implementation notes

The first is `Atlas.Knowledge.IsArtinRestriction.restrict` at the inclusion algebra the
restriction map is defined by. The second is the kernel identity
`Atlas.Knowledge.IsArtinRestriction.ker` at the subfloor, read as the kernel of the
composite, which is the preimage of the restriction kernel, pushed forward along the
surjective `Atlas.Knowledge.IsArtinRestriction.surjective`. Both are stated over abstract
intermediate fields and applied at the concrete Lubin–Tate carriers, where the direct
restriction pattern does not elaborate.

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

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  {E F : IntermediateField K (AlgebraicClosure K)} (hEF : E ≤ F)

/-- An Artin restriction of `F` restricts along `E ≤ F` to an Artin restriction of `E`
([Serre 1979, Chap. XIII, §4, Prop. 12, p.197][Serre1979]). -/
theorem IsArtinRestriction.intermediateFieldRestrict [Normal K E] [Normal K F]
    {ρ : Kˣ →* (F ≃ₐ[K] F)} (hρ : IsArtinRestriction K F ρ) :
    IsArtinRestriction K E ((intermediateFieldRestrictNormalHom E F hEF).comp ρ) := by
  letI : Algebra E F := RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  haveI : IsScalarTower E F (AlgebraicClosure K) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact hρ.restrict K E F

/-- **The Artin image of a subfloor's norm subgroup is the kernel of restriction to it**: the
norm subgroup of `E` is the kernel of `E`'s Artin restriction, the composite of `F`'s with
the restriction, and `F`'s is onto ([Milne 2020, Chap. I, §1, Thm. 1.1 (b), p.20][MilneCFT];
Yamaguchi 2026,
`LocalClassFieldTheory/LubinTateApplication/StandardFilteredArtinComparison.lean:64`, at the
Lubin–Tate levels). -/
theorem IsArtinRestriction.map_normRange_eq_ker [FiniteDimensional K F] [IsAbelianGalois K F]
    [FiniteDimensional K E] [IsAbelianGalois K E] {ρ : Kˣ →* (F ≃ₐ[K] F)}
    (hρ : IsArtinRestriction K F ρ) :
    Subgroup.map ρ (Units.map (Algebra.norm K : E →* K)).range =
      (intermediateFieldRestrictNormalHom E F hEF).ker := by
  rw [← (hρ.intermediateFieldRestrict K hEF).ker, ← MonoidHom.comap_ker, Subgroup.map_comap_eq,
    MonoidHom.range_eq_top.2 hρ.surjective, top_inf_eq]

end Atlas.Knowledge
