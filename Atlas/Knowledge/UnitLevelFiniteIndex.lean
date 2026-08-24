import Mathlib
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.UnitsFiniteIndexOpen

/-!
# finite index of a unit level

A higher unit group of a mixed-characteristic local field has finite index in the
valuation-one units: the kernel of the normalized valuation is the unit group of the
integer ring, compact because the integer ring is a compact closed ball, and the level is
an open subgroup, so the quotient is finite and discrete. This is the compactness step in
Milne's computation of the Herbrand quotient of the units, and one of the two finiteness
inputs of the class field axiom.

## Main statements

* `higherUnitGroup_le_ker` — a unit level sits inside the valuation-one units; proved.
* `unitLevelFiniteIndex` — the quotient of the valuation-one units by a unit level is
  finite; proved.

## Implementation notes

Every topological ingredient is Mathlib's: the kernel is
`Atlas.Knowledge.ker_normalizedValuationHom`-identified with `𝒪[L].toSubmonoid.units`,
whose compactness is `Submonoid.units_isCompact` over the compact closed ball
`IsNonarchimedeanLocalField.isCompact_closedBall`; the level is open by
`Atlas.Knowledge.higherUnitGroup_isOpen`, restricted by `Subgroup.subgroupOf_isOpen`, and
`Subgroup.quotient_finite_of_isOpen` counts the quotient. The `T1Space` hypothesis of the
units-compactness lemma enters through the rank-one normed structure the field carries
compatibly with its topology, as in
`Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField`. The level's containment in the
kernel is the ultrametric evaluation `v (1 + m) = 1` on a maximal-ideal element `m`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsMixedCharLocalField L]

/-- **A unit level lies inside the valuation-one units**: its members are `1 + m` with `m`
in a power of the maximal ideal, and the ultrametric inequality evaluates
`v (1 + m) = 1` ([Milne 2020, Chap. III, proof of Lemma 2.5, p.105][MilneCFT]). -/
theorem higherUnitGroup_le_ker (i : ℕ+) :
    higherUnitGroup L i ≤ (normalizedValuationHom L).ker := by
  intro u hu
  rw [mem_ker_normalizedValuationHom]
  obtain ⟨m, hm⟩ := hu
  have hmval : valuation L ((m : ↥𝒪[L]) : L) < 1 := by
    have hmem1 : (m : ↥𝒪[L]) ∈ 𝓂[L] := by
      have := m.2
      exact Ideal.pow_le_self i.2.ne' this
    have hnonunit : ¬IsUnit (m : ↥𝒪[L]) :=
      fun hunit => IsLocalRing.maximalIdeal.isMaximal ↥𝒪[L] |>.ne_top
        (Ideal.eq_top_of_isUnit_mem _ hmem1 hunit)
    rwa [← Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  have huval : ((u : Lˣ) : L) = 1 + ((m : ↥𝒪[L]) : L) := hm.symm
  rw [huval]
  have hlt1 : valuation L ((m : ↥𝒪[L]) : L) < valuation L (1 : L) := by
    rw [Valuation.map_one]
    exact hmval
  rw [Valuation.map_add_eq_of_lt_left _ hlt1, Valuation.map_one]

/-- **A unit level has finite index in the valuation-one units**: the kernel of the
normalized valuation is the compact unit group of the integers and the level is open, so
the quotient is finite — "because `U_L` is compact, the quotient `U_L/V` is finite"
([Milne 2020, Chap. III, proof of Lemma 2.5, p.105][MilneCFT]; the source counterpart,
over the integer-unit carrier and through a measure-free norm argument, is
[Yamaguchi 2026, `LocalClassFieldTheory/ClassFormation/NormalBasisFiniteQuotient.lean:77`]
[Yamaguchi2026]). -/
theorem unitLevelFiniteIndex (i : ℕ+) :
    Finite (↥(normalizedValuationHom L).ker ⧸
      (higherUnitGroup L i).subgroupOf (normalizedValuationHom L).ker) := by
  letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  haveI : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := L)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := L).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField L := Valued.toNontriviallyNormedField L (ValueGroupWithZero L)
  haveI : T1Space L := inferInstance
  have hcpt : IsCompact (((𝒪[L].toSubmonoid).units : Subgroup Lˣ) : Set Lˣ) := by
    refine Submonoid.units_isCompact ?_
    have h := IsNonarchimedeanLocalField.isCompact_closedBall L 1
    convert h using 1
    ext y
    exact Valuation.mem_integer_iff _ _
  have hker : ((normalizedValuationHom L).ker : Set Lˣ) =
      (((𝒪[L].toSubmonoid).units : Subgroup Lˣ) : Set Lˣ) := by
    rw [ker_normalizedValuationHom]
  haveI : CompactSpace ↥(normalizedValuationHom L).ker :=
    isCompact_iff_compactSpace.mp (hker ▸ hcpt)
  exact Subgroup.quotient_finite_of_isOpen _
    (Subgroup.subgroupOf_isOpen _ _ (higherUnitGroup_isOpen L i))

end Atlas.Knowledge
