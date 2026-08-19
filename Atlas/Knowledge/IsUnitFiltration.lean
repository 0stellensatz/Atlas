import Mathlib
import Atlas.Knowledge.FilteredModule
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.ResidueCharacteristic

/-!
# unit filtration as a filtered module

The higher unit groups of a local field read as a filtered `ℤ_p`-module: the linking predicate
asking a filtered-module structure on the principal units to have the higher-unit chain of
`Atlas.Knowledge.HigherUnitGroup` as its chain, and the recorded claim that a
mixed-characteristic local field carries one. This is the object the source's §5 classifies:
its quasi-freeness is `Atlas.Knowledge.UnitFiltrationQuasiFree`, the classification by extended
jump pairs is `Atlas.Knowledge.UnitFiltrationClassification`, and the realizability of the
admissible pairs is `Atlas.Knowledge.jumpSetRealization`.

## Main definitions

* `IsUnitFiltration` — the chain of the filtered module is the higher-unit chain.

## Main statements

* `exists_isUnitFiltration` — a mixed-characteristic local field carries a `ℤ_p`-module
  structure on its principal units whose higher-unit chain is a filtered module. Claim recorded
  ahead of its proof.

## Implementation notes

A filtered module is additive and the principal units are multiplicative, so the carrier is
`Additive` of the subtype of `U 1 (K)` and the linking condition is stated on memberships: the
`i`-th step of the chain is exactly the part of `U i (K)` inside the principal units. The
`ℤ_p`-module structure is a parameter rather than a construction—the scalar action is the
continuous extension of the power maps, whose formation is exactly the content the existence
claim records, along the route of `Atlas.Knowledge.PadicExpIsomorphism`: above the threshold
the exponential identifies the deep levels with ideal powers, which are `ℤ_p`-modules already,
and the finite levels below are filled in by finiteness. Quantifying consumers over every such
parameter asserts no more than the source does, because the group determines the structure: the
principal units are a finite direct sum of copies of `ℤ_p` and a finite group, additive maps
out of `ℤ_p` with profinite target are multiplications, and so any two `ℤ_p`-scalar actions on
the principal units agree. The prime enters as a variable pinned to
`Atlas.Knowledge.ResidueCharacteristic` by an equation, the notation `ℤ_[p]` requiring a
`Fact p.Prime` instance that a projection cannot carry, as in `Atlas.Knowledge.DeepUnitGroup`.
In the existence claim the module structure is an explicit existential and the filtered module
quantifies over it with `@`, an instance bound by `∃` not being available to elaboration.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
* [FesenkoVostokov2002] I. B. Fesenko, S. V. Vostokov, *Local fields and their extensions*,
  Translations of Mathematical Monographs **121**, American Mathematical Society, second
  edition, 2002.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- The chain of a filtered `ℤ_p`-module structure on the principal units is the higher-unit
chain: the `i`-th filtration step is exactly the part of `U i (K)` inside `U 1 (K)`—the
source's `U_• (K)`, whose classification is the business of its §5
([Pagano 2022, §5, p.441][Pagano2022]). -/
def IsUnitFiltration (K : Type*) [Field K] [ValuativeRel K] (p : ℕ) [Fact p.Prime]
    [Module ℤ_[p] (Additive ↥(higherUnitGroup K 1))]
    (F : FilteredModule ℤ_[p] (Additive ↥(higherUnitGroup K 1))) : Prop :=
  ∀ (i : ℕ+) (x : ↥(higherUnitGroup K 1)),
    Additive.ofMul x ∈ F.filt i ↔ (x : Kˣ) ∈ higherUnitGroup K i

/-- A mixed-characteristic local field carries a unit filtration: a `ℤ_p`-module structure on
its principal units—the continuous extension of the power maps—for which the higher-unit chain
is a filtered module. Claim recorded ahead of its proof
([Pagano 2022, §5, pp.441–442][Pagano2022];
[Fesenko–Vostokov 2002, Chap. I, (6.1), p.17][FesenkoVostokov2002]). -/
theorem exists_isUnitFiltration (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (p : ℕ) [Fact p.Prime] (hp : p = residueCharacteristic K) :
    ∃ (m : Module ℤ_[p] (Additive ↥(higherUnitGroup K 1)))
      (F : @FilteredModule ℤ_[p] _ (Additive ↥(higherUnitGroup K 1)) _ m),
      @IsUnitFiltration K _ _ p _ m F := by
  sorry

end Atlas.Knowledge
