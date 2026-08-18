import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.IntegerIsIntegralClosure

/-!
# finite extension of a mixed-characteristic local field

A finite extension of a mixed-characteristic local field is again one. The statement splits
along what is data and what is property: given a valuative relation on `L` extending that of
`K` and inducing its topology, `L` satisfies `Atlas.Knowledge.IsMixedCharLocalField`—and such a
structure exists, the valuation of `K` prolonging to `L`. The conditional form is proved here
on top of one recorded leg, local compactness: nontriviality ascends through
`Atlas.Knowledge.IntegerIsIntegralClosure.isNontrivial`, and characteristic zero rides the
injective `algebraMap`. This is the field-side infrastructure that lets a statement about a
finite extension of a mixed-characteristic local field drop any explicit local-field hypothesis
on the extension, as `Atlas.Knowledge.CompletedUnitGroup` does.

## Main statements

* `FiniteExtensionIsMixedCharLocalField.locallyCompactSpace` — a finite extension carrying the
  valuative topology is locally compact. Claim recorded ahead of its proof.
* `finiteExtension_isMixedCharLocalField` — the conditional form: the extended structure is a
  mixed-characteristic local field structure. Proved, on top of the recorded leg.
* `exists_extension_isMixedCharLocalField` — the structure exists. Claim recorded ahead of its
  proof.

## Implementation notes

The conditional form hypothesizes `IsValuativeTopology L` rather than deriving it: the
hypothesis ties the topology of `L` to its valuative relation, and without it the statement
would quantify over junk topologies on `L` for which the local-field class is simply false.
What remains and is recorded is exactly the classical content: `L` is complete with finite
residue field, hence locally compact. The natural Mathlib route is
`LocallyCompactSpace.of_finiteDimensional_of_complete`, which asks for `K` as a
`NontriviallyNormedField`; the layer carries `K` only valuatively, so the leg waits on a norm
bridge of the kind the `ℚ_[p]` model `Atlas.Knowledge.PadicIsMixedCharLocalField` built for
`IsValuativeTopology`. The existence form quantifies the instances existentially, the pattern
of `Atlas.Knowledge.IsMLFType`, and conjoins the `Prop`-valued classes; it is what justifies
consumers that state claims about an abstract finite extension with no valuative data at all.
Uniqueness of the prolongation is classical and deliberately not recorded: no consumer compares
two structures.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

namespace FiniteExtensionIsMixedCharLocalField

/-- A finite extension of a mixed-characteristic local field, carrying a valuative relation
that extends the base and the topology it induces, is locally compact: it is complete as a
finite-dimensional topological vector space over a complete base, and its residue field is
finite. Claim recorded ahead of its proof
([Serre 1979, Chap. II, §1, Prop. 1, p.27, and §2, Prop. 3 and Cor. 1, pp.28–29][Serre1979]). -/
theorem locallyCompactSpace (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsValuativeTopology L] :
    LocallyCompactSpace L := by
  sorry

end FiniteExtensionIsMixedCharLocalField

/-- A finite extension of a mixed-characteristic local field is one: the valuative relation
extending the base, together with the topology it induces, satisfies the whole carrier
signature ([Serre 1979, Chap. II, §2, Prop. 3, pp.28–29][Serre1979]). -/
theorem finiteExtension_isMixedCharLocalField (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
    [IsValuativeTopology L] : IsMixedCharLocalField L := by
  haveI : CharZero L := charZero_of_injective_algebraMap (R := K) (algebraMap K L).injective
  haveI : ValuativeRel.IsNontrivial L := IntegerIsIntegralClosure.isNontrivial K L
  haveI := FiniteExtensionIsMixedCharLocalField.locallyCompactSpace K L
  exact {}

/-- The mixed-characteristic local field structure on a finite extension exists: the valuation
of the base prolongs to the extension, and the topology it induces completes the carrier
signature. Claim recorded ahead of its proof
([Serre 1979, Chap. II, §2, Prop. 3 and Cor. 2, pp.28–29][Serre1979]). -/
theorem exists_extension_isMixedCharLocalField (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    ∃ (_ : ValuativeRel L) (_ : TopologicalSpace L),
      ValuativeExtension K L ∧ IsValuativeTopology L ∧ IsMixedCharLocalField L := by
  sorry

end Atlas.Knowledge
