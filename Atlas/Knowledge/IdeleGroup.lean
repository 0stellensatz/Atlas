import Mathlib

/-!
# idele group

The idele group of a number field: the units of the archimedean adeles times the restricted
product of the completions' unit groups over the finite places, restricted along the local
integer units. This is the literature's `𝕀_K` with its own topology — the restricted-product
and units topology, *not* the topology the adele ring induces, under which the ideles fail
to be a topological group at all. The item carries the two facts that make the type usable:
the local unit subgroups are open, which is the `Fact` Mathlib's restricted-product
topological-group instance is gated on, and the comparison isomorphism with the units of the
adele ring, assembled from Mathlib's own equivalences because at this pin the adele ring
*is* definitionally the product of its archimedean and restricted-product halves.

## Main definitions

* `IdeleGroup` — `(InfiniteAdeleRing K)ˣ × Πʳ v, [(v.adicCompletion K)ˣ, 𝒪ᵥˣ]`.
* `ideleGroupEquivAdeleRingUnits` — `𝕀_K ≃* (𝔸_K)ˣ`, sorry-free.

## Main statements

* `isOpen_adicCompletionIntegers_units` — the local unit subgroups are open; packaged as a
  `Fact` instance, it is what makes `IdeleGroup K` a topological group by instance search.

## Implementation notes

The topology matters more than the algebra: Milne's end-of-section note records that the
adelic topology does not induce the idelic one and that the ideles are not even a
topological group under the induced topology, which is why the type is built from the
restricted product of unit groups rather than as a subspace of the adeles. That note is
about the subspace topology; `(𝔸_K)ˣ` in Mathlib carries the units topology instead, under
which it is a topological group, and the comparison below is a `MulEquiv` for a duller
reason — Mathlib's `RestrictedProduct.unitsEquiv` is algebraic only, and whether the
comparison is a homeomorphism is a separate question this item does not take up. The
`Fact` instance is the unlock for every topological instance downstream (quotients, the
identity component); Mathlib gates the restricted-product topological group on it, and the
openness proof is `Valued.isOpen_valuationSubring` through `Submonoid.isOpen_units`. The
source repository builds the same type and the same instance
(`AlgebraicNumberTheory/Idele/Topology.lean:21`).

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- The **idele group** `𝕀_K`: archimedean unit blocks times the restricted product of the
finite completions' units along the local integer units, in the restricted-product topology
([Milne 2020, Chap. V, §4, pp.169–170][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/Basic.lean:43`][Yamaguchi2026]). -/
abbrev IdeleGroup : Type _ :=
  (InfiniteAdeleRing K)ˣ ×
    Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (v.adicCompletionIntegers K).units]

/-- The unit subgroup of the local integers is open in the completion's units: the
valuation subring is open and openness passes to units. This is the `Fact` that Mathlib's
restricted-product topological-group instance is gated on
([Milne 2020, Chap. V, §4, p.170][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/Topology.lean:21`][Yamaguchi2026]). -/
theorem isOpen_adicCompletionIntegers_units (v : HeightOneSpectrum (𝓞 K)) :
    IsOpen ((v.adicCompletionIntegers K).units : Set (v.adicCompletion K)ˣ) :=
  Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)

/-- The openness of the local unit subgroups, packaged as the `Fact` instance that lets
`IsTopologicalGroup (IdeleGroup K)` and everything downstream synthesize
([Yamaguchi 2026, `AlgebraicNumberTheory/Idele/Topology.lean:27`][Yamaguchi2026]). -/
instance factIsOpenAdicCompletionIntegersUnits :
    Fact (∀ v : HeightOneSpectrum (𝓞 K),
      IsOpen ((v.adicCompletionIntegers K).units : Set (v.adicCompletion K)ˣ)) :=
  ⟨isOpen_adicCompletionIntegers_units K⟩

-- Naming the forward composite before inverting keeps `isDefEq` away from unfolding the
-- restricted-product equivalence; the inline `.symm` form times out.
private noncomputable def adeleRingUnitsEquiv :
    (AdeleRing (𝓞 K) K)ˣ ≃*
      ((InfiniteAdeleRing K)ˣ ×
        Πʳ v : HeightOneSpectrum (𝓞 K),
          [(v.adicCompletion K)ˣ, (v.adicCompletionIntegers K).units]) :=
  MulEquiv.prodUnits.trans
    ((MulEquiv.refl (InfiniteAdeleRing K)ˣ).prodCongr
      (RestrictedProduct.unitsEquiv
        (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)))

/-- The idele group is the unit group of the adele ring: `𝕀_K ≃* (𝔸_K)ˣ`, from Mathlib's
`MulEquiv.prodUnits` and `RestrictedProduct.unitsEquiv` — algebraic only: Mathlib states
the units equivalence with no continuity, and no homeomorphism is claimed here
([Milne 2020, Chap. V, §4, p.169, footnote 10][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/Basic.lean:142`][Yamaguchi2026]). -/
noncomputable def ideleGroupEquivAdeleRingUnits :
    IdeleGroup K ≃* (AdeleRing (𝓞 K) K)ˣ :=
  (adeleRingUnitsEquiv K).symm

end Atlas.Knowledge
