import Mathlib
import Atlas.Knowledge.ClosedDerivedSeries

/-!
# maximal m-step solvable extension

The **maximal `m`-step solvable extension** `k^m` of a field `k`: the subextension of an
algebraic closure fixed, under the Galois correspondence, by the `m`-th term of the closed
derived series `Atlas.Knowledge.ClosedDerivedSeries` of the absolute Galois group. For `m = 1`
this is the maximal abelian extension `k^ab`. Its Galois group over `k` is the maximal `m`-step
solvable quotient `Atlas.Knowledge.MStepSolvableQuotient` of the absolute Galois group, which is
what makes the tower `k ⊆ k^1 ⊆ k^2 ⊆ ⋯` the field-side shadow of the closed derived series.

## Main definitions

* `mStepSolvableExtension` — the intermediate field of `AlgebraicClosure k` over `k` fixed by
  `closedDerivedSeries (Field.absoluteGaloisGroup k) m`.

## Implementation notes

The source carves `k^m` out of a *separable* closure. Here it is carved out of Mathlib's
`AlgebraicClosure` via `Field.absoluteGaloisGroup`, whose Krull topology the closed derived
series needs; the two readings agree for the perfect fields this layer applies the notion to,
the mixed-characteristic local fields `Atlas.Knowledge.IsMixedCharLocalField` having
characteristic `0`. That `Gal(k^m/k)` is the maximal `m`-step solvable quotient is the infinite
Galois correspondence applied to a closed normal subgroup, and is deferred until something needs
it stated.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The **maximal `m`-step solvable extension** of `k`: the intermediate field of an algebraic
closure fixed by the `m`-th closed derived subgroup of the absolute Galois group
([Hyeon 2025, §2, p.8][Hyeon2025]). -/
noncomputable def mStepSolvableExtension (k : Type*) [Field k] (m : ℕ) :
    IntermediateField k (AlgebraicClosure k) :=
  IntermediateField.fixedField (closedDerivedSeries (Field.absoluteGaloisGroup k) m)

end Atlas.Knowledge
