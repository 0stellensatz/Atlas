import Mathlib
import Atlas.Knowledge.ClosedDerivedSeries
import Atlas.Knowledge.MStepSolvableExtension
import Atlas.Knowledge.MStepSolvableQuotient
import Atlas.Knowledge.IsMLFType

/-!
# m-step solvable quotient of a subextension

The field side of the stability of `m`-step solvable quotients: for a finite subextension `l`
inside the maximal `m`-step solvable extension `Atlas.Knowledge.MStepSolvableExtension` of `k`,
the `n`-step solvable quotient of the absolute Galois group of `l` is computed at the
`(m + n)`-th level of the tower—it is the `n`-step solvable quotient of the image of the fixing
subgroup of `l` in `Gal (k^{m+n} / k)`. This is the identity through which the group side,
`Atlas.Knowledge.MStepSolvableStability`, speaks about fields: an open subgroup of a truncation
is the Galois group of a finite subextension, by the identification of
`Atlas.Knowledge.AbsoluteGaloisSubextension`. The "in particular" of the source's lemma is the
typeness corollary: an open subgroup of a group of MLF^{m+n}-type above the `m`-th derived term
has `n`-step solvable quotient of MLF^n-type.

## Main statements

Both are claims recorded ahead of their proofs.

* `mStepSolvableSubextension_continuousMulEquiv` — the level identity: the `n`-step solvable
  quotient of `Field.absoluteGaloisGroup ↥l` is that of the image of `l.fixingSubgroup` at
  level `m + n`.
* `isMLFmType_mStepSolvableQuotient` — the typeness corollary, on abstract groups.

## Implementation notes

The truncated Galois group `Gal (k^{m+n} / l)` is encoded as the image of `l.fixingSubgroup`
under the projection onto `mStepSolvableQuotient (Field.absoluteGaloisGroup k) (m + n)`, which
reads the tower group-theoretically and keeps the statement inside the vocabulary of
`Atlas.Knowledge.ClosedDerivedSeries`; the identification of that image with the automorphism
group of the level field is the Galois correspondence and enters the proof, not the statement.
`CharZero` is what makes the correspondence available on Mathlib's algebraic closure, per the
encoding note of `Atlas.Knowledge.MStepSolvableExtension`. The containment hypothesis is
load-bearing: without it the identity has no reason to hold—already at `m = 0`, `n = 1` the
left side is the full abelianization of the subextension's Galois group while the right side
sees only its image in that of `k`. The typeness corollary quantifies a bare
topological group, profiniteness arriving through the isomorphism its hypothesis asserts; the
witness for the conclusion is the fixed field of the preimage of `H`, a finite extension of the
witness for `G` and a mixed-characteristic local field by
`Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

universe u

/-- The level identity for a finite subextension `l` of the maximal `m`-step solvable
extension of `k`: the `n`-step solvable quotient of the absolute Galois group of `l` is the
`n`-step solvable quotient of the image of `l.fixingSubgroup` at level `m + n`—classically,
the `n`-step solvable quotient of `Gal (k^{m+n} / l)`. Claim recorded ahead of its proof
([Hyeon 2025, Lem. 2.3 (2), p.8][Hyeon2025]). -/
theorem mStepSolvableSubextension_continuousMulEquiv (k : Type*) [Field k] [CharZero k]
    (m n : ℕ) (l : IntermediateField k (AlgebraicClosure k)) [FiniteDimensional k ↥l]
    (hl : l ≤ mStepSolvableExtension k m) :
    Nonempty (mStepSolvableQuotient (Field.absoluteGaloisGroup ↥l) n ≃ₜ*
      mStepSolvableQuotient
        ↥(Subgroup.map
          (QuotientGroup.mk' (closedDerivedSeries (Field.absoluteGaloisGroup k) (m + n)))
          l.fixingSubgroup) n) := by
  sorry

/-- An open subgroup of a group of MLF^{m+n}-type containing the `m`-th term of the closed
derived series has `n`-step solvable quotient of MLF^n-type—the "in particular" of the level
identity, read through `Atlas.Knowledge.MStepSolvableStability`. Claim recorded ahead of its
proof ([Hyeon 2025, Lem. 2.3 (2), p.8][Hyeon2025]). -/
theorem isMLFmType_mStepSolvableQuotient {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {m n : ℕ} (hG : IsMLFmType.{u} G (m + n)) {H : Subgroup G}
    (hH : IsOpen (H : Set G)) (hm : closedDerivedSeries G m ≤ H) :
    IsMLFmType.{u} (mStepSolvableQuotient ↥H n) n := by
  sorry

end Atlas.Knowledge
