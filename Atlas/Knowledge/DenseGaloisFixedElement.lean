import Mathlib

/-!
# dense Galois fixed element

An element of a Galois extension fixed by a dense set of automorphisms lies in the base
field. This is the infinite Galois correspondence read at one element: the automorphisms
fixing `x` form its stabilizer, open in the Krull topology because `x` is integral and hence
closed, so a dense set of them is all of them, and the fixed field of the whole group is the
base. It is the form in which the dense range of a reciprocity map reaches an element: in
`Atlas.Knowledge.LocalHilbertSymbolNondegeneracy` a root killed against every lift of every
value of the map is fixed by a dense set of automorphisms, hence rational, which is the left
kernel of the Hilbert symbol.

## Main statements

* `denseGaloisFixedElement` — an element fixed by a dense set of automorphisms lies in the
  base field; proved.

## Implementation notes

The set `S` is an arbitrary dense set of automorphisms, not a subgroup: density and the
pointwise condition are all the argument consumes. Closedness is Mathlib's
`stabilizer_isOpen_of_isIntegral` through `Subgroup.isClosed_of_isOpen` — no adjoined field
and no finite-dimensionality enters — and the last step is
`InfiniteGalois.mem_range_algebraMap_iff_fixed`. The Galois hypothesis is what makes the
fixed field of the full group the base; over an algebraic closure in characteristic zero it
is automatic, which is how the Hilbert-symbol consumer meets it.

## References

* [MilneFT] J. S. Milne, *Fields and Galois theory* (v5.10), available at www.jmilne.org/math/,
  2022.
-/

namespace Atlas.Knowledge

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- An element of a Galois extension fixed by a dense set of automorphisms lies in the base
field: its stabilizer is closed and contains the dense set, so it is the whole group, and the
fixed field of the whole Galois group is the base
([Milne 2022, Chap. 7, Prop. 7.9 and Prop. 7.12 (b), p.97][MilneFT]). -/
theorem denseGaloisFixedElement [IsGalois K L] {S : Set (L ≃ₐ[K] L)} (hS : Dense S) {x : L}
    (hx : ∀ σ ∈ S, σ x = x) : x ∈ Set.range (algebraMap K L) := by
  have hclosed : IsClosed (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) :=
    (MulAction.stabilizer (L ≃ₐ[K] L) x).isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral x)
  refine (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr fun σ => ?_
  have h1 : σ ∈ (MulAction.stabilizer (L ≃ₐ[K] L) x : Set (L ≃ₐ[K] L)) := by
    rw [← hclosed.closure_eq]
    exact closure_mono (fun τ hτ => hx τ hτ) (hS.closure_eq ▸ Set.mem_univ σ)
  exact h1

end Atlas.Knowledge
