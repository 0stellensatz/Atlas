import Mathlib
import Atlas.Knowledge.FixingSubgroupAdjoinSimple

/-!
# dense Galois fixed element

An element of a Galois extension fixed by a dense set of automorphisms lies in the base
field. This is the infinite Galois correspondence read at one element: the automorphisms
fixing `x` form the fixing subgroup of `K⟮x⟯`, closed in the Krull topology because `K⟮x⟯` is
finite over `K`, so a dense set of them is all of them, and the fixed field of the whole
group is the base. It is the form in which the dense range of a reciprocity map reaches an
element: in `Atlas.Knowledge.LocalHilbertSymbolNondegeneracy` a root killed against every
lift of every value of the map is fixed by a dense set of automorphisms, hence rational,
which is the left kernel of the Hilbert symbol.

## Main statements

* `denseGaloisFixedElement` — an element fixed by a dense set of automorphisms lies in the
  base field; proved.

## Implementation notes

The set `S` is an arbitrary dense set of automorphisms, not a subgroup: density and the
pointwise condition are all the argument consumes. Closedness comes from
`IntermediateField.fixingSubgroup_isClosed` through
`Atlas.Knowledge.fixingSubgroupAdjoinSimple`, finite-dimensionality of `K⟮x⟯` from
integrality, which `IsGalois` supplies, and the last step is Mathlib's
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
field: the fixing subgroup of `K⟮x⟯` is closed and contains the dense set, so it is the whole
group, and the fixed field of the whole Galois group is the base
([Milne 2022, Chap. 7, Prop. 7.9 and Prop. 7.12 (b), p.97][MilneFT]). -/
theorem denseGaloisFixedElement [IsGalois K L] {S : Set (L ≃ₐ[K] L)} (hS : Dense S) {x : L}
    (hx : ∀ σ ∈ S, σ x = x) : x ∈ Set.range (algebraMap K L) := by
  haveI : FiniteDimensional K (IntermediateField.adjoin K {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have hsub : S ⊆ ((IntermediateField.adjoin K {x}).fixingSubgroup : Set (L ≃ₐ[K] L)) := by
    intro σ hσ
    rw [SetLike.mem_coe, fixingSubgroupAdjoinSimple, MulAction.mem_stabilizer_iff,
      AlgEquiv.smul_def]
    exact hx σ hσ
  have hall : ∀ σ : L ≃ₐ[K] L, σ x = x := by
    intro σ
    have h1 : σ ∈ ((IntermediateField.adjoin K {x}).fixingSubgroup : Set (L ≃ₐ[K] L)) := by
      rw [← (IntermediateField.fixingSubgroup_isClosed _).closure_eq]
      exact closure_mono hsub (hS.closure_eq ▸ Set.mem_univ σ)
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp h1 x
      (IntermediateField.mem_adjoin_simple_self K x)
  exact (InfiniteGalois.mem_range_algebraMap_iff_fixed x).mpr hall

end Atlas.Knowledge
