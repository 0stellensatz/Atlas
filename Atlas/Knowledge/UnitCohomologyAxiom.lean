import Mathlib
import Atlas.Knowledge.UnitRepresentation

/-!
# unit-cohomology axiom

The reciprocity construction's second axiom on a valuation datum, in the
layer's elementary form: for every finite unramified cyclic extension
`L | K`, every unit of `K` is the relative norm of a unit of `L`, and every
unit of `L` killed by the representation norm is a `σ − 1` difference under
the generator. These are the elementwise contents of the source's
`H⁰(G(L|K), U_L) = 0` and `H⁻¹(G(L|K), U_L) = 0`, taken here as the axiom
itself (#104).

## Main definitions

* `ValuationData.SatisfiesUnramifiedUnitCohomology` — the two vanishing
  statements, elementwise.

## Implementation notes

The source states the axiom through the vanishing of two Tate-cohomology
objects and converts each into its elementwise consequence with an
eliminator (`UnitCohomologyAxiom.lean:417` and `:462`); every site that
uses the axiom's content destructures it and feeds an eliminator, always at
the bundle's own generator, while the rest thread the hypothesis. The layer
takes the eliminators' conclusions as the definition, so those sites
project directly and the Tate comparison — which keeps the acting group in
one universe with the coefficients — is not needed here; the generic `Ĥ⁰`
comparison at `:167` keeps an unrelated consumer and travels to that brick.
The source's one producer, the derivation from the class-field axiom at
`Reciprocity/Core.lean:413`, is the derivation
`Atlas.Knowledge.SatisfiesClassFieldAxiom`'s notes already replace by a
direct local discharge. This is the same reduction that axiom performs.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {A : Rep ℤ G}

/-- **The unit-cohomology axiom, elementwise**: for every finite unramified
cyclic extension `L | K`, every unit of `K` is a relative norm from `L`,
and every unit of `L` of representation norm zero is a `σ − 1` difference —
the elementwise contents of `H⁰(G(L|K), U_L) = 0` and
`H⁻¹(G(L|K), U_L) = 0`. A predicate on the abstract valuation datum, not a
Lean axiom ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:491`]
[Yamaguchi2026]). -/
def ValuationData.SatisfiesUnramifiedUnitCohomology
    (D : DegreeData G) (v : ValuationData D A) : Prop :=
  ∀ (K : FiniteAbstractField G)
    (E : FiniteUnramifiedCyclicExtension D K),
    (∀ u : v.unitAddSubgroup K,
        ∃ ε : v.unitAddSubgroup E.toFiniteAbstractFieldExtension.field,
          relativeNorm A K.field E.field E.below ε.1 = u.1) ∧
    (∀ u : (E.unitRepresentation v).V,
        (E.unitRepresentation v).norm.hom u = 0 →
          ∃ ε : (E.unitRepresentation v).V,
            (E.unitRepresentation v).ρ E.generator ε - ε = u)

end

end Atlas.Knowledge
