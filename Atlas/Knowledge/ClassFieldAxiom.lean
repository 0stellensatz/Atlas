import Mathlib
import Atlas.Knowledge.ExtensionFixedRepresentationEquiv
import Atlas.Knowledge.FiniteCyclicSubextension
import Atlas.Knowledge.FiniteNormQuotient

/-!
# class-field axiom

The reciprocity engine's third input: for every finite cyclic extension
`L | K` of a finite abstract field, the norm quotient `A_K / N_{L|K} A_L` is
finite of cardinality exactly the degree, and every element of `A_L` whose
norm vanishes is a `σ − 1`-difference for the chosen generator. These are the
classical `#Ĥ⁰ = [L:K]` and `Ĥ⁻¹ = 1`, stated on the norm quotient and on
representatives rather than through Tate cohomology, together with the
consequence lemmas the reciprocity construction consumes (#104).

## Main definitions

* `ClassFieldAxiomData` / `SatisfiesClassFieldAxiom` — the axiom at one
  cyclic extension, and its quantification.

## Main statements

* `finiteNormQuotient_card_of_classFieldAxiom` — the norm quotient has the
  degree as cardinality; proved from the axiom.
* `abstractReciprocity_exists_hMinusOne_primitive` — a vanishing norm is a
  `σ − 1`-difference; proved from the axiom.

## Implementation notes

The source states the axiom through Mathlib's Tate cohomology of the
descended representation and recovers the two facts above by the cyclic
comparison equivalences; the reciprocity construction consumes the axiom
exclusively through those facts. The layer states them directly: the
cohomological and the elementary forms carry the same content for a cyclic
extension — `Ĥ⁰` is the norm quotient and `Ĥ⁻¹` vanishes exactly when norm
kernels are `σ − 1`-differences, which is the comparison recorded in
`Atlas.Knowledge.TateCohomologyFiniteCyclic` — and the elementary form is
what the layer's local instances (`Atlas.Knowledge.normIndexCyclic`,
`Atlas.Knowledge.GalUnits`) prove. It also keeps the acting group
universe-polymorphic, where Mathlib's `tateCohomology` would pin it to
`Type 0` against the layer's `Type*` carrier. The consequence lemmas keep
the source's names and signatures, so their consumers port unchanged; here
they are projections.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The class-field axiom at one finite cyclic extension**: the norm
quotient is finite of cardinality the degree, and a vanishing norm is a
`σ − 1`-difference ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean:30`]
[Yamaguchi2026]). -/
structure ClassFieldAxiomData (A : Rep ℤ G) (K : FiniteAbstractField G)
    (E : FiniteCyclicSubextension K) : Prop where
  /-- The finite norm quotient is finite. -/
  finiteNormQuotient : Finite (FiniteNormQuotient A K.field E.field E.below)
  /-- The finite norm quotient has cardinality the extension degree. -/
  card_finiteNormQuotient :
    Nat.card (FiniteNormQuotient A K.field E.field E.below) =
      (E.toFiniteAbstractExtension.degree : ℕ)
  /-- A representative whose relative norm vanishes against another is a
  `σ − 1`-difference for the chosen generator. -/
  exists_primitive : ∀ u w : ambientFixedAddSubgroup A E.field,
    relativeNorm A K.field E.field E.below w =
      relativeNorm A K.field E.field E.below u →
    ∃ a : (extensionFixedRepresentation A K.field E.field E.below
        E.normal).V,
      (extensionFixedRepresentation A K.field E.field E.below
          E.normal).ρ E.generator a - a =
        (extensionFixedRepresentationEquiv A K.field E.field E.below
          E.normal).symm (w - u)

/-- **The class-field axiom**: the data above at every finite cyclic
extension of every finite abstract field ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean:52`]
[Yamaguchi2026]). -/
def SatisfiesClassFieldAxiom (A : Rep ℤ G) : Prop :=
  ∀ (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K),
    ClassFieldAxiomData A K E

/-- **The norm quotient of a cyclic extension is finite** under the axiom
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean:585`]
[Yamaguchi2026]). -/
theorem finiteNormQuotient_finite_of_classFieldAxiom
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractExtension G)
    [hKfinite : Finite ((baseField G).toSubgroup ⧸
      E.base.toSubgroup.subgroupOf (baseField G).toSubgroup)]
    (hnormal : (E.field.toSubgroup.subgroupOf E.base.toSubgroup).Normal)
    (g : E.base.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf E.base.toSubgroup)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Finite (FiniteNormQuotient A E.base E.field E.below) :=
  (hcf ⟨E.base, hKfinite⟩
    { field := E.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }).finiteNormQuotient

/-- **The norm quotient of a cyclic extension has the degree as its order**
under the axiom ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean:490`]
[Yamaguchi2026]). -/
theorem finiteNormQuotient_card_of_classFieldAxiom
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractExtension G)
    [hKfinite : Finite ((baseField G).toSubgroup ⧸
      E.base.toSubgroup.subgroupOf (baseField G).toSubgroup)]
    (hnormal : (E.field.toSubgroup.subgroupOf E.base.toSubgroup).Normal)
    (g : E.base.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf E.base.toSubgroup)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card (FiniteNormQuotient A E.base E.field E.below) =
      (E.degree : ℕ) :=
  (hcf ⟨E.base, hKfinite⟩
    { field := E.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }).card_finiteNormQuotient

/-- **The additive Galois quotient has the degree as its order**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean:546`]
[Yamaguchi2026]). -/
theorem additiveExtensionQuotient_card
    (E : FiniteAbstractExtension G) :
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            E.field.toSubgroup.subgroupOf E.base.toSubgroup)) =
      (E.degree : ℕ) := by
  calc
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            E.field.toSubgroup.subgroupOf E.base.toSubgroup)) =
        Nat.card
          (E.base.toSubgroup ⧸
            E.field.toSubgroup.subgroupOf E.base.toSubgroup) :=
      (Nat.card_congr
        (Additive.ofMul :
          (E.base.toSubgroup ⧸
              E.field.toSubgroup.subgroupOf E.base.toSubgroup) ≃
            Additive
              (E.base.toSubgroup ⧸
                E.field.toSubgroup.subgroupOf E.base.toSubgroup))).symm
    _ = (E.field.toSubgroup.subgroupOf E.base.toSubgroup).index :=
      (Subgroup.index_eq_card
        (E.field.toSubgroup.subgroupOf E.base.toSubgroup)).symm
    _ = (E.degree : ℕ) := E.subgroup_index_eq_degree

/-- **The cyclic Galois quotient and the norm quotient have the same order**
under the axiom ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean:566`]
[Yamaguchi2026]). -/
theorem cyclicReciprocity_card_equality
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractExtension G)
    [Finite ((baseField G).toSubgroup ⧸
      E.base.toSubgroup.subgroupOf (baseField G).toSubgroup)]
    (hnormal : (E.field.toSubgroup.subgroupOf E.base.toSubgroup).Normal)
    (g : E.base.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf E.base.toSubgroup)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    Nat.card
        (Additive
          (E.base.toSubgroup ⧸
            E.field.toSubgroup.subgroupOf E.base.toSubgroup)) =
      Nat.card (FiniteNormQuotient A E.base E.field E.below) := by
  rw [additiveExtensionQuotient_card E,
    finiteNormQuotient_card_of_classFieldAxiom
      A hcf E hnormal g hg]

/-- **A vanishing norm is a `σ − 1`-difference**, in representative form
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean:230`]
[Yamaguchi2026]). -/
theorem abstractReciprocity_exists_hMinusOne_primitive
    {A : Rep ℤ G}
    (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (E.field.field.toSubgroup.subgroupOf
      E.base.field.toSubgroup).Normal)
    (g : E.base.field.toSubgroup ⧸
      E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (u w : ambientFixedAddSubgroup A E.field.field)
    (hnorm : relativeNorm A E.base.field E.field.field E.below w =
      relativeNorm A E.base.field E.field.field E.below u) :
    let M := extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal
    ∃ a : M.V,
      M.ρ g a - a =
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal).symm
          (w - u) :=
  (hcf E.base
    { field := E.field.field
      below := E.below
      normal := hnormal
      finite := E.finiteQuotient
      generator := g
      generates := hg }).exists_primitive u w hnorm

end

end Atlas.Knowledge
