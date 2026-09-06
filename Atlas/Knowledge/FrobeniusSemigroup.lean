import Mathlib
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent

/-!
# Frobenius semigroup

The Frobenius elements of `Frob(L̃|K)` are closed under multiplication:
their normalized degrees are positive natural powers of the generator, and
exponents add under products. The induced multiplication is associative, so
the reciprocity construction can multiply its chosen lifts freely (#104).

## Main definitions

* `DegreeData.frobeniusMul` — the product of two Frobenius elements, with
  the summed exponent witness.
* `DegreeData.frobeniusElementsSemigroup` — the induced semigroup
  structure, an instance.

## Main statements

* `DegreeData.extensionNormalizedDegree_frobenius_mul` — the normalized
  degree is multiplicative on the semigroup; proved.

## Implementation notes

The simp attribute the source puts on the multiplicativity law is dropped:
`frobeniusMul_coe` and `map_mul` are already simp, so simp proves the law
outright and the attribute could never contribute.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The product of two Frobenius elements**: exponents add
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean:21`). -/
def frobeniusMul (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    D.FrobeniusElements K L hLK := by
  let m := D.frobeniusExponent K L hLK σ
  let n := D.frobeniusExponent K L hLK τ
  refine ⟨σ.1 * τ.1, m + n,
    Nat.add_pos_left (D.frobeniusExponent_pos K L hLK σ) n, ?_⟩
  rw [map_mul,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK τ,
    pow_add]

/-- Multiplication of Frobenius elements is induced by multiplication of
their quotient representatives (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean:40`). -/
instance frobeniusElementsMul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    Mul (D.FrobeniusElements K L hLK) :=
  ⟨D.frobeniusMul K L hLK⟩

/-- The product's representative is the product of representatives. -/
@[simp]
theorem frobeniusMul_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    (σ * τ).1 = σ.1 * τ.1 :=
  rfl

/-- **The Frobenius elements form a semigroup** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean:60`). -/
instance frobeniusElementsSemigroup (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    Semigroup (D.FrobeniusElements K L hLK) where
  mul_assoc σ τ υ := by
    apply Subtype.ext
    change (σ.1 * τ.1) * υ.1 = σ.1 * (τ.1 * υ.1)
    exact mul_assoc σ.1 τ.1 υ.1

/-- **The normalized degree is multiplicative on the Frobenius semigroup**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusSemigroup.lean:77`). -/
theorem extensionNormalizedDegree_frobenius_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    D.extensionNormalizedDegree K L hLK (σ * τ).1 =
      D.extensionNormalizedDegree K L hLK σ.1 *
        D.extensionNormalizedDegree K L hLK τ.1 :=
  map_mul _ _ _

end DegreeData

end

end Atlas.Knowledge
