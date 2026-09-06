import Mathlib
import Atlas.Knowledge.AbstractFixedField
import Atlas.Knowledge.FiniteAbelianSubextension
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.GaloisExtensionQuotient
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.NormSubgroupOrderEmbedding
import Atlas.Knowledge.ResidueDatumIn
import Atlas.Knowledge.SeparableFixedFieldNorm

/-!
# order reversal for finite abelian subfields

The inclusion-reversing correspondence between finite abelian subfields of the algebraic
closure of a mixed-characteristic local field and their norm subgroups, stated concretely:
`E₁ ≤ E₂` iff `N_{E₂/K} (E₂ˣ) ≤ N_{E₁/K} (E₁ˣ)`. This is the layer's classification of
`Atlas.Knowledge.NormSubgroupOrderEmbedding` read on intermediate fields rather than on the
abstract subextensions it is stated for, and it is how a containment of fields is proved from
a containment of norm groups — the level fields of the Lubin–Tate tower nest this way, and an
arbitrary abelian floor sits inside a standard compositum this way.

## Main definitions

* `toFiniteAbelianSubextension` — a finite abelian intermediate field as an abstract finite
  abelian subextension of the absolute base.

## Main statements

* `finiteAbelianNormSubgroup_toFiniteAbelianSubextension` — its abstract norm subgroup is
  the ordinary one.
* `finiteAbelian_le_iff_localNormSubgroup_le` — the order reversal.

## Implementation notes

The packaging takes the closed fixing subgroup of the field, over the fixing subgroup of the
bottom field, with normality the instance of `Atlas.Knowledge.GaloisExtensionQuotient` and
finiteness the instance of `Atlas.Knowledge.SeparableFixedFieldNorm` — that file is imported
for the instance alone — and with commutativity transported from the Galois group along
`Atlas.Knowledge.baseFixingExtensionQuotientEquivGaloisGroup`. Its fixed field is the field
again by `InfiniteGalois.fixedField_fixingSubgroup`, which is what identifies the abstract
norm subgroup with `Atlas.Knowledge.localNormSubgroup`. The order on the abstract side is the
reversed containment of fixing subgroups, and the Galois correspondence of the closure turns
that back into containment of fields.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
-/

open ValuativeRel

namespace Atlas.Knowledge

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- A finite abelian subfield of the algebraic closure as an abstract finite abelian
subextension of the absolute base: its closed fixing subgroup, with commutativity carried
over from its Galois group. -/
noncomputable def toFiniteAbelianSubextension (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    FiniteAbelianSubextension
      (closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K))) where
  toFiniteGaloisExtension :=
    { field := closedFixingSubgroup E
      below := fixingSubgroupLeBase K (AlgebraicClosure K) E
      normal := inferInstance
      finite := inferInstance }
  commutative := by
    change IsMulCommutative
      ((closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K))).toSubgroup ⧸
        (closedFixingSubgroup E).toSubgroup.subgroupOf
          (closedFixingSubgroup (⊥ : IntermediateField K (AlgebraicClosure K))).toSubgroup)
    let e := baseFixingExtensionQuotientEquivGaloisGroup K (AlgebraicClosure K) E
    exact
      { is_comm.comm := fun x y => by
          apply e.injective
          rw [map_mul, map_mul]
          exact IsMulCommutative.is_comm.comm _ _ }

/-- The packaged subextension's subgroup is the field's closed fixing subgroup. -/
theorem toFiniteAbelianSubextension_field (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    (toFiniteAbelianSubextension K E).field = closedFixingSubgroup E :=
  rfl

/-- The abstract norm subgroup of the packaged subextension is the ordinary norm subgroup of
the field: the fixed field of its fixing subgroup is the field again. -/
theorem finiteAbelianNormSubgroup_toFiniteAbelianSubextension
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    [IsAbelianGalois K E] :
    finiteAbelianNormSubgroup K (AlgebraicClosure K) (toFiniteAbelianSubextension K E) =
      localNormSubgroup K E := by
  change localNormSubgroup K
      (abstractFixedField K (AlgebraicClosure K) (closedFixingSubgroup E)) =
    localNormSubgroup K E
  have h : abstractFixedField K (AlgebraicClosure K) (closedFixingSubgroup E) = E :=
    InfiniteGalois.fixedField_fixingSubgroup E
  rw [h]

/-- **The order reversal for finite abelian subfields of the algebraic closure**: `E₁ ≤ E₂`
iff the norm subgroup of `E₂` lies in that of `E₁`
([Milne 2020, Chap. I, §1, Cor. 1.2 (b), p.20][MilneCFT]). -/
theorem finiteAbelian_le_iff_localNormSubgroup_le
    (E₁ E₂ : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E₁] [IsAbelianGalois K E₁]
    [FiniteDimensional K E₂] [IsAbelianGalois K E₂] :
    E₁ ≤ E₂ ↔ localNormSubgroup K E₂ ≤ localNormSubgroup K E₁ := by
  have h := localFiniteAbelianSubextension_le_iff_normSubgroup_le K
    (toFiniteAbelianSubextension K E₁) (toFiniteAbelianSubextension K E₂)
  rw [finiteAbelianNormSubgroup_toFiniteAbelianSubextension,
    finiteAbelianNormSubgroup_toFiniteAbelianSubextension, FiniteAbelianSubextension.le_iff] at h
  rw [← h]
  change E₁ ≤ E₂ ↔ E₂.fixingSubgroup ≤ E₁.fixingSubgroup
  constructor
  · exact fun h12 => IntermediateField.fixingSubgroup_le h12
  · intro h12 x hx
    have hx' : x ∈ IntermediateField.fixedField E₂.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      exact (IntermediateField.mem_fixingSubgroup_iff E₁ σ).1 (h12 hσ) x hx
    rwa [InfiniteGalois.fixedField_fixingSubgroup] at hx'

end Atlas.Knowledge
