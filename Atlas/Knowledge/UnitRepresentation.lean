import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteTower
import Atlas.Knowledge.FiniteUnramifiedCyclicExtension
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.ValuationData

/-!
# unit representation

The Galois action on the actual unit group `U_L`: the normalized valuation
is invariant under the normal-extension action, so `G_K` acts on the units
of `L`, the action is trivial on `G_L`, and it descends to a representation
of the finite quotient `G(L|K)` — the coefficient representation of the
unit-cohomology axiom. On underlying coefficients the descended action is
the relative coset action and the representation norm is the relative field
norm, and along an unramified extension the units of `K` include into the
units of `L` (#104).

## Main definitions

* `ValuationData.unitRepresentation` — the `G(L|K)`-representation on
  `U_L`.
* `ValuationData.unitInclusion` — unit inclusion along an unramified
  extension.
* `FiniteUnramifiedCyclicExtension.unitRepresentation` — the coefficient
  representation of a bundled extension.

## Main statements

* `ValuationData.valuationAt_normalExtensionAction` — the normalized
  valuation is Galois-invariant; proved.
* `ValuationData.unitRepresentation_action_coe` /
  `ValuationData.unitRepresentation_norm_coe` — the descended action is
  the coset action and the representation norm is the relative norm, on
  coefficients; proved.

## Implementation notes

The descent through the extension subgroup is Mathlib's `Rep.ofQuotient`,
exactly as in the source, with the triviality instance supplied the same
way. Positivity arguments become the layer's `≠ 0` spellings, as across the
arc.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- **The normalized valuation is invariant under the Galois action in a
finite tower**, by transitivity of the norm and its invariance under the
normal-extension action (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:191`). -/
theorem valuationAt_normalExtensionAction
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal :
      (E.field.field.toSubgroup.subgroupOf
        E.base.field.toSubgroup).Normal)
    (k : E.base.field.toSubgroup)
    (a : ambientFixedAddSubgroup A E.field.field) :
    v.valuationAt E.field
        (normalExtensionAction A E.base.field E.field.field E.below
          hnormal k a) =
      v.valuationAt E.field a := by
  apply Subtype.ext
  apply ProfiniteInteger.nsmul_left_injective
    (E.field.residueDegree D).pos.ne'
  calc
    (E.field.residueDegree D : ℕ) •
        ((v.valuationAt E.field
          (normalExtensionAction A E.base.field E.field.field E.below
            hnormal k a) : v.valueGroup) : ProfiniteInteger) =
      v.normCompositeAt E.field
        (normalExtensionAction A E.base.field E.field.field E.below
          hnormal k a) :=
        v.residueDegree_nsmul_dividedAt E.field _
    _ = v.normCompositeAt E.field a := by
      change v.toAddMonoidHom
          (normToBase A E.field.field
            (normalExtensionAction A E.base.field E.field.field E.below
              hnormal k a)) =
        v.toAddMonoidHom (normToBase A E.field.field a)
      congr 1
      let T : FiniteTower G := {
        top := E.field.field
        middle := E.base.field
        base := baseField G
        top_le_middle := E.below
        middle_le_base := le_baseField E.base.field
        finiteTopQuotient := E.finiteQuotient
        finiteBaseQuotient := E.base.finite }
      calc
        relativeNorm A (baseField G) E.field.field
            (E.below.trans (le_baseField E.base.field))
            (normalExtensionAction A E.base.field E.field.field E.below
              hnormal k a) =
          relativeNorm A (baseField G) E.base.field
            (le_baseField E.base.field)
            (relativeNorm A E.base.field E.field.field E.below
              (normalExtensionAction A E.base.field E.field.field E.below
                hnormal k a)) :=
          (T.norm_trans_apply A _).symm
        _ = relativeNorm A (baseField G) E.base.field
            (le_baseField E.base.field)
            (relativeNorm A E.base.field E.field.field E.below a) := by
          rw [relativeNorm_normalExtensionAction A E.base.field
            E.field.field E.below hnormal k a]
        _ = relativeNorm A (baseField G) E.field.field
            (E.below.trans (le_baseField E.base.field)) a :=
          T.norm_trans_apply A a
    _ = (E.field.residueDegree D : ℕ) •
        ((v.valuationAt E.field a : v.valueGroup) : ProfiniteInteger) :=
      (v.residueDegree_nsmul_dividedAt E.field a).symm

/-- The action of `G_K` on the actual unit subgroup `U_L`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:250`). -/
noncomputable def unitActionLinearMap
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal :
      (E.field.field.toSubgroup.subgroupOf
        E.base.field.toSubgroup).Normal)
    (k : E.base.field.toSubgroup) :
    v.unitAddSubgroup E.field →ₗ[ℤ] v.unitAddSubgroup E.field where
  toFun u := ⟨normalExtensionAction A E.base.field E.field.field E.below
      hnormal k u.1, by
    rw [mem_unitAddSubgroup_iff,
      v.valuationAt_normalExtensionAction E hnormal k u.1]
    exact u.2⟩
  map_add' u w := by
    apply Subtype.ext
    apply Subtype.ext
    change A.ρ k.1 (u.1.1 + w.1.1) = A.ρ k.1 u.1.1 + A.ρ k.1 w.1.1
    exact map_add (A.ρ k.1) _ _
  map_smul' n u := by
    apply Subtype.ext
    apply Subtype.ext
    change A.ρ k.1 (n • u.1.1) = n • A.ρ k.1 u.1.1
    exact map_zsmul (A.ρ k.1) n u.1.1

/-- The `G_K`-representation on `U_L`, before descending through `G_L`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:272`). -/
noncomputable def unitRepresentationOverK
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal :
      (E.field.field.toSubgroup.subgroupOf
        E.base.field.toSubgroup).Normal) :
    Rep ℤ E.base.field.toSubgroup :=
  Rep.of
    { toFun := fun k => v.unitActionLinearMap E hnormal k
      map_one' := by
        ext u
        change A.ρ (1 : G) u.1.1 = u.1.1
        simp
      map_mul' := by
        intro k₁ k₂
        ext u
        change A.ρ (k₁.1 * k₂.1) u.1.1 =
          A.ρ k₁.1 (A.ρ k₂.1 u.1.1)
        rw [map_mul]
        rfl }

/- The pre-descent representation is trivial on the extension subgroup
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:290`). -/
private theorem unitRepresentationOverK_isTrivialOnExtension
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal :
      (E.field.field.toSubgroup.subgroupOf
        E.base.field.toSubgroup).Normal) :
    Representation.IsTrivial
      ((v.unitRepresentationOverK E hnormal).ρ.comp
        (E.field.field.toSubgroup.subgroupOf
          E.base.field.toSubgroup).subtype) := by
  constructor
  intro s
  ext u
  apply Subtype.ext
  apply Subtype.ext
  change A.ρ s.1.1 u.1.1 = u.1.1
  exact u.1.2 ⟨s.1.1, Subgroup.mem_subgroupOf.1 s.2⟩

/-- **The `G(L|K)`-representation on the actual unit group `U_L`**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:306`). -/
noncomputable def unitRepresentation
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal :
      (E.field.field.toSubgroup.subgroupOf
        E.base.field.toSubgroup).Normal) :
    Rep ℤ (E.base.field.toSubgroup ⧸
      E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup) := by
  letI : Representation.IsTrivial
      ((v.unitRepresentationOverK E hnormal).ρ.comp
        (E.field.field.toSubgroup.subgroupOf
          E.base.field.toSubgroup).subtype) :=
    v.unitRepresentationOverK_isTrivialOnExtension E hnormal
  exact (v.unitRepresentationOverK E hnormal).ofQuotient
    (E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)

end ValuationData

namespace FiniteUnramifiedCyclicExtension

variable {K : FiniteAbstractField G}

/-- The unit representation carried by a bundled finite unramified cyclic
extension (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:327`). -/
noncomputable def unitRepresentation
    (E : FiniteUnramifiedCyclicExtension D K) (v : ValuationData D A) :
    Rep ℤ (K.field.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
  v.unitRepresentation E.toFiniteAbstractFieldExtension E.normal

end FiniteUnramifiedCyclicExtension

namespace ValuationData

/-- The quotient action computes on a representative through the original
unit action (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:338`). -/
@[simp]
theorem unitRepresentation_quotient_mk_apply
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal :
      (E.field.field.toSubgroup.subgroupOf
        E.base.field.toSubgroup).Normal)
    (k : E.base.field.toSubgroup) (u : v.unitAddSubgroup E.field) :
    (v.unitRepresentation E hnormal).ρ
        (k : E.base.field.toSubgroup ⧸
          E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup) u =
      v.unitActionLinearMap E hnormal k u :=
  rfl

/-- **Inclusion of units along an unramified finite extension**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:349`). -/
def unitInclusion
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hUnramified : E.IsUnramified D) :
    v.unitAddSubgroup E.base →+ v.unitAddSubgroup E.field where
  toFun u := ⟨fixedFieldInclusion A E.base.field E.field.field
      E.below u.1, by
    rw [mem_unitAddSubgroup_iff]
    exact (v.valuationAt_fixedFieldInclusion_of_unramified E
      hUnramified u.1).trans u.2⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl

/-- **On coefficients, the descended action on `U_L` is the relative coset
action** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:366`). -/
theorem unitRepresentation_action_coe
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal :
      (E.field.field.toSubgroup.subgroupOf
        E.base.field.toSubgroup).Normal)
    (q : E.base.field.toSubgroup ⧸
      E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
    (u : v.unitAddSubgroup E.field) :
    (((v.unitRepresentation E hnormal).ρ q u).1 :
        ambientFixedAddSubgroup A E.field.field).1 =
      relativeCosetAction A E.base.field E.field.field E.below u.1 q := by
  refine Quotient.inductionOn' q ?_
  intro k
  rw [relativeCosetAction_mk]
  rfl

/-- **The representation norm on `U_L` is the relative field norm on
coefficients** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UnitCohomologyAxiom.lean:382`). -/
theorem unitRepresentation_norm_coe
    (v : ValuationData D A) (E : FiniteAbstractFieldExtension G)
    (hnormal :
      (E.field.field.toSubgroup.subgroupOf
        E.base.field.toSubgroup).Normal)
    (u : v.unitAddSubgroup E.field) :
    letI := Fintype.ofFinite
      (E.base.field.toSubgroup ⧸
        E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
    ((((v.unitRepresentation E hnormal).norm.hom u).1 :
        ambientFixedAddSubgroup A E.field.field) : A.V) =
      ((relativeNorm A E.base.field E.field.field E.below u.1 :
        ambientFixedAddSubgroup A E.base.field) : A.V) := by
  letI := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
  rw [relativeNorm_apply_coe]
  change
    (((Representation.norm (v.unitRepresentation E hnormal).ρ) u).1 :
      ambientFixedAddSubgroup A E.field.field).1 =
      relativeNormValue A E.base.field E.field.field E.below u.1
  rw [Representation.norm, relativeNormValue]
  simp only [LinearMap.sum_apply]
  let coeToAmbient : v.unitAddSubgroup E.field →+ A.V :=
    (ambientFixedAddSubgroup A E.field.field).subtype.comp
      (v.unitAddSubgroup E.field).subtype
  change coeToAmbient
      (∑ q, (v.unitRepresentation E hnormal).ρ q u) =
    ∑ q, relativeCosetAction A E.base.field E.field.field E.below u.1 q
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  simpa [coeToAmbient] using
    v.unitRepresentation_action_coe E hnormal q u

end ValuationData

end

end Atlas.Knowledge
