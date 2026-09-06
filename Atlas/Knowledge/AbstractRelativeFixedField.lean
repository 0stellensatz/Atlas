import Mathlib
import Atlas.Knowledge.AbstractFixedField
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteExtensionTransitivity

/-!
# relative fixed fields of abstract extensions

The tower dictionary of the reciprocity engine: for closed subgroups
`L ≤ K`, the upper fixed field over the lower one, its fixing subgroup as
the image of the engine's relative subgroup, normality and the Galois
property transported from the engine's normality witness, the identification
of the engine's relative quotient with the concrete Galois group, and the
equality of the abstract degree with the concrete field degree. This is what
turns the engine's class-field-axiom inputs into statements about actual
finite Galois extensions (#104).

## Main definitions

* `abstractRelativeFixedField` — the upper fixed field over the lower.
* `abstractExtensionQuotientEquivGaloisGroup` — the engine's relative
  quotient is the concrete Galois group.

## Main statements

* `map_extensionSubgroup_abstractSubgroupEquiv` — the relative subgroup maps
  onto the fixing subgroup of the upper field; proved.
* `abstractRelativeFixedField_isGalois` — the engine's normality witness
  makes the concrete extension Galois; proved.
* `finiteAbstractExtension_degree_eq_finrank` — the abstract degree is the
  concrete degree; proved.

## Implementation notes

The engine's relative subgroup is spelled `Subgroup.subgroupOf` as across
the layer — the source's `extensionSubgroup` is an abbreviation of it, its
membership lemma is Mathlib's `Subgroup.mem_subgroupOf`, and the source
names are kept even where they mention that spelling. The tower finiteness
input rides `Atlas.Knowledge.finite_extension_trans`, and the
bundled-extension degree comparison closes with
`Atlas.Knowledge.FiniteAbstractExtension.subgroup_index_eq_degree`, the
layer's name for the source's `extensionSubgroup_index_eq_degree`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable (k : Type u) (Ω : Type v) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω]

/-- **The upper fixed field over the lower** in a relative abstract extension
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:110`). -/
abbrev abstractRelativeFixedField
    {K L : ClosedSubgroup (Ω ≃ₐ[k] Ω)}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    IntermediateField (abstractFixedField k Ω K) Ω :=
  IntermediateField.extendScalars (abstractFixedField_le k Ω hLK)

/-- **The engine's relative subgroup maps onto the fixing subgroup of the
upper field** under the Galois-group reading of the lower subgroup
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:118`). -/
theorem map_extensionSubgroup_abstractSubgroupEquiv
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (L.toSubgroup.subgroupOf K.toSubgroup).map
        (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom =
      (abstractRelativeFixedField k Ω hLK).fixingSubgroup := by
  ext τ
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    have hσL : (σ.1 : Ω ≃ₐ[k] Ω) ∈ L :=
      Subgroup.mem_subgroupOf.1 hσ
    have hfix : ∀ y ∈ abstractFixedField k Ω L, σ.1 y = y := by
      have hσfix : σ.1 ∈ (abstractFixedField k Ω L).fixingSubgroup := by
        rw [InfiniteGalois.fixingSubgroup_fixedField L]
        exact hσL
      exact (IntermediateField.mem_fixingSubgroup_iff
        (abstractFixedField k Ω L) σ.1).1 hσfix
    exact hfix x hx
  · intro hτ
    let σ : K.toSubgroup :=
      (abstractSubgroupEquivGaloisGroup k Ω K).symm τ
    refine ⟨σ, ?_, (abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply τ⟩
    apply Subgroup.mem_subgroupOf.2
    have hσfix : (σ.1 : Ω ≃ₐ[k] Ω) ∈
        (abstractFixedField k Ω L).fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro x hx
      have hτfix := (IntermediateField.mem_fixingSubgroup_iff
        (abstractRelativeFixedField k Ω hLK) τ).1 hτ x hx
      calc
        σ.1 x = abstractSubgroupEquivGaloisGroup k Ω K σ x :=
          (abstractSubgroupEquivGaloisGroup_apply k Ω K σ x).symm
        _ = τ x := by
          rw [show abstractSubgroupEquivGaloisGroup k Ω K σ = τ by
            exact (abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply τ]
        _ = x := hτfix
    rw [InfiniteGalois.fixingSubgroup_fixedField L] at hσfix
    exact hσfix

/-- **The engine's normality witness is normality of the upper fixing
subgroup** (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:161`). -/
theorem abstractRelativeFixingSubgroup_normal
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal := by
  have hmap : ((L.toSubgroup.subgroupOf K.toSubgroup).map
      (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom).Normal :=
    hnormal.map (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom
      (abstractSubgroupEquivGaloisGroup k Ω K).surjective
  rw [map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK] at hmap
  exact hmap

/-- **The engine's normality witness makes the concrete extension Galois**
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:175`). -/
theorem abstractRelativeFixedField_isGalois
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    IsGalois (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) := by
  apply (InfiniteGalois.normal_iff_isGalois
    (abstractRelativeFixedField k Ω hLK)).1
  exact abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal

/-- Restriction through the lower fixed field, followed by quotienting by
the upper fixing subgroup (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:187`). -/
def abstractRelativeToAmbientQuotient
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    K.toSubgroup →*
      (Ω ≃ₐ[abstractFixedField k Ω K] Ω) ⧸
        (abstractRelativeFixedField k Ω hLK).fixingSubgroup := by
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  exact (QuotientGroup.mk'
    (abstractRelativeFixedField k Ω hLK).fixingSubgroup).comp
      (abstractSubgroupEquivGaloisGroup k Ω K).toMonoidHom

/-- The kernel of the ambient quotient map is the engine's relative subgroup
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:203`). -/
theorem abstractRelativeToAmbientQuotient_ker
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal).ker =
      L.toSubgroup.subgroupOf K.toSubgroup := by
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  ext σ
  change
    QuotientGroup.mk' (abstractRelativeFixedField k Ω hLK).fixingSubgroup
        (abstractSubgroupEquivGaloisGroup k Ω K σ) = 1 ↔
      σ ∈ L.toSubgroup.subgroupOf K.toSubgroup
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [← map_extensionSubgroup_abstractSubgroupEquiv k Ω K L hLK]
  constructor
  · rintro ⟨τ, hτ, hτσ⟩
    have : τ = σ :=
      (abstractSubgroupEquivGaloisGroup k Ω K).injective hτσ
    simpa [this] using hτ
  · intro hσ
    exact ⟨σ, hσ, rfl⟩

/-- The ambient quotient map is surjective (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:228`). -/
theorem abstractRelativeToAmbientQuotient_surjective
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    Function.Surjective
      (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal) := by
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  intro q
  refine Quotient.inductionOn' q ?_
  intro τ
  refine ⟨(abstractSubgroupEquivGaloisGroup k Ω K).symm τ, ?_⟩
  change QuotientGroup.mk
    (abstractSubgroupEquivGaloisGroup k Ω K
      ((abstractSubgroupEquivGaloisGroup k Ω K).symm τ)) =
      QuotientGroup.mk τ
  rw [(abstractSubgroupEquivGaloisGroup k Ω K).apply_symm_apply]

/-- **The engine's relative quotient is the ambient quotient** by the upper
fixing subgroup (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:250`). -/
def abstractExtensionQuotientEquivAmbient
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    letI := hnormal
    letI := abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
    K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup ≃*
      (Ω ≃ₐ[abstractFixedField k Ω K] Ω) ⧸
        (abstractRelativeFixedField k Ω hLK).fixingSubgroup := by
  letI := hnormal
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  exact (QuotientGroup.quotientMulEquivOfEq
      (abstractRelativeToAmbientQuotient_ker
        k Ω K L hLK hnormal).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (abstractRelativeToAmbientQuotient k Ω K L hLK hnormal)
      (abstractRelativeToAmbientQuotient_surjective
        k Ω K L hLK hnormal))

/-- **The engine's relative quotient is the concrete Galois group** of the
two fixed fields (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:272`). -/
def abstractExtensionQuotientEquivGaloisGroup
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    letI := hnormal
    K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup ≃*
      (abstractRelativeFixedField k Ω hLK ≃ₐ[abstractFixedField k Ω K]
        abstractRelativeFixedField k Ω hLK) := by
  letI := hnormal
  letI : (abstractRelativeFixedField k Ω hLK).fixingSubgroup.Normal :=
    abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  let H : ClosedSubgroup (Ω ≃ₐ[abstractFixedField k Ω K] Ω) :=
    closedFixingSubgroup (abstractRelativeFixedField k Ω hLK)
  letI : H.toSubgroup.Normal := by
    exact abstractRelativeFixingSubgroup_normal k Ω K L hLK hnormal
  exact (abstractExtensionQuotientEquivAmbient
      k Ω K L hLK hnormal).trans
    ((InfiniteGalois.normalAutEquivQuotient H).trans
      (AlgEquiv.autCongr
        (IntermediateField.equivOfEq
          (InfiniteGalois.fixedField_fixingSubgroup
            (abstractRelativeFixedField k Ω hLK)))))

/-- **In a finite abstract tower the upper fixed field is finite over the
lower** (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:297`). -/
theorem abstractFixedField_relativeFiniteDimensional
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Ω ≃ₐ[k] Ω)).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)) :
    letI : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
      RingHom.toAlgebra
        (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
    FiniteDimensional (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) := by
  letI : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
    RingHom.toAlgebra
      (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
  letI : IsScalarTower k (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : Finite ((baseField (Ω ≃ₐ[k] Ω)).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup) :=
    hKfinite
  letI : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) := hLKfinite
  letI : Finite ((baseField (Ω ≃ₐ[k] Ω)).toSubgroup ⧸
      L.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup) :=
    finite_extension_trans hLK (le_baseField K)
  letI : FiniteDimensional k (abstractFixedField k Ω L) :=
    abstractFixedField_finiteDimensional k Ω L inferInstance
  exact FiniteDimensional.right k
    (abstractFixedField k Ω K) (abstractFixedField k Ω L)

/-- The same relative finiteness in the scalar-extended presentation
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:330`). -/
theorem abstractRelativeFixedField_finiteDimensional
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hKfinite : Finite ((baseField (Ω ≃ₐ[k] Ω)).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)) :
    FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) := by
  letI : Algebra (abstractFixedField k Ω K) (abstractFixedField k Ω L) :=
    RingHom.toAlgebra
      (IntermediateField.inclusion (abstractFixedField_le k Ω hLK))
  letI : FiniteDimensional (abstractFixedField k Ω K)
      (abstractFixedField k Ω L) :=
    abstractFixedField_relativeFiniteDimensional
      k Ω K L hLK hKfinite hLKfinite
  let e : abstractFixedField k Ω L ≃ₗ[abstractFixedField k Ω K]
      abstractRelativeFixedField k Ω hLK :=
    { toFun := fun x => ⟨x.1, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact e.finiteDimensional

/-- **The abstract degree is the concrete degree** of the finite Galois
extension the same pair of fixed fields presents (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean:358`). -/
theorem finiteAbstractExtension_degree_eq_finrank
    (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (hKfinite : Finite ((baseField (Ω ≃ₐ[k] Ω)).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup))
    (hLKfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)) :
    ((FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ) =
      Module.finrank (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) := by
  letI := hnormal
  letI : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) := hLKfinite
  letI : FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKfinite hLKfinite
  letI : IsGalois (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    abstractRelativeFixedField_isGalois k Ω K L hLK hnormal
  calc
    ((FiniteAbstractExtension.ofInclusion L K hLK).degree : ℕ) =
        (L.toSubgroup.subgroupOf K.toSubgroup).index :=
      (FiniteAbstractExtension.ofInclusion L K hLK).subgroup_index_eq_degree.symm
    _ = Nat.card
        (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      Subgroup.index_eq_card (L.toSubgroup.subgroupOf K.toSubgroup)
    _ = Nat.card
        (abstractRelativeFixedField k Ω hLK ≃ₐ[abstractFixedField k Ω K]
          abstractRelativeFixedField k Ω hLK) :=
      Nat.card_congr
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal).toEquiv
    _ = Module.finrank (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK) :=
      IsGalois.card_aut_eq_finrank
        (abstractFixedField k Ω K)
        (abstractRelativeFixedField k Ω hLK)

end

end Atlas.Knowledge
