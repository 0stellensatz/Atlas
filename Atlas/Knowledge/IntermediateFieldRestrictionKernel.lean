import Mathlib
import Atlas.Knowledge.IntermediateFieldRestrictNormalHom

/-!
# kernel of the subfloor restriction

The restriction `Gal (F/K) →* Gal (E/K)` between two normal intermediate fields `E ≤ F` of
one ambient normal extension, `Atlas.Knowledge.intermediateFieldRestrictNormalHom`, read at
the level a descent argument needs: it is onto, its kernel has order the degree ratio
`[F : E]`, an automorphism of a compositum `E₁ ⊔ E₂` that restricts trivially to both factors
is trivial, and so a compositum of two abelian floors is abelian. Every ramification and
reciprocity statement of the layer that passes from a floor to a subfloor passes through this
map, and these are the four facts it needs about the map itself, stated once over abstract
intermediate fields so that they are applied — never re-elaborated — at the concrete carriers
of the Lubin–Tate tower.

## Main statements

* `intermediateFieldRestrictNormalHom_surjective` — the restriction is onto.
* `card_ker_intermediateFieldRestrictNormalHom` — `#ker · [E : K] = [F : K]`.
* `intermediateFieldRestrictNormalHom_sup_eq_one` — joint injectivity on a compositum.
* `isAbelianGalois_sup` — a compositum of abelian floors is abelian.

## Implementation notes

The map is defined by a `letI` on the inclusion algebra, so each proof reinstalls that
algebra and closes by the Mathlib statement about `AlgEquiv.restrictNormalHom`
(`AlgEquiv.restrictNormalHom_surjective`); the order of the kernel is the first isomorphism
theorem against `IsGalois.card_aut_eq_finrank` on both floors. Joint injectivity lifts the
automorphism to the ambient field, reads the two trivial restrictions as membership in the
two fixing subgroups through `Atlas.Knowledge.intermediateFieldRestrictNormalHom_apply_val`,
and closes by `IntermediateField.fixingSubgroup_sup`; commutativity of a compositum's Galois
group is the commutator restricting trivially to each factor. Applying these at a concrete
carrier is a plain instantiation, which is the point: the direct `letI`-and-restrict pattern
at the Lubin–Tate level closures overran the kernel's budget, and the general statements are
what replaces it.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

variable {K : Type*} [Field K] {Ω : Type*} [Field Ω] [Algebra K Ω]
  {E F : IntermediateField K Ω} (hEF : E ≤ F)

/-- The subfloor restriction is onto — `AlgEquiv.restrictNormalHom_surjective` at the
inclusion algebra. -/
theorem intermediateFieldRestrictNormalHom_surjective [Normal K E] [Normal K F] :
    Function.Surjective (intermediateFieldRestrictNormalHom E F hEF) := by
  letI : Algebra E F := RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  exact AlgEquiv.restrictNormalHom_surjective F

/-- **The order of the restriction kernel times the lower degree is the upper degree**:
`#ker · [E : K] = [F : K]`, the first isomorphism theorem read through
`IsGalois.card_aut_eq_finrank` on both floors ([Serre 1979, Chap. IV, §1, p.61][Serre1979] —
the tower `G (F/E) ⊆ G (F/K)`). -/
theorem card_ker_intermediateFieldRestrictNormalHom [Normal K E] [FiniteDimensional K F]
    [IsGalois K F] [IsGalois K E] :
    Nat.card (intermediateFieldRestrictNormalHom E F hEF).ker * Module.finrank K E =
      Module.finrank K F := by
  haveI : FiniteDimensional K E := FiniteDimensional.of_injective
    (IntermediateField.inclusion hEF).toLinearMap (IntermediateField.inclusion hEF).injective
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (intermediateFieldRestrictNormalHom E F hEF).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
    (intermediateFieldRestrictNormalHom_surjective hEF)).toEquiv,
    IsGalois.card_aut_eq_finrank, IsGalois.card_aut_eq_finrank] at h
  rw [h, mul_comm]

/-- **Joint injectivity on a compositum**: an automorphism of `E₁ ⊔ E₂` restricting trivially
to `E₁` and to `E₂` is trivial — its lift to the ambient field fixes both factors, hence the
compositum, by `IntermediateField.fixingSubgroup_sup`. -/
theorem intermediateFieldRestrictNormalHom_sup_eq_one {E₁ E₂ : IntermediateField K Ω}
    [Normal K E₁] [Normal K E₂] [Normal K (E₁ ⊔ E₂ : IntermediateField K Ω)] [Normal K Ω]
    {σ : (E₁ ⊔ E₂ : IntermediateField K Ω) ≃ₐ[K] (E₁ ⊔ E₂ : IntermediateField K Ω)}
    (h₁ : intermediateFieldRestrictNormalHom E₁ (E₁ ⊔ E₂) le_sup_left σ = 1)
    (h₂ : intermediateFieldRestrictNormalHom E₂ (E₁ ⊔ E₂) le_sup_right σ = 1) : σ = 1 := by
  obtain ⟨σ', hσ'⟩ := AlgEquiv.restrictNormalHom_surjective (F := K)
    (K₁ := (E₁ ⊔ E₂ : IntermediateField K Ω)) Ω σ
  have hfix : ∀ (E : IntermediateField K Ω) [Normal K E] (hE : E ≤ E₁ ⊔ E₂),
      intermediateFieldRestrictNormalHom E (E₁ ⊔ E₂) hE σ = 1 → ∀ x ∈ E, σ' x = x := by
    intro E _ hE hres x hx
    have h1 := intermediateFieldRestrictNormalHom_apply_val E (E₁ ⊔ E₂) hE σ ⟨x, hx⟩
    rw [hres, AlgEquiv.one_apply] at h1
    have h2 := AlgEquiv.restrictNormal_commutes σ' (E₁ ⊔ E₂ : IntermediateField K Ω)
      (IntermediateField.inclusion hE ⟨x, hx⟩)
    change algebraMap _ Ω ((AlgEquiv.restrictNormalHom (E₁ ⊔ E₂ : IntermediateField K Ω) σ')
      (IntermediateField.inclusion hE ⟨x, hx⟩)) =
        σ' (algebraMap _ Ω (IntermediateField.inclusion hE ⟨x, hx⟩)) at h2
    rw [hσ'] at h2
    change E.val ⟨x, hx⟩ =
      (E₁ ⊔ E₂ : IntermediateField K Ω).val (σ (IntermediateField.inclusion hE ⟨x, hx⟩)) at h1
    change (E₁ ⊔ E₂ : IntermediateField K Ω).val (σ (IntermediateField.inclusion hE ⟨x, hx⟩)) =
      σ' x at h2
    exact h2.symm.trans h1.symm
  have hmem : σ' ∈ (E₁ ⊔ E₂ : IntermediateField K Ω).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨(IntermediateField.mem_fixingSubgroup_iff _ _).2 (hfix E₁ le_sup_left h₁),
      (IntermediateField.mem_fixingSubgroup_iff _ _).2 (hfix E₂ le_sup_right h₂)⟩
  rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker] at hmem
  rw [← hσ', hmem]

/-- **A compositum of two abelian floors is abelian**: a commutator restricts to a commutator
on each factor, hence to `1`, hence is `1` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteAbelianSubextension.lean:206`, the abstract
compositum's commutativity). -/
theorem isAbelianGalois_sup {E₁ E₂ : IntermediateField K Ω} [IsAbelianGalois K E₁]
    [IsAbelianGalois K E₂] [Normal K Ω] [IsGalois K (E₁ ⊔ E₂ : IntermediateField K Ω)] :
    IsAbelianGalois K (E₁ ⊔ E₂ : IntermediateField K Ω) where
  is_comm := ⟨fun σ τ => by
    have h : σ * τ * (τ * σ)⁻¹ = 1 := by
      refine intermediateFieldRestrictNormalHom_sup_eq_one ?_ ?_
      · rw [map_mul, map_inv, map_mul, map_mul,
          IsMulCommutative.is_comm.comm
            (intermediateFieldRestrictNormalHom E₁ (E₁ ⊔ E₂) le_sup_left σ),
          mul_inv_cancel]
      · rw [map_mul, map_inv, map_mul, map_mul,
          IsMulCommutative.is_comm.comm
            (intermediateFieldRestrictNormalHom E₂ (E₁ ⊔ E₂) le_sup_right σ),
          mul_inv_cancel]
    exact mul_inv_eq_one.1 h⟩

end Atlas.Knowledge
