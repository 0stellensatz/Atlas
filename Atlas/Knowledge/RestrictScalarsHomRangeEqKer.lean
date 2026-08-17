import Mathlib

/-!
# scalar-restriction range as normal-restriction kernel

For a tower of fields `K ⊆ E ⊆ L` with `E` normal over `K`, the subgroup of `L ≃ₐ[K] L` fixing
`E` pointwise has two names: it is the range of
`AlgEquiv.restrictScalarsHom K : (L ≃ₐ[E] L) →* (L ≃ₐ[K] L)`, and it is the kernel of the
restriction `AlgEquiv.restrictNormalHom E : (L ≃ₐ[K] L) →* (E ≃ₐ[K] E)` that normality of `E`
over `K` provides. This is the background identity Serre uses silently in the proof of Prop. 3
when, having chosen one `s ∈ G` representing `σ ∈ G/H`, he writes the other representatives as
`st`, `t ∈ H`: a fiber of the restriction is a coset of the subgroup fixing the subextension.

## Main statements

* `restrictScalarsHom_range_eq_ker` — the range of `AlgEquiv.restrictScalarsHom K` equals the
  kernel of `AlgEquiv.restrictNormalHom E`. No finiteness and no Galois hypothesis on `L` over
  `K` enters: `E` normal over `K` is all the restriction needs to exist.
* `restrictNormalHom_fiber_eq` — under finiteness, the `Finset` of automorphisms restricting to
  a given `σ' : E ≃ₐ[K] E` is the image of `L ≃ₐ[E] L` under `t ↦ σ * t.restrictScalars K`,
  for any one representative `σ`.

## Implementation notes

Mathlib carries the kernel description as `IntermediateField.restrictNormalHom_ker`, typed at an
`IntermediateField K L` and phrased through `IntermediateField.fixingSubgroup`. The tower here
is abstract—`E` is a field in its own right, related to `L` only through `algebraMap E L`—so
that statement does not apply, and this item is its abstract-tower sibling with the fixing
subgroup presented as a `MonoidHom.range` instead. The forward inclusion is
`AlgEquiv.restrictNormal_commutes` plus injectivity of `algebraMap E L`; the reverse inclusion
reconstructs from `s : L ≃ₐ[K] L` fixing `algebraMap E L` pointwise the `E`-algebra
automorphism `AlgEquiv.ofRingEquiv (f := s.toRingEquiv)`, whose `commutes'` field is exactly
the kernel equation evaluated through the commuting square. The fiber corollary assumes
`[FiniteDimensional E L]` alongside `[FiniteDimensional K L]` because `Module.Finite.right` is
not an instance, and `DecidableEq` on the two automorphism groups because `Finset.filter` and
`Finset.image` ask for them; all four are `Classical`-dischargeable at a use site.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K] (E : Type*) [Field E] (L : Type*) [Field L]
  [Algebra K E] [Algebra K L] [Algebra E L] [IsScalarTower K E L] [Normal K E]

/-- For a tower `K ⊆ E ⊆ L` of fields with `E` normal over `K`, the subgroup of `L ≃ₐ[K] L`
fixing `E` pointwise—the range of `AlgEquiv.restrictScalarsHom K`—is the kernel of the
restriction `AlgEquiv.restrictNormalHom E`
([Serre 1979, Chap. IV, §1, proof of Prop. 3, p.63][Serre1979]). -/
theorem restrictScalarsHom_range_eq_ker :
    (AlgEquiv.restrictScalarsHom (S := E) (A := L) K).range =
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker := by
  have hcomm : ∀ (s : L ≃ₐ[K] L) (y : E),
      algebraMap E L (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E s y) =
        s (algebraMap E L y) := fun s y => AlgEquiv.restrictNormal_commutes s E y
  refine le_antisymm ?_ ?_
  · rintro s ⟨t, rfl⟩
    rw [MonoidHom.mem_ker]
    ext y
    apply (algebraMap E L).injective
    rw [hcomm]
    simp
  · intro s hs
    rw [MonoidHom.mem_ker] at hs
    have hfix : ∀ y : E, s (algebraMap E L y) = algebraMap E L y := fun y => by
      rw [← hcomm s y, hs]; rfl
    exact ⟨AlgEquiv.ofRingEquiv (f := s.toRingEquiv) hfix, AlgEquiv.ext fun _ => rfl⟩

section Finite

variable [FiniteDimensional K L] [FiniteDimensional E L]
  [DecidableEq (E ≃ₐ[K] E)] [DecidableEq (L ≃ₐ[K] L)]

/-- For `σ : L ≃ₐ[K] L` restricting to `σ' : E ≃ₐ[K] E`, the automorphisms of `L` over `K`
restricting to `σ'` are exactly the products `σ * t.restrictScalars K` for `t : L ≃ₐ[E] L`—the
representatives of `σ'` are the `st`, `t ∈ H`
([Serre 1979, Chap. IV, §1, proof of Prop. 3, p.63][Serre1979]). -/
theorem restrictNormalHom_fiber_eq (σ : L ≃ₐ[K] L) (σ' : E ≃ₐ[K] E)
    (hσ : AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E σ = σ') :
    Finset.univ.filter
        (fun s : L ≃ₐ[K] L => AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E s = σ') =
      Finset.univ.image (fun t : L ≃ₐ[E] L => σ * t.restrictScalars K) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · intro h
    have hker : σ⁻¹ * s ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, h, inv_mul_cancel]
    obtain ⟨t, ht⟩ := (restrictScalarsHom_range_eq_ker K E L).ge hker
    exact ⟨t, by rw [show t.restrictScalars K = AlgEquiv.restrictScalarsHom K t from rfl, ht,
      mul_inv_cancel_left]⟩
  · rintro ⟨t, rfl⟩
    have hker := (restrictScalarsHom_range_eq_ker K E L).le (MonoidHom.mem_range.mpr ⟨t, rfl⟩)
    rw [MonoidHom.mem_ker] at hker
    rw [map_mul, hσ, show t.restrictScalars K = AlgEquiv.restrictScalarsHom K t from rfl, hker,
      mul_one]

end Finite

end Atlas.Knowledge
