import Mathlib

/-!
# semilinear conjugation of automorphism groups

Compatible isomorphisms of the bottom and top fields of an extension identify its
automorphism group by conjugation, even when the two bases are different types.

## Main definitions

* `semilinearAutCongr` — the automorphism-group equivalence.
-/

namespace Atlas.Knowledge

variable {E F M N : Type*} [Field E] [Field F] [Field M] [Field N]
  [Algebra E M] [Algebra F N]

private def semilinearAutMap (τ : E ≃+* F) (μ : M ≃+* N)
    (hμ : ∀ a, μ (algebraMap E M a) = algebraMap F N (τ a))
    (σ : M ≃ₐ[E] M) : N ≃ₐ[F] N :=
  { μ.symm.trans (σ.toRingEquiv.trans μ) with
    commutes' := by
      intro a
      obtain ⟨b, rfl⟩ := τ.surjective a
      change μ (σ (μ.symm (algebraMap F N (τ b)))) = algebraMap F N (τ b)
      rw [← hμ, μ.symm_apply_apply, σ.commutes, hμ] }

/-- Compatible field isomorphisms act on automorphism groups by conjugation. -/
def semilinearAutCongr (τ : E ≃+* F) (μ : M ≃+* N)
    (hμ : ∀ a, μ (algebraMap E M a) = algebraMap F N (τ a)) :
    (M ≃ₐ[E] M) ≃* (N ≃ₐ[F] N) where
  toFun := semilinearAutMap τ μ hμ
  invFun := semilinearAutMap τ.symm μ.symm (fun b => by
    apply μ.injective
    rw [μ.apply_symm_apply, hμ, τ.apply_symm_apply])
  left_inv σ := by
    ext x
    change μ.symm (μ (σ (μ.symm (μ x)))) = σ x
    rw [μ.symm_apply_apply, μ.symm_apply_apply]
  right_inv σ := by
    ext x
    change μ (μ.symm (σ (μ (μ.symm x)))) = σ x
    rw [μ.apply_symm_apply, μ.apply_symm_apply]
  map_mul' σ ρ := by
    ext x
    change μ (σ (ρ (μ.symm x))) = μ (σ (μ.symm (μ (ρ (μ.symm x)))))
    rw [μ.symm_apply_apply]

/-- The conjugated automorphism evaluates by the top-field isomorphism. -/
theorem semilinearAutCongr_apply (τ : E ≃+* F) (μ : M ≃+* N)
    (hμ : ∀ a, μ (algebraMap E M a) = algebraMap F N (τ a))
    (σ : M ≃ₐ[E] M) (x : N) :
    semilinearAutCongr τ μ hμ σ x = μ (σ (μ.symm x)) := rfl

end Atlas.Knowledge
