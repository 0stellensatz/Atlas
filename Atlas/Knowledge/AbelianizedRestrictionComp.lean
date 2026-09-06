import Mathlib

/-!
# abelianized restriction composition

Restriction of Galois automorphisms through two normal extensions composes after
abelianization, even when their embeddings into the ambient extension do not form a scalar
tower. The two embeddings of the smaller field differ by one of its automorphisms, so the
two restrictions are conjugate.

## Main statements

* `abelianizedRestrictionComp` — composition of abelianized restriction with independent
  embeddings.
* `abelianizedRestriction_autCongr` — transport between ambient fields commutes with
  abelianized restriction, with independent embeddings of the normal field.

## Implementation notes

Mathlib's `IsScalarTower.AlgEquiv.restrictNormalHom_comp` assumes the embeddings compose.
Here `AlgHom.restrictNormal'` identifies the discrepancy as an inner automorphism, which
vanishes in the abelianization. Neither finiteness nor commutativity of the Galois groups is
required. This supplies the embedding comparison in `Atlas.Knowledge.ArtinMapNormNaturality`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

/-- Restriction through normal extensions composes on abelianizations even for independent
embeddings into the ambient field. This removes the compatible-embedding hypothesis from the
restriction arrow used in the norm-residue triangle (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/NormResidueNaturality.lean:34`). -/
theorem abelianizedRestrictionComp
    (K M M' Ω : Type*) [Field K] [Field M] [Field M'] [Field Ω]
    [Algebra K M] [Algebra K M'] [Algebra K Ω]
    [Algebra M M'] [Algebra M Ω] [Algebra M' Ω]
    [IsScalarTower K M M'] [IsScalarTower K M Ω] [IsScalarTower K M' Ω]
    [Normal K M] [Normal K M'] (σ : Ω ≃ₐ[K] Ω) :
    Abelianization.of
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M') M
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M' σ)) =
      Abelianization.of (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M σ) := by
  let i : M →ₐ[K] Ω :=
    (IsScalarTower.toAlgHom K M' Ω).comp (IsScalarTower.toAlgHom K M M')
  let g : M ≃ₐ[K] M := i.restrictNormal' M
  let s := AlgEquiv.restrictNormalHom (F := K) (K₁ := M') M
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M' σ)
  let r := AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M σ
  have hg (x : M) : algebraMap M Ω (g x) = i x :=
    i.restrictNormal_commutes M x
  have hi (x : M) : i (s x) = σ (i x) := by
    change algebraMap M' Ω (algebraMap M M' (s x)) =
      σ (algebraMap M' Ω (algebraMap M M' x))
    exact (congrArg (algebraMap M' Ω)
      (AlgEquiv.restrictNormal_commutes (σ.restrictNormal M') M x)).trans
        (AlgEquiv.restrictNormal_commutes σ M' (algebraMap M M' x))
  have hconj : g * s = r * g := by
    ext x
    apply (algebraMap M Ω).injective
    change algebraMap M Ω (g (s x)) = algebraMap M Ω (r (g x))
    rw [hg, hi]
    exact (congrArg σ (hg x)).symm.trans
      (AlgEquiv.restrictNormal_commutes σ M (g x)).symm
  have h := congrArg (Abelianization.of : (M ≃ₐ[K] M) →* _) hconj
  rw [map_mul, map_mul, mul_comm _ (Abelianization.of g)] at h
  exact mul_left_cancel h

/-- Conjugating an ambient automorphism through a field equivalence preserves its
abelianized restriction to an independently embedded normal field. -/
theorem abelianizedRestriction_autCongr
    (K M Ω Ω' : Type*) [Field K] [Field M] [Field Ω] [Field Ω']
    [Algebra K M] [Algebra K Ω] [Algebra K Ω']
    [Algebra M Ω] [Algebra M Ω'] [IsScalarTower K M Ω] [IsScalarTower K M Ω']
    [Normal K M] (e : Ω ≃ₐ[K] Ω') (σ : Ω ≃ₐ[K] Ω) :
    Abelianization.of (AlgEquiv.restrictNormalHom (F := K) M (AlgEquiv.autCongr e σ)) =
      Abelianization.of (AlgEquiv.restrictNormalHom (F := K) M σ) := by
  let i : M →ₐ[K] Ω' := e.toAlgHom.comp (IsScalarTower.toAlgHom K M Ω)
  let g : M ≃ₐ[K] M := i.restrictNormal' M
  let s := AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω) M σ
  let r := AlgEquiv.restrictNormalHom (F := K) (K₁ := Ω') M (AlgEquiv.autCongr e σ)
  have hg (x : M) : algebraMap M Ω' (g x) = i x := i.restrictNormal_commutes M x
  have hi (x : M) : i (s x) = (AlgEquiv.autCongr e σ) (i x) := by
    change e (algebraMap M Ω (s x)) = e (σ (e.symm (e (algebraMap M Ω x))))
    rw [e.symm_apply_apply]
    exact congrArg e (AlgEquiv.restrictNormal_commutes σ M x)
  have hconj : g * s = r * g := by
    ext x
    apply (algebraMap M Ω').injective
    change algebraMap M Ω' (g (s x)) = algebraMap M Ω' (r (g x))
    rw [hg, hi]
    exact (congrArg (AlgEquiv.autCongr e σ) (hg x)).symm.trans
      (AlgEquiv.restrictNormal_commutes (AlgEquiv.autCongr e σ) M (g x)).symm
  have h := congrArg (Abelianization.of : (M ≃ₐ[K] M) →* _) hconj
  rw [map_mul, map_mul, mul_comm _ (Abelianization.of g)] at h
  exact (mul_left_cancel h).symm

end Atlas.Knowledge
