import Mathlib

/-!
# maximal abelian subextension

The maximal abelian subextension of a field extension, as the supremum of its abelian
Galois intermediate fields: the `M` of the norm limitation theorem — the largest piece of
`L/K` that abelian class field theory can see, and the exact extent to which norm subgroups
of the idele class group forget the non-abelian part. The definition asks for nothing
beyond a field extension; that the supremum is itself abelian over `K` — the
compositum-of-abelian-is-abelian fact that makes it deserve its name, and what connects
`Atlas.Knowledge.normLimitation` to Milne's `M` — is proved here.

## Main definitions

* `maximalAbelianSubextension` — `sSup {M : IntermediateField K L | IsAbelianGalois K M}`.

## Main statements

* `isAbelianGalois_maximalAbelianSubextension` — the supremum is abelian Galois over `K`;
  proved.

## Implementation notes

Defined by the lattice supremum rather than as a fixed field of the commutator, so that no
Galois hypothesis on `L/K` enters: Milne's norm limitation (Chap. VIII, Thm. 4.8) takes an
arbitrary finite extension. The source works instead inside a chosen normal closure
(`AlgebraicNumberTheory/Galois/MaximalAbelianSubextension.lean:47`), fixing the commutator
together with the fixing subgroup of the embedded field — the same subfield through its
Galois-closed model. The abelianness proof stays in the lattice: Mathlib's `normal_iSup`
and `isSeparable_iSup` make the supremum Galois, and commutativity is checked on the adjoin
generators — each generator lies in an abelian member, which is normal, so both
automorphisms restrict to it and commute there.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K]

/-- The **maximal abelian subextension** of `L / K`: the supremum of the abelian Galois
intermediate fields ([Milne 2020, Chap. VIII, §4, Thm. 4.8, p.242][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Galois/MaximalAbelianSubextension.lean:47`]
[Yamaguchi2026]). -/
noncomputable def maximalAbelianSubextension (L : Type*) [Field L] [Algebra K L] :
    IntermediateField K L :=
  sSup {M : IntermediateField K L | IsAbelianGalois K M}

/-- The maximal abelian subextension is abelian Galois over the base: the compositum of
abelian extensions is abelian — Galoisness passes to the supremum, and two automorphisms
commute because they commute after restriction to every abelian member, and the members
generate ([Milne 2020, Chap. VIII, §4, Thm. 4.8, p.242][MilneCFT]). -/
theorem isAbelianGalois_maximalAbelianSubextension (L : Type*) [Field L] [Algebra K L] :
    IsAbelianGalois K (maximalAbelianSubextension K L) := by
  have hT : maximalAbelianSubextension K L =
      ⨆ M : {M : IntermediateField K L | IsAbelianGalois K ↥M}, (M : IntermediateField K L) :=
    sSup_eq_iSup' _
  rw [hT]
  haveI : ∀ M : {M : IntermediateField K L | IsAbelianGalois K ↥M},
      IsGalois K ↥(M : IntermediateField K L) := fun M => M.2.toIsGalois
  haveI : IsGalois K ↥(⨆ M : {M : IntermediateField K L | IsAbelianGalois K ↥M},
      (M : IntermediateField K L)) := ⟨⟩
  haveI : IsMulCommutative
      (↥(⨆ M : {M : IntermediateField K L | IsAbelianGalois K ↥M},
          (M : IntermediateField K L)) ≃ₐ[K]
        ↥(⨆ M : {M : IntermediateField K L | IsAbelianGalois K ↥M},
          (M : IntermediateField K L))) := by
    refine isMulCommutative_iff.mpr fun σ τ => ?_
    have key : (σ * τ).toAlgHom = (τ * σ).toAlgHom := by
      refine IntermediateField.algHom_ext_of_eq_adjoin K
        (IntermediateField.iSup_eq_adjoin K _) ?_
      intro x hx
      obtain ⟨M, hxM⟩ := Set.mem_iUnion.mp hx
      have hle : (M : IntermediateField K L) ≤
          ⨆ M : {M : IntermediateField K L | IsAbelianGalois K ↥M},
            (M : IntermediateField K L) :=
        le_iSup (fun M : {M : IntermediateField K L | IsAbelianGalois K ↥M} =>
          (M : IntermediateField K L)) M
      letI : Algebra ↥(M : IntermediateField K L)
          ↥(⨆ M : {M : IntermediateField K L | IsAbelianGalois K ↥M},
            (M : IntermediateField K L)) :=
        (IntermediateField.inclusion hle).toAlgebra
      haveI : IsScalarTower K ↥(M : IntermediateField K L)
          ↥(⨆ M : {M : IntermediateField K L | IsAbelianGalois K ↥M},
            (M : IntermediateField K L)) :=
        IsScalarTower.of_algebraMap_eq fun r => rfl
      haveI : IsAbelianGalois K ↥(M : IntermediateField K L) := M.2
      -- restrict both automorphisms to the abelian member and commute them there
      have hres : ∀ ρ : ↥(⨆ M : {M : IntermediateField K L | IsAbelianGalois K ↥M},
            (M : IntermediateField K L)) ≃ₐ[K]
              ↥(⨆ M : {M : IntermediateField K L | IsAbelianGalois K ↥M},
                (M : IntermediateField K L)),
          ∀ m : ↥(M : IntermediateField K L),
            ρ (algebraMap _ _ m) =
              algebraMap _ _ (ρ.restrictNormal ↥(M : IntermediateField K L) m) :=
        fun ρ m =>
          (AlgEquiv.restrictNormal_commutes ρ ↥(M : IntermediateField K L) m).symm
      have hy : (⟨x, (IntermediateField.iSup_eq_adjoin K _).ge
            (IntermediateField.subset_adjoin _ _ hx)⟩ :
          ↥(⨆ M : {M : IntermediateField K L | IsAbelianGalois K ↥M},
            (M : IntermediateField K L))) = algebraMap _ _ (⟨x, hxM⟩ :
              ↥(M : IntermediateField K L)) := rfl
      rw [hy]
      simp only [AlgEquiv.coe_toAlgHom]
      rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hres τ, hres σ, hres σ, hres τ]
      congr 1
      rw [← AlgEquiv.mul_apply, ← AlgEquiv.mul_apply, mul_comm']
    exact AlgEquiv.coe_toAlgHom_injective key
  constructor

end Atlas.Knowledge
