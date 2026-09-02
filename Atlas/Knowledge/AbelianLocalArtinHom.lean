import Mathlib
import Atlas.Knowledge.FiniteLocalReciprocityLaw
import Atlas.Knowledge.NormQuotient

/-!
# abelian local Artin homomorphism

For a finite abelian Galois extension of a mixed-characteristic local
field, finite local reciprocity takes values in the actual Galois
group, not merely its abelianization: the local Artin homomorphism
`Kˣ →* Gal(L/K)`, surjective with kernel exactly the norm subgroup —
the finite coordinate of the absolute Artin map (#104).

## Main definitions

* `abelianLocalArtinMonoidHom` — the Artin homomorphism into the
  actual abelian Galois group.

## Main statements

* `abelianLocalArtinMonoidHom_surjective` — it is onto; proved.
* `abelianLocalArtinMonoidHom_ker` — its kernel is the norm
  subgroup; proved.

## Implementation notes

The source pairs this algebraic homomorphism with a continuous
refinement built on its topological reciprocity file; the layer takes
only the algebraic half — `IsLocalReciprocity` never asks for
continuity of the reciprocity map, and the absolute assembly's dense
range lives on the target side — so the topological file stays
unported and the deferred profinite-completion claim keeps its own
ledger. Everything else ports token-for-token; the file is the
source's `LocalReciprocity/NormResidue.lean:26`–`:51`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

open scoped IsMulCommutative

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  [FiniteDimensional K L] [IsAbelianGalois K L]

/-- **The finite local Artin homomorphism with values in the actual
Galois group** of an abelian extension ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean:26`]
[Yamaguchi2026]). -/
noncomputable def abelianLocalArtinMonoidHom :
    Kˣ →* (L ≃ₐ[K] L) :=
  ((Abelianization.equivOfComm (H := (L ≃ₐ[K] L))).symm).toMonoidHom.comp
    (localArtinMonoidHom K L)

/-- The actual abelian local Artin homomorphism is surjective
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean:32`]
[Yamaguchi2026]). -/
theorem abelianLocalArtinMonoidHom_surjective :
    Function.Surjective (abelianLocalArtinMonoidHom K L) :=
  (Abelianization.equivOfComm (H := (L ≃ₐ[K] L))).symm.surjective.comp
    (localArtinMonoidHom_surjective K L)

/-- **The kernel of the actual abelian local Artin homomorphism is
the norm subgroup** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean:39`]
[Yamaguchi2026]). -/
theorem abelianLocalArtinMonoidHom_ker :
    MonoidHom.ker (abelianLocalArtinMonoidHom K L) =
      localNormSubgroup K L := by
  rw [← localArtinMonoidHom_ker K L]
  ext a
  simp only [MonoidHom.mem_ker, abelianLocalArtinMonoidHom,
    MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · intro ha
    apply (Abelianization.equivOfComm (H := (L ≃ₐ[K] L))).symm.injective
    simpa using ha
  · intro ha
    rw [ha, map_one]

end

end Atlas.Knowledge
