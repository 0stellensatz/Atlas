import Mathlib
import Atlas.Knowledge.AbelianLocalArtinMonoidHom
import Atlas.Knowledge.IntermediateFieldNormResidueNaturality
import Atlas.Knowledge.IntermediateFieldRestrictNormalHom

/-!
# restriction naturality of the abelian local Artin homomorphism

The actual algebraic Artin homomorphisms commute with restriction
between finite abelian intermediate fields of the algebraic closure:
restricting the Artin automorphism of the larger field to the smaller
yields the smaller field's Artin automorphism (#104).

## Main statements

* `abelianLocalArtinMonoidHom_restrict` — the restriction square of the
  abelian local Artin homomorphisms commutes; proved.

## Implementation notes

The source pairs this algebraic naturality with its continuous
refinements (`intermediateFieldRestrictContinuous` and the continuous
`abelianLocalArtinMap_restrict`, its `:24` and `:47`); the layer takes
only the algebraic square — the recorded continuity fork, as on
`Atlas.Knowledge.AbelianLocalArtinMonoidHom`, whose topological file
stays unported. The intermediate fields live in the layer's
`AlgebraicClosure K` ambient where the source pins its separable
closure, over `[IsMixedCharLocalField K]` in place of the source's
`[IsNonarchimedeanLocalField K]` — the arc conventions recorded on
`Atlas.Knowledge.FiniteLocalReciprocityLaw` and
`Atlas.Knowledge.IntermediateFieldNormResidueNaturality`. Everything
else ports token-for-token; the file is the source's
`LocalReciprocity/NormResidueNaturality.lean:34`–`:43`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable (K : Type) [Field K]
  [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- **Finite Artin homomorphisms commute with restriction along a tower
of finite abelian intermediate fields** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/NormResidueNaturality.lean:34`]
[Yamaguchi2026]). -/
theorem abelianLocalArtinMonoidHom_restrict
    (E F : IntermediateField K (AlgebraicClosure K)) (hEF : E ≤ F)
    [FiniteDimensional K E] [FiniteDimensional K F]
    [IsAbelianGalois K E] [IsAbelianGalois K F] :
    (intermediateFieldRestrictNormalHom E F hEF).comp
        (abelianLocalArtinMonoidHom K F) =
      abelianLocalArtinMonoidHom K E := by
  apply MonoidHom.ext
  intro a
  exact localArtinAutomorphism_restrict K E F hEF a

end

end Atlas.Knowledge
