import Mathlib

/-!
# restriction between normal intermediate fields

The canonical restriction map `Gal(F/K) →* Gal(E/K)` between two
intermediate fields `E ≤ F` of one ambient extension, packaged so that
callers need not install the auxiliary `Algebra E F` and scalar-tower
instances attached to the inclusion, together with its evaluation law
after both sides are included in the ambient field (#104).

## Main definitions

* `intermediateFieldRestrictNormalHom` — the restriction homomorphism
  `Gal(F/K) →* Gal(E/K)`.

## Main statements

* `intermediateFieldRestrictNormalHom_apply_val` — evaluation through
  the ambient inclusions; proved.

## Implementation notes

Everything ports token-for-token; the file is the source's
`RamificationTheory/GaloisValuation/IntermediateFieldRestriction.lean`
whole.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable {K : Type u} {Ω : Type v}
  [Field K] [Field Ω] [Algebra K Ω]

/-- **Restriction `Gal(F/K) →* Gal(E/K)` for two intermediate fields
`E ≤ F` in one ambient extension** ([Yamaguchi 2026,
`RamificationTheory/GaloisValuation/IntermediateFieldRestriction.lean:22`]
[Yamaguchi2026]). -/
noncomputable def intermediateFieldRestrictNormalHom
    (E F : IntermediateField K Ω) (hEF : E ≤ F) [Normal K E] :
    (F ≃ₐ[K] F) →* (E ≃ₐ[K] E) := by
  letI : Algebra E F :=
    RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  exact AlgEquiv.restrictNormalHom E

/-- Evaluation of the canonical intermediate-field restriction after
both sides are included in the common ambient field ([Yamaguchi 2026,
`RamificationTheory/GaloisValuation/IntermediateFieldRestriction.lean:32`]
[Yamaguchi2026]). -/
theorem intermediateFieldRestrictNormalHom_apply_val
    (E F : IntermediateField K Ω) (hEF : E ≤ F) [Normal K E]
    (sigma : F ≃ₐ[K] F) (x : E) :
    E.val (intermediateFieldRestrictNormalHom E F hEF sigma x) =
      F.val (sigma (IntermediateField.inclusion hEF x)) := by
  letI : Algebra E F :=
    RingHom.toAlgebra (IntermediateField.inclusion hEF).toRingHom
  letI : IsScalarTower K E F := IsScalarTower.of_algebraMap_eq' rfl
  have h := AlgEquiv.restrictNormal_commutes sigma E x
  exact congrArg F.val h

end

end Atlas.Knowledge
