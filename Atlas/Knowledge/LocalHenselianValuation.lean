import Mathlib
import Atlas.Knowledge.AbstractFixedFieldNorm
import Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField
import Atlas.Knowledge.LocalFixedResidueFinrank

/-!
# Henselian valuation datum of a local field

The engine's valuation datum, instantiated: the normalized valuation of a
mixed-characteristic local field, on the coefficient group its degree datum
acts through, is a Henselian valuation. The value group is the copy of the
integers with bijective canonical value quotients, and for every finite
abstract field — normal over the base or not — the norm image is the
residue-degree multiple of the value group, by the norm-range computation
read through the residue-degree transfer. With the degree datum of the local
residue action, this is the second of the reciprocity engine's three inputs
(#104).

## Main definitions

* `localHenselianValuation` — the valuation datum of a mixed-characteristic
  local field.

## Implementation notes

The mixed-characteristic structure on a finite fixed field is produced
inside the norm-range proof by
`Atlas.Knowledge.exists_extension_isMixedCharLocalField`, replacing the
source's ninety-line manufacture of a nonarchimedean local field structure
through spectral norms; the integral-closure witness the source threads is
the layer's `Atlas.Knowledge.integerIsIntegralClosure` instance, already
inside the norm law.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- **The valuation datum of a mixed-characteristic local field**: the
normalized valuation on the base fixed coefficients is a Henselian valuation
for the local residue degree datum (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalHenselianValuation.lean:25`). -/
def localHenselianValuation :
    ValuationData (localResidueDatum K)
      (galoisAmbientUnitsRep K (AlgebraicClosure K)) := by
  refine
    { toAddMonoidHom := localBaseValuation K
      integers_mem := intCast_mem_localBaseValuation_range K
      canonical_value_quotient_bijective := fun n _ =>
        localCanonicalValueQuotientMap_bijective K n
      norm_range := ?_ }
  intro F
  letI : FiniteDimensional K
      (abstractFixedField K (AlgebraicClosure K) F.field) :=
    abstractFixedField_finiteDimensional
      K (AlgebraicClosure K) F.field F.finite
  obtain ⟨vE, tE, hVE, _hVT, hMCLF⟩ :=
    exists_extension_isMixedCharLocalField K
      (abstractFixedField K (AlgebraicClosure K) F.field)
  letI := vE
  letI := tE
  letI := hVE
  letI := hMCLF
  rw [localResidueDatum_residueDegree_eq_residueFinrank K F]
  exact localBaseValuation_comp_normToBase_range_eq_residueFinrank
    K F.field

end

end Atlas.Knowledge
