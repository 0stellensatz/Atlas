import Mathlib
import Atlas.Knowledge.AbstractExtensionUnitsRepIso

/-!
# restriction to a relative fixed field

The quotient-to-Galois equivalence of an abstract fixed-field extension evaluates by
restricting an ambient representative. This is the pointwise reading needed to compare
an intrinsic Artin lift with an element of the abstract Galois quotient.

## Main statements

* `abstractExtensionQuotientEquivGaloisGroup_mk` — a quotient representative acts by restriction.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

/-- A relative Galois quotient class acts by its ambient representative
(Yamaguchi 2026, `FiniteAbstractFixedField.lean:272`). -/
theorem abstractExtensionQuotientEquivGaloisGroup_mk
    (k Ω : Type*) [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (H L : ClosedSubgroup (Ω ≃ₐ[k] Ω)) (hLH : L.toSubgroup ≤ H.toSubgroup)
    [(L.toSubgroup.subgroupOf H.toSubgroup).Normal]
    (s : H.toSubgroup) :
    letI : IsGalois (abstractFixedField k Ω H) (abstractRelativeFixedField k Ω hLH) :=
      abstractRelativeFixedField_isGalois k Ω H L hLH inferInstance
    abstractExtensionQuotientEquivGaloisGroup k Ω H L hLH inferInstance (QuotientGroup.mk s) =
      AlgEquiv.restrictNormalHom (F := abstractFixedField k Ω H)
        (abstractRelativeFixedField k Ω hLH) (abstractSubgroupEquivGaloisGroup k Ω H s) := by
  letI : IsGalois (abstractFixedField k Ω H) (abstractRelativeFixedField k Ω hLH) :=
    abstractRelativeFixedField_isGalois k Ω H L hLH inferInstance
  ext x
  exact (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
    k Ω H L hLH inferInstance s x).symm.trans
      (AlgEquiv.restrictNormal_commutes (abstractSubgroupEquivGaloisGroup k Ω H s)
        (abstractRelativeFixedField k Ω hLH) x).symm

end Atlas.Knowledge
