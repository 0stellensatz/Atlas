import Mathlib
import Atlas.Knowledge.NormQuotient

/-!
# additive norm subgroup

The additive subgroup of `Additive Kˣ` attached to the multiplicative
norm subgroup, identified with the kernel of the additive reading of
the norm-quotient map — the hinge on which the abstract finite norm
quotient is compared with the concrete one (#104).

## Main definitions

* `additiveNormSubgroup` — the norm subgroup, read additively.

## Main statements

* `additiveNormSubgroup_eq_ker_quotient_map` — it is the kernel of the
  norm-quotient map; proved.

## Implementation notes

Everything ports token-for-token; the two declarations are the
source's `CyclicCohomology/TateH0/NormImage.lean:108` and `:113`, the
only slice of that file the quotient transport consumes.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

/-- The additive subgroup of `Additive Kˣ` attached to the
multiplicative norm subgroup ([Yamaguchi 2026,
`CyclicCohomology/TateH0/NormImage.lean:108`][Yamaguchi2026]). -/
def additiveNormSubgroup (K L : Type u) [Field K] [Field L] [Algebra K L] :
    AddSubgroup (Additive Kˣ) :=
  (localNormSubgroup K L).toAddSubgroup

/-- The additive norm subgroup is the kernel of the norm-quotient map
([Yamaguchi 2026,
`CyclicCohomology/TateH0/NormImage.lean:113`][Yamaguchi2026]). -/
lemma additiveNormSubgroup_eq_ker_quotient_map (K L : Type u)
    [Field K] [Field L] [Algebra K L] :
    additiveNormSubgroup K L =
      (MonoidHom.toAdditive (normClass K L)).ker := by
  ext x
  change Additive.toMul x ∈ localNormSubgroup K L ↔
    Additive.ofMul (normClass K L (Additive.toMul x)) = 0
  constructor
  · intro hx
    exact congrArg Additive.ofMul
      ((normClass_eq_one_iff K L (Additive.toMul x)).mpr
        (MonoidHom.mem_range.mp hx))
  · intro hx
    exact MonoidHom.mem_range.mpr
      ((normClass_eq_one_iff K L (Additive.toMul x)).mp
        (Additive.ofMul.injective hx))

end

end Atlas.Knowledge
