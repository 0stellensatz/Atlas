import Mathlib

/-!
# field norms on unit groups

The common algebraic norm map on unit groups — independent of any
valuation or local-field structure, so valued-field and
discrete-valuation APIs can share the same definition (#104).

## Main definitions

* `normUnits` — the algebra norm restricted to unit groups.

## Main statements

* `normUnits_tower` — unit norms are transitive in a tower; proved.

## Implementation notes

The file ports token-for-token; it is the source's
`LocalFieldTheory/NormUnits.lean` whole.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v w

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/-- **The algebra norm, restricted to unit groups** ([Yamaguchi 2026,
`LocalFieldTheory/NormUnits.lean:21`][Yamaguchi2026]). -/
def normUnits : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

/-- The underlying field element of a unit norm is the algebra norm
([Yamaguchi 2026, `LocalFieldTheory/NormUnits.lean:26`][Yamaguchi2026]). -/
@[simp]
theorem normUnits_apply_coe (x : Lˣ) :
    ((normUnits K L x : Kˣ) : K) = Algebra.norm K (x : L) :=
  rfl

/-- Field norms on unit groups are transitive in a tower
([Yamaguchi 2026, `LocalFieldTheory/NormUnits.lean:31`][Yamaguchi2026]). -/
theorem normUnits_tower
    (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L] [Module.Free M L] (x : Lˣ) :
    normUnits K M (normUnits M L x) = normUnits K L x := by
  apply Units.ext
  exact Algebra.norm_norm

end

end Atlas.Knowledge
