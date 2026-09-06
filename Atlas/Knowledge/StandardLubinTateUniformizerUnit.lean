import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# standard Lubin–Tate uniformizer unit

The chosen uniformizer of the base, read as a unit of the fraction field: the element
whose powers span the principal side of the norm-subgroup description. A definition
only — the norm statement lives in `Atlas.Knowledge.StandardLubinTateNormSubgroup`,
and this file exists so that the index and membership items can name the unit without
importing the statement they feed.

## Main definitions

* `standardLubinTateUniformizerUnit` — `π` as an element of `Kˣ`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open scoped ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- The uniformizer as a unit of the fraction field
(Yamaguchi 2026,
`LubinTate/FiniteLevel/NormSubgroup.lean:36`). -/
noncomputable def standardLubinTateUniformizerUnit {π : 𝒪[K]} (hπ : Irreducible π) :
    Kˣ :=
  Units.mk0 (algebraMap 𝒪[K] K π) (by
    intro h0
    exact hπ.ne_zero (IsFractionRing.injective 𝒪[K] K (by rw [h0, map_zero])))

end Atlas.Knowledge
