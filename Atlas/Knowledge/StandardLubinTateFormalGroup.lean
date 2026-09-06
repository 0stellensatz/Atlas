import Mathlib
import Atlas.Knowledge.LubinTateFormalGroup
import Atlas.Knowledge.LubinTateIntertwiner
import Atlas.Knowledge.StandardLubinTateSeries

/-!
# standard Lubin–Tate formal group

The formal group law of the standard series, landing in Mathlib's own `FormalGroup`: the
unique two-variable intertwiner of `π X + X ^ q` with itself with linear term `X + Y`.
Associativity and commutativity are the general laws of
`Atlas.Knowledge.lubinTateFormalGroupPowerSeries` read at the standard series — the two
series are definitionally the same intertwiner — so this item is now the standard
instance of the general formal module, and the `FormalGroup` value bundles its
associativity. Everything here is proved.

## Main definitions

* `standardLubinTateFormalGroupPowerSeries` — the intertwiner with linear term `X + Y`.
* `standardLubinTateFormalGroup` — the `FormalGroup` it defines.

## Main statements

* `existsUnique_standardLubinTateFormalGroupPowerSeries` — the characterizing property.
* `standardLubinTateFormalGroup_isComm` — commutativity, as Mathlib's `IsComm` instance.

## Implementation notes

The closure machinery this file once carried privately — intertwining and prescribed
linear terms preserved by substitution — lives publicly in
`Atlas.Knowledge.LubinTateFormalGroup` since the general formal module landed, and the
associativity and commutativity computations reduce to `simpa` against the general laws
through the definitional identity of the two series. The `FormalGroup` bundle keeps the
shape Mathlib expects: the linear coefficients are the `coeff_single` face of the
prescribed linear term, and `IsComm` reads the general commutativity law with the sides
swapped.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open MvPowerSeries

namespace Atlas.Knowledge

section FormalGroupAssembly

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)] {π : A}

/-- The **standard Lubin–Tate formal group series**: the unique two-variable intertwiner
of the standard series with itself with linear term `X + Y`
([Milne 2020, Chap. I, §2, Prop. 2.12, p.33][MilneCFT]; Yamaguchi 2026,
`LubinTate/FormalModule/StandardFormalGroup.lean:331`). -/
noncomputable def standardLubinTateFormalGroupPowerSeries (hπ : Irreducible π) :
    MvPowerSeries (Fin 2) A :=
  lubinTateIntertwiner hπ (standardLubinTateSeries hπ) (standardLubinTateSeries hπ)
    (fun _ => 1)

/-- The characterizing property of the standard formal-group series
([Milne 2020, Chap. I, §2, Lem. 2.11 and Prop. 2.12, pp.32–33][MilneCFT];
Yamaguchi 2026,
`LubinTate/FormalModule/StandardFormalGroup.lean:353`). -/
theorem existsUnique_standardLubinTateFormalGroupPowerSeries (hπ : Irreducible π) :
    ∃! H : MvPowerSeries (Fin 2) A,
      LubinTateHasLinearTerm H (fun _ => 1) ∧
        LubinTateIntertwines (standardLubinTateSeries hπ)
          (standardLubinTateSeries hπ) H :=
  existsUnique_lubinTateIntertwiner hπ _ _ _

/- The standard series' formal group is the general one at the standard series. -/
private theorem std_eq (hπ : Irreducible π) :
    standardLubinTateFormalGroupPowerSeries hπ =
      lubinTateFormalGroupPowerSeries hπ (standardLubinTateSeries hπ) := rfl

private theorem hLT_std (hπ : Irreducible π) :
    LubinTateHasLinearTerm (standardLubinTateFormalGroupPowerSeries hπ)
      (fun _ : Fin 2 => (1 : A)) :=
  lubinTateIntertwiner_hasLinearTerm hπ _ _ _

private theorem hF0_std (hπ : Irreducible π) :
    constantCoeff (standardLubinTateFormalGroupPowerSeries hπ) = 0 :=
  (hLT_std hπ).constantCoeff_eq_zero

/-- The **standard Lubin–Tate formal group**, landing in Mathlib's `FormalGroup`: the
formal group law admitting the standard series as an endomorphism
([Milne 2020, Chap. I, §2, Prop. 2.12, p.33][MilneCFT]; Yamaguchi 2026,
`LubinTate/FormalModule/StandardFormalGroup.lean:673`). -/
noncomputable def standardLubinTateFormalGroup (hπ : Irreducible π) : FormalGroup A where
  toPowerSeries := standardLubinTateFormalGroupPowerSeries hπ
  zero_constantCoeff := hF0_std hπ
  lin_coeff_X := by
    have := (hLT_std hπ).coeff_single 0
    simpa using this
  lin_coeff_Y := by
    have := (hLT_std hπ).coeff_single 1
    simpa using this
  assoc := by
    have := lubinTateFormalGroupPowerSeries_assoc hπ (standardLubinTateSeries hπ)
    rw [← std_eq] at this
    simpa using this

/-- The standard Lubin–Tate formal group is commutative
([Milne 2020, Chap. I, §2, Prop. 2.12, p.33][MilneCFT];
Yamaguchi 2026,
`LubinTate/FormalModule/StandardFormalGroup.lean:688`). -/
instance standardLubinTateFormalGroup_isComm (hπ : Irreducible π) :
    (standardLubinTateFormalGroup hπ).IsComm where
  comm := by
    have := (lubinTateFormalGroupPowerSeries_comm hπ (standardLubinTateSeries hπ)).symm
    rw [← std_eq] at this
    simpa [standardLubinTateFormalGroup] using this

end FormalGroupAssembly

end Atlas.Knowledge
