import Mathlib
import Atlas.Knowledge.LubinTateSeries

/-!
# standard Lubin–Tate series

The canonical polynomial member of Milne's `ℱ_π`: over a discrete valuation ring with
finite residue field of cardinality `q`, the series `π X + X ^ q` has constant term
zero, linear coefficient `π`, and reduces to the Frobenius because a uniformizer
reduces to zero. This is the input every standard Lubin–Tate construction downstream is
built on, and it exists without any equal-characteristic assumption. Everything here is
proved.

## Main definitions

* `standardLubinTateSeries` — `π X + X ^ q` as an `Atlas.Knowledge.LubinTateSeries`.

## Main statements

* `standardLubinTateSeries_toPowerSeries` — the underlying series is literally
  `π X + X ^ q`.

## Implementation notes

The hypotheses are the ambient decision of the layer: an abstract Mathlib discrete
valuation ring with finite residue field and `hπ : Irreducible π` replace the source's
bundled complete local field with its chosen uniformizer
(`F.toCompleteDVF.valuation.IsUniformizer`); irreducibility is Mathlib's
characterization of a uniformizer (`DiscreteValuationRing.irreducible_iff_uniformizer`),
and the reduction field is proved from `Irreducible.maximalIdeal_eq`. Finiteness of the
residue field makes `q ≥ 2`, which the constant- and linear-coefficient computations
use.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)] {π : A}

/-- The **standard Lubin–Tate series** `π X + X ^ q`, `q` the residue cardinality, as a
Lubin–Tate series over a discrete valuation ring with finite residue field
([Milne 2020, Chap. I, §2, Ex. 2.10 (a), p.32][MilneCFT];
[Yamaguchi 2026, `LubinTate/FormalModule/StandardSeries.lean:35`][Yamaguchi2026]). -/
noncomputable def standardLubinTateSeries (hπ : Irreducible π) : LubinTateSeries A π where
  toPowerSeries := PowerSeries.C π * PowerSeries.X +
    PowerSeries.X ^ Nat.card (IsLocalRing.ResidueField A)
  constantCoeff_eq_zero := by
    have hq0 : Nat.card (IsLocalRing.ResidueField A) ≠ 0 :=
      Nat.ne_of_gt (lt_trans Nat.zero_lt_one
        (Finite.one_lt_card (α := IsLocalRing.ResidueField A)))
    simp [hq0]
  coeff_one_eq := by
    have hq : 1 ≠ Nat.card (IsLocalRing.ResidueField A) :=
      (Finite.one_lt_card (α := IsLocalRing.ResidueField A)).ne
    simp [PowerSeries.coeff_X_pow, hq]
  map_residue_eq_frobenius := by
    have hπ0 : IsLocalRing.residue A π = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff, hπ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self π
    simp [hπ0]

/-- The underlying series of the standard Lubin–Tate series is literally `π X + X ^ q`
([Milne 2020, Chap. I, §2, Ex. 2.10 (a), p.32][MilneCFT]). -/
@[simp]
theorem standardLubinTateSeries_toPowerSeries (hπ : Irreducible π) :
    (standardLubinTateSeries hπ).toPowerSeries =
      PowerSeries.C π * PowerSeries.X +
        PowerSeries.X ^ Nat.card (IsLocalRing.ResidueField A) :=
  rfl

end Atlas.Knowledge
