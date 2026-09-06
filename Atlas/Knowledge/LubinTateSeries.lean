import Mathlib

/-!
# Lubin–Tate series

The coefficient package of Lubin–Tate theory: a one-variable power series over a local
ring with constant term zero, prescribed linear coefficient `π`, and reduction modulo the
maximal ideal equal to the `q`-power map, `q` the cardinality of the residue field —
Milne's set `ℱ_π`. Everything the recursive intertwiner construction consumes is these
three fields; the structure itself asks for no more of the ambient ring than a local
`CommRing`, and the standard example and the fundamental lemma add their own hypotheses.
Everything here is proved.

## Main definitions

* `LubinTateSeries` — the structure: constant term zero, linear coefficient `π`,
  reduction the `q`-power Frobenius.

## Main statements

* `LubinTateSeries.ext` — equality of the underlying series is equality.

## Implementation notes

The source binds the package to its own bundled local-field structure — a chosen complete
discretely valued field with finite residue field — and takes the coefficient ring to be
its valuation subring (`LubinTate/FormalModule/Series.lean:28`). The recursion that
consumes the structure uses none of the completeness, so Atlas states the layer over an
abstract Mathlib local ring, of which the source's valuation subring is the special case;
Milne's ambient (`A = 𝒪_K`, `K` nonarchimedean local) narrows the same way. When the
residue field is infinite `Nat.card` is `0` and the Frobenius field degenerates to
`X ^ 0`; the downstream items all assume finiteness, so nothing is built on the
degenerate reading.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

/-- A **Lubin–Tate series** over a local ring `A` with prescribed linear coefficient
`π`: constant term zero, linear coefficient `π`, and reduction modulo the maximal ideal
the `q`-power map for `q` the residue cardinality — Milne's `ℱ_π`
([Milne 2020, Chap. I, §2, Defn. 2.9, pp.31–32][MilneCFT]; Yamaguchi 2026,
`LubinTate/FormalModule/Series.lean:28`). -/
structure LubinTateSeries (A : Type*) [CommRing A] [IsLocalRing A] (π : A) where
  /-- The underlying one-variable power series over `A`. -/
  toPowerSeries : PowerSeries A
  /-- The constant coefficient vanishes. -/
  constantCoeff_eq_zero : PowerSeries.constantCoeff toPowerSeries = 0
  /-- The linear coefficient is the prescribed element `π`. -/
  coeff_one_eq : PowerSeries.coeff 1 toPowerSeries = π
  /-- Reduction to the residue field is the `q`-power Frobenius series. -/
  map_residue_eq_frobenius :
    PowerSeries.map (IsLocalRing.residue A) toPowerSeries =
      (PowerSeries.X : PowerSeries (IsLocalRing.ResidueField A)) ^
        Nat.card (IsLocalRing.ResidueField A)

attribute [simp] LubinTateSeries.constantCoeff_eq_zero LubinTateSeries.coeff_one_eq
  LubinTateSeries.map_residue_eq_frobenius

namespace LubinTateSeries

variable {A : Type*} [CommRing A] [IsLocalRing A] {π : A}

/-- Two Lubin–Tate series with equal underlying series are equal. -/
@[ext]
theorem ext {e e' : LubinTateSeries A π} (h : e.toPowerSeries = e'.toPowerSeries) :
    e = e' := by
  cases e; cases e'; cases h; rfl

end LubinTateSeries

end Atlas.Knowledge
