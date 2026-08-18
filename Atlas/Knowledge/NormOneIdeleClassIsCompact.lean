import Mathlib
import Atlas.Knowledge.IdeleContent

/-!
# compactness of the norm-one idele class group

Fujisaki's theorem: `C_K¹ = ker (c : C_K → ℝ≥0ˣ)` is compact. The full idele class group
cannot be — the content maps it onto a ray — but the norm-one part is, and the theorem is
the analytic engine of the finiteness results of global class field theory: the finiteness
of the class number and the unit theorem both fall out of it. Recorded ahead of its proof;
this is the phase's one claim.

## Main statements

* `normOneIdeleClass_isCompact` — `C_K¹` is compact, recorded ahead of its proof.

## Implementation notes

The claim is stated on the carrier of `Atlas.Knowledge.normOneIdeleClassGroup` in the
quotient topology that the openness `Fact` of `Atlas.Knowledge.IdeleGroup` makes a
topological group. The theorem is classically attributed to Fujisaki (1951), and its
standard textbook home is Weil's *Basic number theory* — neither is citable here with a
verifiable pinpoint, so the citation is Milne's assertion of the statement, and the name
stays in prose. The source repository proves it in
`AlgebraicNumberTheory/Idele/NormOneCompact.lean` through an adelic Minkowski-style
argument (a compact integral cover shrunk onto the norm-one classes, `:793`); the discharge
of this claim will follow that proof.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField
open NumberField

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- **Fujisaki's theorem**: the norm-one idele class group is compact. Claim recorded ahead
of its proof ([Milne 2020, Chap. V, §4, p.171][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/NormOneCompact.lean:793`][Yamaguchi2026]). -/
theorem normOneIdeleClass_isCompact :
    IsCompact (normOneIdeleClassGroup K : Set (IdeleClassGroup K)) := by
  sorry

end Atlas.Knowledge
