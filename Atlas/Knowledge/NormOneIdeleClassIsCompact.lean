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
topological group. The theorem is classically attributed to Fujisaki (1951); Milne asserts
it without number or proof, and Neukirch–Schmidt–Wingberg state it in exactly this item's
vocabulary — the kernel of the absolute value descended to the idele class group is
compact — pinning the classical homes as Weil, *Basic number theory*, Chap. VI, (1.6), and
Cassels–Fröhlich, Chap. II, §16. Weil's book is keyed in the bibliography but not cached,
so the rendered pinpoint is theirs. The source repository proves the theorem in
`AlgebraicNumberTheory/Idele/NormOneCompact.lean` through an adelic Minkowski-style
argument (a compact integral cover shrunk onto the norm-one classes, `:793`); the discharge
of this claim will follow that proof.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [NeukirchEtAl2008] J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of number fields*,
  Grundlehren der mathematischen Wissenschaften **323**, Springer Berlin Heidelberg, 2008.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField
open NumberField

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- **Fujisaki's theorem**: the norm-one idele class group is compact. Claim recorded ahead
of its proof ([Milne 2020, Chap. V, §4, p.171][MilneCFT];
[Neukirch–Schmidt–Wingberg 2008, Chap. VIII, §1, p.442][NeukirchEtAl2008];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/NormOneCompact.lean:793`][Yamaguchi2026]). -/
theorem normOneIdeleClass_isCompact :
    IsCompact (normOneIdeleClassGroup K : Set (IdeleClassGroup K)) := by
  sorry

end Atlas.Knowledge
