import Mathlib
import Atlas.Knowledge.MaximalAbelianSubextension
import Atlas.Knowledge.IdeleClassNormRange

/-!
# norm limitation

The norm limitation theorem: the idele-class norm subgroup of an arbitrary finite
extension equals that of its maximal abelian subextension — abelian class field theory
sees no further than the abelian part, and norm subgroups cannot distinguish an extension
from the largest abelian piece inside it. Recorded ahead of its proof.

## Main statements

* `normLimitation` — `N_{L/K} (C_L) = N_{M/K} (C_M)` for `M` the maximal abelian
  subextension of `L / K`; recorded ahead of its proof.

## Implementation notes

Milne's statement takes the maximal abelian subextension of `L / K` itself — not of a
normal closure, which is how the phase plan's shape line paraphrased it; this item follows
Milne, and the source's model (the distinguished copy inside a chosen normal closure,
`GlobalClassFieldTheory/GlobalClassFields/NormLimitation.lean:131`) is the same subfield
read through its embedding. No Galois hypothesis is carried, exactly as in Milne.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- **Norm limitation**: the norm subgroup of a finite extension is that of its maximal
abelian subextension. Claim recorded ahead of its proof
([Milne 2020, Chap. VIII, §4, Thm. 4.8, p.242][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/GlobalClassFields/NormLimitation.lean:131`,
on its normal-closure model][Yamaguchi2026]). -/
theorem normLimitation (L : Type*) [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] :
    ideleClassNormRange K L =
      ideleClassNormRange K (maximalAbelianSubextension K L) := by
  sorry

end Atlas.Knowledge

end
