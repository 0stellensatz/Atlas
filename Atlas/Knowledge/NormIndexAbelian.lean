import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# norm index of an abelian extension

The norm index of a finite abelian extension of mixed-characteristic local fields is
its degree: `#(Kˣ ⧸ N Lˣ) = [L : K]`. This is the cardinality summit of finite local
reciprocity — `Kˣ/N Lˣ ≅ Gal(L/K)` — and the single point where the cyclic case of
`Atlas.Knowledge.normIndexCyclic` must be ascended to abelian Galois groups. The
ascent is not elementary: the elementary tower argument bounds the norm index above
by the degree, so the recorded content is the lower bound, and the classical routes
to it run through a reciprocity map (Neukirch's Frobenius-lift construction, the
source's choice) or the fundamental class. Recorded ahead of its proof.

## Main statements

* `normIndexAbelian` — `#(Kˣ ⧸ N Lˣ) = [L : K]` for finite abelian `L/K`; recorded
  ahead of its proof.

## Implementation notes

The statement mirrors `Atlas.Knowledge.normIndexCyclic` in its conclusion, with the
generator hypothesis replaced by Mathlib's `IsAbelianGalois` and the field variables
kept explicit, nothing being left to infer them from; the local-field structure on `L`
is hypothesized, as there. The cyclic case this claim generalizes is proved; consumers
needing only a cyclic-generated level should prefer it. The Lubin–Tate norm-subgroup
description consumes this claim through the index squeeze — both sides of that
equality have index exactly the level degree.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] [IsMixedCharLocalField L]
  [IsAbelianGalois K L]

/-- **The norm index of a finite abelian extension is its degree** — the cardinality
form of finite local reciprocity, the abelian ascent of
`Atlas.Knowledge.normIndexCyclic`. Claim recorded ahead of its proof
([Milne 2020, Chap. I, §1, Thm. 1.1, p.20][MilneCFT];
[Yamaguchi 2026, `LocalClassFieldTheory/Finite/UnramifiedConductor.lean:94`,
`card_normQuotient_eq_finrank_of_isAbelianGalois`][Yamaguchi2026]). -/
theorem normIndexAbelian :
    Nat.card (Kˣ ⧸ (Units.map (Algebra.norm K : L →* K)).range) =
      Module.finrank K L := by
  sorry

end Atlas.Knowledge
