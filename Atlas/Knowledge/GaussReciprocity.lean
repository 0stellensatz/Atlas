import Mathlib
import Atlas.Knowledge.IsFinitePlaceHilbertSymbol
import Atlas.Knowledge.PowerResidueBadPlaceCorrection

/-!
# Gauss reciprocity

Gauss's quadratic reciprocity law in the form the class-field machinery derives it: for
odd coprime naturals, `J(a|b) · J(b|a) = (-1)^{a/2 · b/2}`, together with the evaluation
of the quadratic bad-place correction over `ℚ` that turns the general power reciprocity
law into it. The correction evaluation — the infinite place trivial on positives, the
dyadic Hilbert symbol contributing the classical sign — is recorded ahead of its proof;
the law itself is proved *from* Mathlib's `jacobiSym.quadratic_reciprocity`, which is how
the build certifies the CFT-derived form: a three-line derivation, not an identity — the
two statements differ by the coprimality hypothesis that cancels `J(b|a)²` — and nothing
formal yet ties this theorem to the recorded class-field chain, which is future work the
implementation notes lay out.

## Main statements

* `powerResidueBadPlaceCorrection_rat_two` — the dyadic correction is the classical
  sign; recorded ahead of its proof.
* `gaussReciprocity` — the law; proved from Mathlib.

## Implementation notes

The source derives `gaussReciprocity_nat_from_powerResidueReciprocity` from its general
law without invoking the library theorem
(`GlobalClassFieldTheory/Reciprocity/RationalQuadraticPowerResidueReciprocity.lean:1040`)
and identifies the two post hoc by proof irrelevance (`:1202`) — empty as a Lean
statement, so no identification theorem can carry that content here. What this file does
instead: it states the CFT-derived form — identical to the source's `:1040` down to the
`a / 2` Nat-division, which Mathlib's `jacobiSym.quadratic_reciprocity` also carries at
the pin — and proves it from the library theorem, with coprimality entering only to
cancel the square `J(b|a)^2`, which the library statement does not need. The derivation
*from class field theory* is recorded at statement level by the two neighbors —
`Atlas.Knowledge.powerResidueReciprocity` and the correction evaluation here (its source
form at `:980`) — but no Lean term yet connects them to `gaussReciprocity`; porting the
source's specialization (residue fields to `ZMod p`, the quadratic ideal symbol to the
Jacobi symbol) is the future work that would close that loop formally.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberTheorySymbols
open NumberField IsDedekindDomain

namespace Atlas.Knowledge

/-- The quadratic **bad-place correction over `ℚ`** of two odd naturals is the classical
sign `(-1)^{a/2 · b/2}`: the infinite factor is trivial on positives and the sole
exponent place is the dyadic one, whose wild Hilbert symbol Milne's formula
`(u2^r, v2^s)_2 = (-1)^{(u-1)/2·(v-1)/2 + r(v²-1)/8 + s(u²-1)/8}` evaluates. Claim
recorded ahead of its proof
([Milne 2020, Chap. VIII, §5, p.248][MilneCFT];
[Yamaguchi 2026,
`GlobalClassFieldTheory/Reciprocity/RationalQuadraticPowerResidueReciprocity.lean:980`]
[Yamaguchi2026]). -/
theorem powerResidueBadPlaceCorrection_rat_two
    (h : ∀ _v : HeightOneSpectrum (𝓞 ℚ), ℚˣ → ℚˣ → ℚˣ)
    (hh : ∀ v, IsFinitePlaceHilbertSymbol ℚ 2 v (h v))
    {a b : ℕ} (ha : Odd a) (hb : Odd b) (ua ub : ℚˣ)
    (hua : (ua : ℚ) = a) (hub : (ub : ℚ) = b) :
    powerResidueBadPlaceCorrection ℚ 2 two_ne_zero h ua ub =
      (-1 : ℚˣ) ^ (a / 2 * (b / 2)) := by
  sorry

/-- **Gauss reciprocity**: for odd coprime naturals,
`J(a|b) · J(b|a) = (-1)^{a/2 · b/2}` — the form the source derives from power-residue
reciprocity with the dyadic correction evaluated, proved here from Mathlib's
`jacobiSym.quadratic_reciprocity`; the statements differ by the coprimality that cancels
`J(b|a)²`, and the tie to the recorded class-field chain is future work
([Milne 2020, Chap. VIII, §5, pp.243, 248][MilneCFT];
[Yamaguchi 2026,
`GlobalClassFieldTheory/Reciprocity/RationalQuadraticPowerResidueReciprocity.lean:1040`,
identification at `:1202`][Yamaguchi2026]). -/
theorem gaussReciprocity {a b : ℕ} (ha : Odd a) (hb : Odd b) (hab : a.Coprime b) :
    J(a | b) * J(b | a) = (-1) ^ (a / 2 * (b / 2)) := by
  have hsq : J(b | a) ^ 2 = 1 := by
    apply jacobiSym.sq_one
    simpa [Int.gcd_natCast_natCast] using hab.symm
  calc
    J(a | b) * J(b | a) = (-1) ^ (a / 2 * (b / 2)) * J(b | a) * J(b | a) := by
      rw [jacobiSym.quadratic_reciprocity ha hb]
    _ = (-1) ^ (a / 2 * (b / 2)) * J(b | a) ^ 2 := by ring
    _ = (-1) ^ (a / 2 * (b / 2)) := by rw [hsq, mul_one]

end Atlas.Knowledge
