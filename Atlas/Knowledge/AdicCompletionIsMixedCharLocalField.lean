import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# adic completion as mixed-characteristic local field

The completion of a number field at a finite place, carried into the local layer's
signature: the canonical valuative relation induced by the `v`-adic valuation is installed
as an instance, pinned to that valuation by its compatibility certificate, and the field is
proved to have characteristic zero. What remains — that the completion is a
mixed-characteristic local field — is recorded ahead of its proof, and it owes three
obligations: that the `Valued` topology is the valuative one, that the valuation is
nontrivial, and local compactness, of which the last is the only hard one. This item is
the junction the reciprocity phase crosses every time it evaluates a local notion at a
place of a global field; without it, `Atlas.Knowledge.IsLocalHilbertSymbol` cannot even be
stated at a completion.

## Main definitions

* `adicCompletionValuativeRel`, `adicCompletionValuedCompatible` — the canonical
  `ValuativeRel` on `v.adicCompletion K` and its pinning to `Valued.v`.

## Main statements

* `adicCompletion_charZero` — characteristic zero; proved.
* `adicCompletion_isMixedCharLocalField` — the local-field certificate; recorded ahead of
  its proof.

## Implementation notes

The valuative relation is `ValuativeRel.ofValuation` applied to the completion's `Valued`
structure, and the `Valuation.Compatible` instance is what pins the relation to the
`v`-adic valuation rather than an arbitrary one — together they are the canonical bridge
Mathlib's own `Valued`-to-`ValuativeRel` migration uses, so no orphan structure is
invented. At the pinned Mathlib, `IsNonarchimedeanLocalField` ships with no instance at
all — the `ℚ_[p]` model is Atlas's own, `Atlas.Knowledge.PadicIsMixedCharLocalField` — and
none of its three components synthesizes for the completion: `IsValuativeTopology` (Mathlib carries
it only for `WithVal` and for the `ValuativeRel`-induced topology, neither of which fires here —
its own TODO at `Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean:50` says as much),
`ValuativeRel.IsNontrivial`, and `LocallyCompactSpace`. The first two are routine facts about the
`Valued` structure; the compactness is Serre's Proposition 1 — locally compact iff complete with
finite residue field — and is the real content. The source builds the same certificate over its
normed completion from its own machinery
(`GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/Construction.lean:294`, certificate at
`:305`); Atlas records the claim on Mathlib's `Valued` completion instead and lets the backlog
carry it.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open NumberField IsDedekindDomain
open scoped WithZero

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The canonical valuative relation on the completion at a finite place, induced by the
`v`-adic valuation ([Serre 1979, Chap. II, §1, p.27][Serre1979];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/Construction.lean:294`]
[Yamaguchi2026]). -/
noncomputable instance adicCompletionValuativeRel : ValuativeRel (v.adicCompletion K) :=
  ValuativeRel.ofValuation (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

/-- The valuative relation is the one of the `v`-adic valuation — the compatibility
certificate that keeps the instance canonical. -/
instance adicCompletionValuedCompatible :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Compatible :=
  Valuation.Compatible.ofValuation _

/-- The completion of a number field has characteristic zero — the mixed-characteristic
half that is provable now, through the rational algebra structure. -/
instance adicCompletion_charZero : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion K)).injective

/-- The completion of a number field at a finite place is a mixed-characteristic local
field. Three obligations remain open at the pinned Mathlib — the `Valued` topology is the
valuative one, the valuation is nontrivial, and local compactness — the first two routine,
the last Serre's Proposition 1 (a complete discretely valued field is locally compact iff
its residue field is finite) plus the finiteness of that residue field; recorded ahead of
its proof ([Serre 1979, Chap. II, §1, Prop. 1, p.27][Serre1979];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/Construction.lean:305`]
[Yamaguchi2026]). -/
theorem adicCompletion_isMixedCharLocalField :
    IsMixedCharLocalField (v.adicCompletion K) := by
  sorry

end Atlas.Knowledge
