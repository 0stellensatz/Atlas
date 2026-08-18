import Mathlib
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.IsArithmeticFrobenius

/-!
# Frobenius-normalized reciprocity map

The unramified normalization of local class field theory as a predicate on candidate
reciprocity maps: `ρ : Kˣ →* (L ≃ₐ[K] L)` is Frobenius-normalized when
`ρ x = σ ^ v (x)` for every arithmetic Frobenius `σ` of `L` over `K`, `v` the normalized
valuation `Atlas.Knowledge.normalizedValuation`. Read at a uniformizer this is
uniformizer ↦ arithmetic Frobenius — the commuting square of the reciprocity map against the
normalized valuation, the *arithmetic* normalization of [Serre1979], [MilneCFT], and
[Hyeon2025]. That the normalization pins the map is the two-line `isFrobeniusNormalized_unique`
below — this box's slogan, machine-checked and sorry-free.

## Main definitions

* `IsFrobeniusNormalized` — `ρ x = σ ^ v (x)` against every arithmetic Frobenius.

## Main statements

* `isFrobeniusNormalized_unique` — the normalization pins the map: two Frobenius-normalized
  maps agree as soon as one arithmetic Frobenius exists.
* `IsFrobeniusNormalized.apply_integerUnit` — integer units land at the identity.

## Implementation notes

The predicate quantifies over every arithmetic Frobenius rather than choosing one, so it is
total and choice-free; over an extension with no Frobenius it is vacuous, and the junk is
owned by the hypotheses of its consumers. It is stated `Gal`-valued for the unramified floor
— the group there is cyclic, so nothing is lost against an `Abelianization`-valued form, and
the transcription into one is `Abelianization.of` applied pointwise. Existence of a
Frobenius-normalized map with the right kernel is not this item's claim: it is part of the
full characterization `Atlas.Knowledge.IsLocalReciprocity`, whose `frobenius` field is this
square read on roots of unity one floor up. The source repository proves the square for its
constructed map (`Finite/LocalReciprocity/UnramifiedNormalization.lean:383, :479`) — against
its inverse-standard valuation, so its uniformizer-to-Frobenius statement is literally about
the *inverse* uniformizer (`:437`); the port into this vocabulary composes with the negation
recorded in `Atlas.Knowledge.NormalizedValuation`.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic
  local fields*, J. London Math. Soc. **112** (2025), e70402.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The **Frobenius normalization** predicate on a candidate reciprocity map:
`ρ x = σ ^ v (x)` for every arithmetic Frobenius `σ`, `v` the normalized valuation — at a
uniformizer, uniformizer ↦ arithmetic Frobenius
([Serre 1979, Chap. XIII, §4, Prop. 13, p.197][Serre1979];
[Milne 2020, Chap. I, §1, Thm. 1.1 (a), p.20][MilneCFT];
[Hyeon 2025, §3, p.10][Hyeon2025];
[Yamaguchi 2026, `Finite/LocalReciprocity/UnramifiedNormalization.lean:383`, valuation sign
reversed][Yamaguchi2026]). -/
def IsFrobeniusNormalized (ρ : Kˣ →* (L ≃ₐ[K] L)) : Prop :=
  ∀ σ : L ≃ₐ[K] L, IsArithmeticFrobenius K L σ →
    ∀ x : Kˣ, ρ x = σ ^ normalizedValuation K x

/-- The unramified normalization pins the reciprocity map: as soon as one arithmetic
Frobenius exists, two Frobenius-normalized maps agree
([Milne 2020, Chap. I, §1, Thm. 1.1, p.20][MilneCFT]). -/
theorem isFrobeniusNormalized_unique {σ : L ≃ₐ[K] L} (hσ : IsArithmeticFrobenius K L σ)
    {ρ₁ ρ₂ : Kˣ →* (L ≃ₐ[K] L)} (h₁ : IsFrobeniusNormalized K L ρ₁)
    (h₂ : IsFrobeniusNormalized K L ρ₂) : ρ₁ = ρ₂ := by
  ext x
  rw [h₁ σ hσ x, h₂ σ hσ x]

/-- A Frobenius-normalized map sends the units of the integer ring to the identity: their
normalized valuation is `0` ([Serre 1979, Chap. XIII, §4, p.198][Serre1979]). -/
theorem IsFrobeniusNormalized.apply_integerUnit {ρ : Kˣ →* (L ≃ₐ[K] L)}
    (hρ : IsFrobeniusNormalized K L ρ) {σ : L ≃ₐ[K] L} (hσ : IsArithmeticFrobenius K L σ)
    (u : 𝒪[K]ˣ) : ρ (Units.map (algebraMap 𝒪[K] K).toMonoidHom u) = 1 := by
  rw [hρ σ hσ, normalizedValuation_eq_zero_of_valuation_eq_one, zpow_zero]
  exact Valuation.Integers.valuation_unit (Valuation.integer.integers (valuation K)) u

end Atlas.Knowledge
