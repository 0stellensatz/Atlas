import Mathlib

/-!
# modulus

A modulus of a number field: a finitely supported choice of exponents at the finite places
together with a set of real places — the datum `𝔪 = ∏ 𝔭^{m(𝔭)} · ∏ v_ℝ` that ray class
theory filters the idele class group by. The structure is the literature's definition read
off directly: nonnegative exponents, almost all zero, real places squarefree, complex
places absent — the last two encoded by carrying the real places as a `Finset` rather than
as exponents. Divisibility of moduli is the componentwise order, and it is the order the
conductor of `Atlas.Knowledge.IsConductor` is least in.

## Main definitions

* `RealPlace` — the subtype of real infinite places.
* `Modulus` — finite part a `Finsupp` over `HeightOneSpectrum (𝓞 K)`, infinite part a
  `Finset` of real places, with its componentwise partial order.

## Implementation notes

The finite part is `HeightOneSpectrum (𝓞 K) →₀ ℕ` inlined — no separate finite-modulus
wrapper, unlike the source (`AlgebraicNumberTheory/RayClass/Basic.lean:24`,
`FullModulus.lean:26`), whose two-layer shape this item flattens. Only the partial order is
provided; lattice structure can come when something needs it. The structure does not
mention `[NumberField K]` in its fields, so statements about bare moduli omit it.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- A **real place**: an infinite place that is real
([Milne 2020, Chap. V, §1, Def. 1.3, pp.148–149][MilneCFT]). -/
abbrev RealPlace : Type _ := {v : InfinitePlace K // v.IsReal}

/-- A **modulus**: a finitely supported exponent at each finite place and a set of real
places — `𝔪 = ∏ 𝔭^{m(𝔭)} · ∏ v` with real places squarefree and complex places absent
([Milne 2020, Chap. V, §1, Def. 1.3, pp.148–149][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/RayClass/FullModulus.lean:26`][Yamaguchi2026]). -/
structure Modulus where
  /-- The finite prime-power part. -/
  finitePart : HeightOneSpectrum (𝓞 K) →₀ ℕ
  /-- The real places at which positivity is imposed. -/
  infinitePart : Finset (RealPlace K)

namespace Modulus

instance : PartialOrder (Modulus K) where
  le m n := m.finitePart ≤ n.finitePart ∧ m.infinitePart ⊆ n.infinitePart
  le_refl m := ⟨le_rfl, Finset.Subset.refl _⟩
  le_trans _ _ _ h h' := ⟨h.1.trans h'.1, h.2.trans h'.2⟩
  le_antisymm m n h h' := by
    cases m
    cases n
    simp only [Modulus.mk.injEq]
    exact ⟨le_antisymm h.1 h'.1, Finset.Subset.antisymm h.2 h'.2⟩

omit [NumberField K] in
/-- Divisibility of moduli is the componentwise order
([Milne 2020, Chap. V, §1, p.149][MilneCFT]). -/
theorem le_def {m n : Modulus K} :
    m ≤ n ↔ m.finitePart ≤ n.finitePart ∧ m.infinitePart ⊆ n.infinitePart :=
  Iff.rfl

end Modulus

end Atlas.Knowledge
