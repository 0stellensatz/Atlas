import Mathlib

/-!
# infinite-place Hilbert symbol

The Hilbert symbol of two global units at an infinite place of a number field — the
archimedean factor of the product formula, and unlike its finite-place counterpart an
honest definition: the completion at a complex place has no nontrivial abelian extension
and at a real place exactly one, so the symbol is `-1` precisely in the quadratic case at
a real place with both arguments negative, and `1` everywhere else. Everything here is
proved; nothing is recorded.

## Main definitions

* `infinitePlaceHilbertSymbol` — `(a, b)_v ∈ Kˣ` for `v` an infinite place.

## Main statements

* `infinitePlaceHilbertSymbol_pow_eq_one` — the value is an `n`-th root of unity.
* `infinitePlaceHilbertSymbol_eq_one_of_isComplex`,
  `infinitePlaceHilbertSymbol_eq_one_of_ne_two` — triviality off the real quadratic case.
* `infinitePlaceHilbertSymbol_apply_of_isReal` — the real-place evaluation.

## Implementation notes

The value lives in `Kˣ`, matching the finite-place layer, with the root-of-unity fact a
lemma rather than a bundled codomain; at `n = 2` the value `-1` is genuinely an `n`-th
root, and every other branch is `1`. Negativity is read through Mathlib's
`InfinitePlace.embedding_of_isReal`, so the definition is a three-way `if` over `n = 2`,
reality of the place, and the signs — the source's shape exactly
(`GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/InfinitePlace.lean:28`), with its
`nthRootsSubgroup` codomain flattened. Milne evaluates the real symbol as
`(a,b)_v = 1 ⟺ a > 0 or b > 0`, the form `infinitePlaceHilbertSymbol_apply_of_isReal`
states.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open NumberField

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

open scoped Classical in
/-- The **infinite-place Hilbert symbol**: `-1` when the exponent is `2`, the place is
real, and both arguments are negative there; `1` otherwise
([Milne 2020, Chap. VIII, §5, p.248][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/InfinitePlace.lean:28`). -/
noncomputable def infinitePlaceHilbertSymbol (n : ℕ) (v : InfinitePlace K)
    (a b : Kˣ) : Kˣ :=
  if n = 2 ∧ ∃ hv : v.IsReal,
      InfinitePlace.embedding_of_isReal hv (a : K) < 0 ∧
      InfinitePlace.embedding_of_isReal hv (b : K) < 0 then
    -1
  else
    1

variable {K}

omit [NumberField K] in
/-- The value of the infinite-place symbol is an `n`-th root of unity
([Milne 2020, Chap. VIII, §5, p.248][MilneCFT]). -/
theorem infinitePlaceHilbertSymbol_pow_eq_one (n : ℕ) (v : InfinitePlace K)
    (a b : Kˣ) : infinitePlaceHilbertSymbol K n v a b ^ n = 1 := by
  rw [infinitePlaceHilbertSymbol]
  split_ifs with h
  · rw [h.1]
    ext
    simp
  · exact one_pow n

omit [NumberField K] in
/-- A complex place contributes the trivial factor
([Milne 2020, Chap. VIII, §5, p.248][MilneCFT];
Yamaguchi 2026,
`GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/InfinitePlace.lean:47`). -/
theorem infinitePlaceHilbertSymbol_eq_one_of_isComplex (n : ℕ) {v : InfinitePlace K}
    (hv : v.IsComplex) (a b : Kˣ) : infinitePlaceHilbertSymbol K n v a b = 1 := by
  rw [infinitePlaceHilbertSymbol, if_neg]
  rintro ⟨-, hreal, -⟩
  exact (InfinitePlace.not_isReal_iff_isComplex.mpr hv) hreal

omit [NumberField K] in
/-- Away from the quadratic exponent the infinite factor is trivial — `μₙ ⊄ ℝ` past
`n = 2`, so only the quadratic case can see a real place (Yamaguchi 2026,
`GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/InfinitePlace.lean:59`). -/
theorem infinitePlaceHilbertSymbol_eq_one_of_ne_two {n : ℕ} (hn : n ≠ 2)
    (v : InfinitePlace K) (a b : Kˣ) : infinitePlaceHilbertSymbol K n v a b = 1 := by
  rw [infinitePlaceHilbertSymbol, if_neg]
  rintro ⟨h2, -⟩
  exact hn h2

omit [NumberField K] in
/-- The real-place evaluation of the quadratic symbol: `-1` exactly when both arguments
are negative — Milne's `(a,b)_v = 1 ⟺ a > 0` or `b > 0`
([Milne 2020, Chap. VIII, §5, p.248][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/InfinitePlace.lean:67`). -/
theorem infinitePlaceHilbertSymbol_apply_of_isReal {v : InfinitePlace K}
    (hv : v.IsReal) (a b : Kˣ) :
    infinitePlaceHilbertSymbol K 2 v a b =
      if InfinitePlace.embedding_of_isReal hv (a : K) < 0 ∧
          InfinitePlace.embedding_of_isReal hv (b : K) < 0 then
        -1
      else
        1 := by
  rw [infinitePlaceHilbertSymbol]
  by_cases h : InfinitePlace.embedding_of_isReal hv (a : K) < 0 ∧
      InfinitePlace.embedding_of_isReal hv (b : K) < 0
  · rw [if_pos h, if_pos ⟨rfl, hv, h⟩]
  · rw [if_neg h, if_neg]
    rintro ⟨-, hv', ha', hb'⟩
    exact h ⟨ha', hb'⟩

end Atlas.Knowledge
