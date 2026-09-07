import Mathlib
import Atlas.Knowledge.IdeleClassGroup

/-!
# finite-place idele

The one-place inclusion into the idele group: a unit of one finite completion, placed at
its own coordinate with `1` everywhere else — the idele Milne writes `(1, …, 1, a, 1, …)`.
It is the mouth through which local data enters global statements: the arithmetic
normalization of `Atlas.Knowledge.IsGlobalArtinMap` speaks of the class of a one-place
uniformizer idele, and that class is this map followed by the projection to the idele
class group. Everything here is proved; nothing is recorded.

## Main definitions

* `finitePlaceIdele` — `(v.adicCompletion K)ˣ →* 𝕀_K`.
* `finitePlaceIdeleClass` — the same, followed by the class-group projection.

## Main statements

* `finitePlaceIdele_fst`, `finitePlaceIdele_apply_self`, `finitePlaceIdele_apply_of_ne` —
  the components: `1` in the archimedean block, the prescribed unit at `v`, `1` at every
  other finite place.

## Implementation notes

The value function is a dependent `if`-update, `x` at `v` and `1` elsewhere; the
restricted-product membership is cofinitely trivial because `1` is everywhere integral.
The construction is a port of the finite half of the source's single-place module
(`AlgebraicNumberTheory/Idele/SinglePlace.lean`), with the classical `open Classical`
narrowed to the value function. The component lemmas read the value function back off the
idele; they are what the one-place congruence steps of
`Atlas.Knowledge.LocalHigherUnitClassSubgroup` split an idele with.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace Atlas.Knowledge

variable {K : Type*} [Field K] [NumberField K]

open Classical in
/-- The dependent local value which is `x` at `v` and `1` elsewhere. -/
private noncomputable def finitePlaceValue (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) (w : HeightOneSpectrum (𝓞 K)) : (w.adicCompletion K)ˣ :=
  if h : w = v then h.symm ▸ x else 1

@[simp]
private theorem finitePlaceValue_same (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : finitePlaceValue v x v = x := by
  simp [finitePlaceValue]

@[simp]
private theorem finitePlaceValue_of_ne (v w : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) (h : w ≠ v) : finitePlaceValue v x w = 1 := by
  simp [finitePlaceValue, h]

/-- The **finite-place idele**: the idele whose `v`-component is prescribed and whose other
components are `1` — Milne's `(1, …, 1, a, 1, …)`
([Milne 2020, Chap. V, §4, 4.3, p.171][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:204`). -/
noncomputable def finitePlaceIdele (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* IdeleGroup K where
  toFun x :=
    (1,
      ⟨finitePlaceValue v x, by
        have hAway : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, w ≠ v := by
          rw [Filter.eventually_cofinite]
          simp
        filter_upwards [hAway] with w hw
        rw [finitePlaceValue_of_ne v w x hw]
        exact Subgroup.one_mem _⟩)
  map_one' := by
    apply Prod.ext
    · rfl
    · apply RestrictedProduct.ext
      intro w
      by_cases hw : w = v
      · subst w
        simp
      · simp [finitePlaceValue_of_ne v w 1 hw]
  map_mul' x y := by
    apply Prod.ext
    · simp
    · apply RestrictedProduct.ext
      intro w
      by_cases hw : w = v
      · subst w
        simp
      · simp [finitePlaceValue_of_ne v w x hw, finitePlaceValue_of_ne v w y hw,
          finitePlaceValue_of_ne v w (x * y) hw]

/-- The finite-place idele has archimedean block `1`
([Milne 2020, Chap. V, §4, 4.3, p.171][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:261`). -/
theorem finitePlaceIdele_fst (v : HeightOneSpectrum (𝓞 K)) (x : (v.adicCompletion K)ˣ) :
    (finitePlaceIdele v x).1 = 1 :=
  rfl

/-- At its own place the finite-place idele is the prescribed unit
([Milne 2020, Chap. V, §4, 4.3, p.171][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:242`). -/
@[simp]
theorem finitePlaceIdele_apply_self (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) : (finitePlaceIdele v x).2 v = x :=
  finitePlaceValue_same v x

/-- At every other finite place the finite-place idele is `1`
([Milne 2020, Chap. V, §4, 4.3, p.171][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:251`). -/
@[simp]
theorem finitePlaceIdele_apply_of_ne (v w : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) (h : w ≠ v) : (finitePlaceIdele v x).2 w = 1 :=
  finitePlaceValue_of_ne v w x h

/-- The **finite-place idele class**: one local unit, made global, made a class
([Milne 2020, Chap. V, §4, 4.3, p.171][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:271`). -/
noncomputable def finitePlaceIdeleClass (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* IdeleClassGroup K :=
  (QuotientGroup.mk' (principalIdeleSubgroup K)).comp (finitePlaceIdele v)

end Atlas.Knowledge

end
