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

## Implementation notes

The value function is a dependent `if`-update, `x` at `v` and `1` elsewhere; the
restricted-product membership is cofinitely trivial because `1` is everywhere integral.
The construction is a port of the finite half of the source's single-place module
(`AlgebraicNumberTheory/Idele/SinglePlace.lean`), with the classical `open Classical`
narrowed to the value function.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
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
([Milne 2020, Chap. V, §4, 4.3, p.171][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/SinglePlace.lean:54`][Yamaguchi2026]). -/
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

/-- The **finite-place idele class**: one local unit, made global, made a class
([Milne 2020, Chap. V, §4, 4.3, p.171][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/SinglePlace.lean:172`][Yamaguchi2026]). -/
noncomputable def finitePlaceIdeleClass (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* IdeleClassGroup K :=
  (QuotientGroup.mk' (principalIdeleSubgroup K)).comp (finitePlaceIdele v)

end Atlas.Knowledge

end
