import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.StandardLubinTateLevelField

/-!
# standard Lubin–Tate Galois description

The Galois structure of the level tower over a mixed-characteristic local field: the
level-`n + 1` field is abelian over `K`, with Galois group the finite unit-parameter
group `𝒪ˣ/U^{(n+1)}` — Milne's `(A/𝔪^{n+1})ˣ ≅ Gal(K_{π,n+1}/K)`, read through
`𝒪ˣ/(1 + 𝔪^{n+1}) ≅ (A/𝔪^{n+1})ˣ`. The integer-units higher unit subgroup is defined
here, proved a subgroup; the abelianness and the description are recorded ahead of their
proofs — they are local class field theory's torsion-action computation, which needs the
completed formal module.

## Main definitions

* `integerHigherUnitGroup` — `1 + 𝔪ⁿ` as a subgroup of `𝒪[K]ˣ`.

## Main statements

* `nonempty_standardLubinTateGaloisDescription` — `𝒪ˣ/U^{(n+1)} ≃* Gal(Lₙ/K)`;
  recorded ahead of its proof.
* `standardLubinTateLevelField_isAbelianGalois` — recorded ahead of its proof.

## Implementation notes

**Deliberate weakening, flagged in the route:** the source's description is *data* — the
specific action sending the unit parameter `u` to the automorphism moving the chosen
torsion point by `[u⁻¹]` (`LubinTate/FiniteLevel/LevelAbelian.lean:53`; the twist is
Milne's `φ_π(a)(λ) = [u⁻¹]_f(λ)` on p.40, two pages past the bare isomorphism), whose
construction needs the completed formal-module torsion theory. Atlas records abstract
isomorphy and the abelianness, not the pinned action; a future discharge that proves more
than `Nonempty` replaces this claim rather than extending it. The subgroup is on integer
units where `Atlas.Knowledge.higherUnitGroup` is on field units — the two sit on
opposite sides of `𝒪ˣ → Kˣ`, and this item does not identify them. The abelianness is a
plain recorded theorem, not an `instance`: a `sorry`-carried instance would let
downstream terms silently absorb `sorryAx`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- The **integer higher unit group** `1 + 𝔪ⁿ` as a subgroup of `𝒪[K]ˣ` — the
unit-parameter side of the level tower's Galois description
([Milne 2020, Chap. I, §3, Prop. 3.4 and Thm. 3.6 (b), p.38][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/FiniteParameters.lean:35`][Yamaguchi2026]). -/
def integerHigherUnitGroup (n : ℕ) : Subgroup 𝒪[K]ˣ where
  carrier := {u | (u : 𝒪[K]) - 1 ∈ IsLocalRing.maximalIdeal 𝒪[K] ^ n}
  one_mem' := by
    simp
  mul_mem' := by
    intro u v hu hv
    have key : ((u * v : 𝒪[K]ˣ) : 𝒪[K]) - 1 =
        (u : 𝒪[K]) * ((v : 𝒪[K]) - 1) + ((u : 𝒪[K]) - 1) := by
      push_cast
      ring
    rw [Set.mem_setOf_eq, key]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hv) hu
  inv_mem' := by
    intro u hu
    have key : ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) - 1 =
        -(((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * ((u : 𝒪[K]) - 1)) := by
      have hinv : ((u⁻¹ : 𝒪[K]ˣ) : 𝒪[K]) * (u : 𝒪[K]) = 1 := by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
      rw [mul_sub, hinv, mul_one]
      ring
    rw [Set.mem_setOf_eq, key]
    exact neg_mem (Ideal.mul_mem_left _ _ hu)

/-- The **unit-parameter description of the level Galois group**:
`𝒪ˣ/U^{(n+1)} ≃* Gal(Lₙ/K)`. Claim recorded ahead of its proof — and deliberately
weaker than the source, which constructs the specific `[u⁻¹]`-action on the chosen
torsion point ([Milne 2020, Chap. I, §3, Thm. 3.6 (b), p.38][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/LevelAbelian.lean:53`,
`standardLubinTateUnitParameterEquivGal`][Yamaguchi2026]). -/
theorem nonempty_standardLubinTateGaloisDescription {π : 𝒪[K]} (hπ : Irreducible π)
    (n : ℕ) :
    Nonempty ((𝒪[K]ˣ ⧸ integerHigherUnitGroup K (n + 1)) ≃*
      (standardLubinTateLevelField K hπ n ≃ₐ[K]
        standardLubinTateLevelField K hπ n)) := by
  sorry

/-- Every standard level field is **abelian Galois** over the base local field. Claim
recorded ahead of its proof, as a plain theorem rather than an instance
([Milne 2020, Chap. I, §3, Thm. 3.6 (b), p.38][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/LevelAbelian.lean:141`][Yamaguchi2026]). -/
theorem standardLubinTateLevelField_isAbelianGalois {π : 𝒪[K]} (hπ : Irreducible π)
    (n : ℕ) :
    IsAbelianGalois K (standardLubinTateLevelField K hπ n) := by
  sorry

end Atlas.Knowledge
