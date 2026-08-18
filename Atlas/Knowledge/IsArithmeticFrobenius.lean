import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LowerRamificationGroup

/-!
# arithmetic Frobenius

The arithmetic Frobenius of an extension of a mixed-characteristic local field, as a
predicate: `σ : L ≃ₐ[K] L` is an arithmetic Frobenius when it satisfies the Frobenius
substitution congruence `σ x ≡ x ^ q` on the integral closure of `𝒪[K]` in `L` modulo its
Jacobson radical, `q` the cardinality of the residue field of `K`. This is the literature's
definition read literally — no residue-action isomorphism is constructed to state it — and it
is the element the unramified normalization of the Artin map
(`Atlas.Knowledge.IsFrobeniusNormalized`) points at. Over an unramified extension the
predicate pins a unique element, which generates the Galois group; those are the recorded
claims.

## Main definitions

* `IsArithmeticFrobenius` — the Frobenius substitution congruence.

## Main statements

* `isArithmeticFrobenius_unique` / `exists_isArithmeticFrobenius` — over an unramified
  extension (trivial inertia, `G_0 = ⊥`) there is exactly one arithmetic Frobenius; both
  recorded ahead of their proofs.
* `orderOf_of_isArithmeticFrobenius` / `zpowers_of_isArithmeticFrobenius` — its order is the
  degree and it generates, recorded ahead of their proofs.

## Implementation notes

The carrier is `integralClosure 𝒪[K] L` with congruence modulo `Ideal.jacobson ⊥`, the
layer's uniform encoding (`Atlas.Knowledge.LowerRamificationGroup`), and unramifiedness is
rendered Atlas-natively as `lowerRamificationGroup K L 0 = ⊥`; the identification with the
ramification-index-one class of the literature is `e = |G_0|`,
`Atlas.Knowledge.MapMaximalIdealEqPowCardInertia`. The predicate is stated for any algebraic
extension and owns its junk regions: without unramifiedness the congruence pins σ only up to
inertia — uniqueness genuinely needs `G_0 = ⊥` — and the exponent is `Nat.card 𝓀[K]`, the
*base* residue cardinality, so nothing here collapses when the residue extension is proper.
The source repository builds its Frobenius through a residue-action equivalence instead
(`LocalFieldTheory/NonarchimedeanLocalField/UnramifiedFrobenius.lean:119`) and proves that
it satisfies the equivalent residue-field form of the congruence (`:167`).

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The **arithmetic Frobenius** predicate: `σ` satisfies the Frobenius substitution
congruence `σ x ≡ x ^ q` modulo the Jacobson radical on the integral closure of `𝒪[K]` in
`L`, where `q = Nat.card 𝓀[K]`
([Milne 2020, Chap. I, §1, p.20][MilneCFT];
[Yamaguchi 2026, `LocalFieldTheory/NonarchimedeanLocalField/UnramifiedFrobenius.lean:167`]
[Yamaguchi2026]). -/
def IsArithmeticFrobenius (σ : L ≃ₐ[K] L) : Prop :=
  ∀ x : integralClosure 𝒪[K] L,
    galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ x - x ^ Nat.card 𝓀[K] ∈
      Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L))

/-- Over an unramified extension the arithmetic Frobenius is unique: two automorphisms
satisfying the substitution congruence agree once the inertia group is trivial. Claim
recorded ahead of its proof ([Milne 2020, Chap. I, §1, p.20][MilneCFT]). -/
theorem isArithmeticFrobenius_unique [FiniteDimensional K L]
    (h : lowerRamificationGroup K L 0 = ⊥) {σ τ : L ≃ₐ[K] L}
    (hσ : IsArithmeticFrobenius K L σ) (hτ : IsArithmeticFrobenius K L τ) : σ = τ := by
  sorry

/-- Over a finite Galois unramified extension an arithmetic Frobenius exists. Claim recorded
ahead of its proof ([Milne 2020, Chap. I, §1, p.20][MilneCFT]). -/
theorem exists_isArithmeticFrobenius [FiniteDimensional K L] [IsGalois K L]
    (h : lowerRamificationGroup K L 0 = ⊥) :
    ∃ σ : L ≃ₐ[K] L, IsArithmeticFrobenius K L σ := by
  sorry

/-- The arithmetic Frobenius of a finite Galois unramified extension has order the degree —
the Galois group is cyclic of order `[L : K]`, carried by the residue extension. Claim
recorded ahead of its proof ([Milne 2020, Chap. I, §1, p.20][MilneCFT]). -/
theorem orderOf_of_isArithmeticFrobenius [FiniteDimensional K L] [IsGalois K L]
    (h : lowerRamificationGroup K L 0 = ⊥) {σ : L ≃ₐ[K] L}
    (hσ : IsArithmeticFrobenius K L σ) : orderOf σ = Module.finrank K L := by
  sorry

/-- The arithmetic Frobenius of a finite Galois unramified extension generates the Galois
group. Claim recorded ahead of its proof
([Milne 2020, Chap. I, §1, p.20][MilneCFT];
[Yamaguchi 2026, `LocalFieldTheory/NonarchimedeanLocalField/UnramifiedFrobenius.lean:377`]
[Yamaguchi2026]). -/
theorem zpowers_of_isArithmeticFrobenius [FiniteDimensional K L] [IsGalois K L]
    (h : lowerRamificationGroup K L 0 = ⊥) {σ : L ≃ₐ[K] L}
    (hσ : IsArithmeticFrobenius K L σ) : Subgroup.zpowers σ = ⊤ := by
  sorry

end Atlas.Knowledge
