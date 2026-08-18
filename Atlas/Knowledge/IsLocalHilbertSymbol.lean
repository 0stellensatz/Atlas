import Mathlib
import Atlas.Knowledge.IsLocalReciprocity

/-!
# local Hilbert symbol

The `n`-th Hilbert symbol of a mixed-characteristic local field, as a characterization:
`IsLocalHilbertSymbol K n h` says the function `h : Kˣ → Kˣ → Kˣ` is computed from some
absolute reciprocity map — every lift of `φ (b)` moves every `n`-th root `β` of `a` in the
algebraic closure by the factor `h a b`. This is the literature's `(a, b) = s_b (α) / α`,
`α ^ n = a`, read pointwise with `Atlas.Knowledge.IsLocalReciprocity` in the norm-residue
slot; the symbol itself is as unconstructible here as the Artin map it is built from, so the
predicate is the item. What the characterization already pins, it pins sorry-free: the values
are `n`-th roots of unity, the symbol is bimultiplicative, both slots kill `n`-th powers, and
two symbols for the same `n` agree — everything provable now is proved below, and only
existence is recorded ahead of its proof.

## Main definitions

* `IsLocalHilbertSymbol` — `h` is an `n`-th Hilbert symbol for some absolute reciprocity map.

## Main statements

* `exists_isLocalHilbertSymbol` — existence, recorded ahead of its proof.
* `IsLocalHilbertSymbol.pow_eq_one`, `.mul_left`, `.mul_right` — the values are `n`-th roots
  of unity and the symbol is bimultiplicative; proved from the characterization alone.
* `IsLocalHilbertSymbol.pow_left_eq_one`, `.pow_right_eq_one` — `n`-th powers die in either
  slot; the trivial halves of nondegeneracy, proved.
* `IsLocalHilbertSymbol.unique` — the characterization pins the symbol; proved modulo the
  recorded uniqueness of the reciprocity map.

## Implementation notes

The slot convention is Serre's and Milne's, and it matters: the norm-residue symbol of the
*second* argument acts on the roots of the *first*. The read repository builds its symbol the
other way around (`LocalClassFieldTheory/Kummer/LocalHilbertSymbol.lean:44`) *and* composes
with the inverse-normalized Artin map recorded in `Atlas.Knowledge.NormalizedValuation`'s
notes — two departures that cancel through skew-symmetry, so its symbol is equal to the one
characterized here. The carrier is a bare curried function rather than a bundled bilinear
map: the predicate pins values only where lifts and roots exist, and bimultiplicativity is
derived, not imposed. The `μ_n ⊂ K` hypothesis of the literature is not baked into the
predicate; the claims that need it carry it. At `n = 0` there are no roots and the predicate
degenerates, which is why the pinning statements carry `n ≠ 0`. `unique` consumes the
recorded claim `Atlas.Knowledge.IsLocalReciprocity.unique`, and the axiom audit tracks that
inheritance — the proof is genuine, the taint deliberate.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- The **local Hilbert symbol** characterization of `h : Kˣ → Kˣ → Kˣ`: some absolute
reciprocity map `φ` has every lift of `φ (b)` multiplying every `n`-th root of `a` in the
algebraic closure by `h a b` — the norm-residue symbol of the second slot acting on the
radicals of the first
([Serre 1979, Chap. XIV, §2, p.206 and Prop. 6, p.208][Serre1979];
[Milne 2020, Chap. III, §4, Rem. 4.5, p.114][MilneCFT];
[Yamaguchi 2026, `LocalClassFieldTheory/Kummer/LocalHilbertSymbol.lean:44`, slots transposed
and normalization inverted, equal by skew-symmetry][Yamaguchi2026]). -/
def IsLocalHilbertSymbol (n : ℕ) (h : Kˣ → Kˣ → Kˣ) : Prop :=
  ∃ φ : Kˣ →* Field.absoluteGaloisGroupAbelianization K, IsLocalReciprocity K φ ∧
    ∀ (a b : Kˣ) (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
      (QuotientGroup.mk (σ : Field.absoluteGaloisGroup K) :
        Field.absoluteGaloisGroupAbelianization K) = φ b →
      ∀ β : AlgebraicClosure K, β ^ n = algebraMap K (AlgebraicClosure K) (a : K) →
        σ β = algebraMap K (AlgebraicClosure K) ((h a b : Kˣ) : K) * β

/-- An `n`-th Hilbert symbol exists once `K` contains the `n`-th roots of unity. Claim
recorded ahead of its proof ([Serre 1979, Chap. XIV, §2, p.206][Serre1979];
[Yamaguchi 2026, `LocalClassFieldTheory/Kummer/LocalHilbertSymbol.lean:44`][Yamaguchi2026]). -/
theorem exists_isLocalHilbertSymbol (n : ℕ) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) :
    ∃ h : Kˣ → Kˣ → Kˣ, IsLocalHilbertSymbol K n h := by
  sorry

namespace IsLocalHilbertSymbol

variable {K}

omit [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K] in
private theorem exists_lift (g : Field.absoluteGaloisGroupAbelianization K) :
    ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      (QuotientGroup.mk (σ : Field.absoluteGaloisGroup K) :
        Field.absoluteGaloisGroupAbelianization K) = g := by
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk_surjective g
  exact ⟨σ, rfl⟩

omit [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K] in
private theorem exists_root (a : Kˣ) {n : ℕ} (hn : n ≠ 0) :
    ∃ β : AlgebraicClosure K, β ^ n = algebraMap K (AlgebraicClosure K) (a : K) ∧ β ≠ 0 := by
  obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq
    (algebraMap K (AlgebraicClosure K) (a : K)) (Nat.pos_of_ne_zero hn)
  refine ⟨β, hβ, fun h0 => ?_⟩
  rw [h0, zero_pow hn] at hβ
  exact (map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr a.ne_zero hβ.symm

omit [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K] in
private theorem units_eq_of_smul {x y : Kˣ} {β : AlgebraicClosure K} (hβ : β ≠ 0)
    (hxy : algebraMap K (AlgebraicClosure K) (x : K) * β
      = algebraMap K (AlgebraicClosure K) (y : K) * β) : x = y :=
  Units.ext ((algebraMap K (AlgebraicClosure K)).injective (mul_right_cancel₀ hβ hxy))

variable {n : ℕ} {h : Kˣ → Kˣ → Kˣ}

/-- The values of a Hilbert symbol are `n`-th roots of unity
([Serre 1979, Chap. XIV, §2, p.208][Serre1979]). -/
theorem pow_eq_one (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0) (a b : Kˣ) :
    h a b ^ n = 1 := by
  obtain ⟨φ, -, hspec⟩ := hh
  obtain ⟨σ, hσ⟩ := exists_lift (φ b)
  obtain ⟨β, hβ, hβ0⟩ := exists_root a hn
  have h1 := hspec a b σ hσ β hβ
  have h2 : σ β ^ n = β ^ n := by rw [← map_pow, hβ, AlgEquiv.commutes]
  rw [h1, mul_pow, ← map_pow] at h2
  have h3 := (mul_left_eq_self₀.mp h2).resolve_right (pow_ne_zero n hβ0)
  have h4 : ((h a b : Kˣ) : K) ^ n = 1 := by
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [map_pow] at h3
    rw [map_pow, map_one]
    exact h3
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h4)

/-- The Hilbert symbol is multiplicative in its first slot: the roots multiply
([Serre 1979, Chap. XIV, §2, Prop. 7 i, p.208][Serre1979];
[Milne 2020, Chap. III, §4, Thm. 4.4 (a), p.113][MilneCFT]). -/
theorem mul_left (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0) (a a' b : Kˣ) :
    h (a * a') b = h a b * h a' b := by
  obtain ⟨φ, -, hspec⟩ := hh
  obtain ⟨σ, hσ⟩ := exists_lift (φ b)
  obtain ⟨β, hβ, hβ0⟩ := exists_root a hn
  obtain ⟨β', hβ', hβ'0⟩ := exists_root a' hn
  have hββ' : (β * β') ^ n = algebraMap K (AlgebraicClosure K) ((a * a' : Kˣ) : K) := by
    rw [mul_pow, hβ, hβ', Units.val_mul, map_mul]
  have h1 := hspec a b σ hσ β hβ
  have h2 := hspec a' b σ hσ β' hβ'
  have h3 := hspec (a * a') b σ hσ (β * β') hββ'
  rw [map_mul, h1, h2] at h3
  apply units_eq_of_smul (mul_ne_zero hβ0 hβ'0)
  rw [← h3, Units.val_mul, map_mul]
  ring

/-- The Hilbert symbol is multiplicative in its second slot: the lifts multiply
([Serre 1979, Chap. XIV, §2, Prop. 7 ii, p.208][Serre1979];
[Milne 2020, Chap. III, §4, Thm. 4.4 (a), p.113][MilneCFT]). -/
theorem mul_right (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0) (a b b' : Kˣ) :
    h a (b * b') = h a b * h a b' := by
  obtain ⟨φ, -, hspec⟩ := hh
  obtain ⟨σ, hσ⟩ := exists_lift (φ b)
  obtain ⟨σ', hσ'⟩ := exists_lift (φ b')
  obtain ⟨β, hβ, hβ0⟩ := exists_root a hn
  have hσσ' : (QuotientGroup.mk
      ((σ * σ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :
        Field.absoluteGaloisGroup K) :
      Field.absoluteGaloisGroupAbelianization K) = φ (b * b') := by
    rw [map_mul, ← hσ, ← hσ']
    rfl
  have h1 := hspec a b σ hσ β hβ
  have h2 := hspec a b' σ' hσ' β hβ
  have h3 := hspec a (b * b') (σ * σ') hσσ' β hβ
  rw [AlgEquiv.mul_apply, h2, map_mul, AlgEquiv.commutes, h1] at h3
  apply units_eq_of_smul hβ0
  rw [← h3, Units.val_mul, map_mul]
  ring

/-- An `n`-th power in the first slot kills the symbol: its root is already rational, so
every lift fixes it. The trivial half of left nondegeneracy, and the only pinning statement
that survives `n = 0` ([Serre 1979, Chap. XIV, §2, Prop. 7 vi, p.208][Serre1979]). -/
theorem pow_left_eq_one (hh : IsLocalHilbertSymbol K n h) (c b : Kˣ) :
    h (c ^ n) b = 1 := by
  obtain ⟨φ, -, hspec⟩ := hh
  obtain ⟨σ, hσ⟩ := exists_lift (φ b)
  have hβ : (algebraMap K (AlgebraicClosure K) (c : K)) ^ n
      = algebraMap K (AlgebraicClosure K) ((c ^ n : Kˣ) : K) := by
    rw [Units.val_pow_eq_pow_val, map_pow]
  have h1 := hspec (c ^ n) b σ hσ (algebraMap K (AlgebraicClosure K) (c : K)) hβ
  rw [AlgEquiv.commutes] at h1
  have hc0 : algebraMap K (AlgebraicClosure K) (c : K) ≠ 0 :=
    (map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr c.ne_zero
  have h2 := (mul_left_eq_self₀.mp h1.symm).resolve_right hc0
  have h3 : ((h (c ^ n) b : Kˣ) : K) = 1 :=
    (algebraMap K (AlgebraicClosure K)).injective (by rw [map_one]; exact h2)
  exact Units.ext (by rw [Units.val_one]; exact h3)

/-- The symbol against `1` is `1` — the second slot at the trivial class
([Serre 1979, Chap. XIV, §2, Prop. 7 ii, p.208][Serre1979]). -/
theorem one_right (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0) (a : Kˣ) : h a 1 = 1 := by
  have h1 := mul_right hh hn a 1 1
  rw [one_mul] at h1
  exact (mul_left_cancel (a := h a 1) (by rw [mul_one]; exact h1)).symm

/-- An `n`-th power in the second slot kills the symbol: its norm-residue class acts through
the `n`-th power of a lift, and the values are `n`-th roots of unity. The trivial half of
right nondegeneracy ([Serre 1979, Chap. XIV, §2, Prop. 7 vi and Cor., pp.208–209]
[Serre1979]). -/
theorem pow_right_eq_one (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0) (a c : Kˣ) :
    h a (c ^ n) = 1 := by
  have key : ∀ m : ℕ, h a (c ^ m) = h a c ^ m := by
    intro m
    induction m with
    | zero => rw [pow_zero, pow_zero, one_right hh hn]
    | succ k ih => rw [pow_succ, pow_succ, mul_right hh hn, ih]
  rw [key n, pow_eq_one hh hn]

/-- The characterization pins the symbol: two `n`-th Hilbert symbols agree. The proof
consumes the recorded uniqueness of the reciprocity map,
`Atlas.Knowledge.IsLocalReciprocity.unique`, and inherits its backlog through the axiom
audit ([Serre 1979, Chap. XIV, §2, Prop. 6, p.208][Serre1979];
[Milne 2020, Chap. III, §4, Rem. 4.5, p.114][MilneCFT]). -/
theorem unique (hn : n ≠ 0) {h₁ h₂ : Kˣ → Kˣ → Kˣ} (hh₁ : IsLocalHilbertSymbol K n h₁)
    (hh₂ : IsLocalHilbertSymbol K n h₂) : h₁ = h₂ := by
  obtain ⟨φ₁, hφ₁, hspec₁⟩ := hh₁
  obtain ⟨φ₂, hφ₂, hspec₂⟩ := hh₂
  have hφ : φ₂ = φ₁ := IsLocalReciprocity.unique hφ₂ hφ₁
  subst hφ
  funext a b
  obtain ⟨σ, hσ⟩ := exists_lift (φ₂ b)
  obtain ⟨β, hβ, hβ0⟩ := exists_root a hn
  exact units_eq_of_smul hβ0 ((hspec₁ a b σ hσ β hβ).symm.trans (hspec₂ a b σ hσ β hβ))

end IsLocalHilbertSymbol

end Atlas.Knowledge
