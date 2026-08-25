import Mathlib
import Atlas.Knowledge.LubinTateModule
import Atlas.Knowledge.StandardLubinTatePolynomial
import Atlas.Knowledge.StandardLubinTateSeries

/-!
# standard Lubin–Tate torsion

The torsion theory of the evaluated standard module on an abstract finite extension:
multiplication by `π` is evaluation of the standard polynomial and `[π ^ k]` of its
`k`-th iterate, so a root of the level-`n + 1` primitive polynomial lying in the maximal
ideal is exact `π ^ (n + 1)`-torsion — the `n`-th iterate cannot vanish, because its
`q − 1`-st power is `−π` — its annihilator is exactly `𝔪 ^ (n + 1)`, two scalars move it
to the same point iff they are congruent modulo `𝔪 ^ (n + 1)`, and its unit orbit
consists of primitive roots again. This is Milne's `Λ_n ≅ A/(πⁿ)` computation carried
out on one generator, the engine behind the Galois description of the level fields.

## Main statements

* `standardLubinTateSMul_pi` / `standardLubinTateSMul_pi_pow` — the polynomial bridge;
  proved.
* `standardLubinTateSMul_pi_pow_succ_eq_zero` / `standardLubinTateSMul_pi_pow_ne_zero`
  / `standardLubinTateSMul_pi_pow_ne_zero_of_le` — exact torsion; proved.
* `standardLubinTateSMul_eq_zero_iff` — the annihilator; proved.
* `standardLubinTateSMul_eq_iff` — scalar congruence; proved.
* `standardLubinTateSMul_isRoot` — the unit orbit; proved.

## Implementation notes

The carrier is the abstract pair of `Atlas.Knowledge.lubinTateSMul` — a finite extension
`E` of `K` carrying its own local-field structure — and not the level field itself: the
level tower of `Atlas.Knowledge.StandardLubinTateLevelField` acquires that structure
only through `Atlas.Knowledge.exists_extension_isMixedCharLocalField`, inside the proofs
of the recorded Galois claims, and stating the torsion facts abstractly is what lets
them be read there. The bridge from series to polynomial is `eval₂`'s polynomial branch
— `PowerSeries.eval₂_coe` needs neither continuity nor an evaluation family — and the
primitive-root hypothesis enters as the bare polynomial equation `Qₙ (x) = 0`, the form
the level generator satisfies by construction.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [Algebra K E]
  [ValuativeExtension K E] [FiniteDimensional K E] [IsMixedCharLocalField E]

variable {π : ↥𝒪[K]}

omit [FiniteDimensional K E]

/-- **Multiplication by `π` is evaluation of the standard polynomial**: `[π] = e` read
through `eval₂`'s polynomial branch
([Milne 2020, Chap. I, §2, Rem. 2.19 (a), p.35][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveAction.lean:60`][Yamaguchi2026]). -/
theorem standardLubinTateSMul_pi (hπ : Irreducible π) (x : ↥𝒪[E]) :
    lubinTateSMul K E hπ (standardLubinTateSeries hπ) π x =
      Polynomial.aeval x (standardLubinTatePolynomial ↥𝒪[K] π) := by
  unfold lubinTateSMul
  letI : UniformSpace ↥𝒪[K] := ⊥
  letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  rw [lubinTateScalar_pi hπ (standardLubinTateSeries hπ), ← standardLubinTatePolynomial_coe hπ]
  rw [show MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) (fun _ : Unit => x)
      ((standardLubinTatePolynomial ↥𝒪[K] π : Polynomial ↥𝒪[K]) : PowerSeries ↥𝒪[K]) =
    PowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) x
      ((standardLubinTatePolynomial ↥𝒪[K] π : Polynomial ↥𝒪[K]) : PowerSeries ↥𝒪[K]) from rfl]
  rw [PowerSeries.eval₂_coe, Polynomial.aeval_def]

/-- **Multiplication by `π ^ k` is evaluation of the `k`-th iterate**
([Milne 2020, Chap. I, §3, p.37][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveTorsion.lean:74`][Yamaguchi2026]). -/
theorem standardLubinTateSMul_pi_pow (hπ : Irreducible π) {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E])
    (k : ℕ) :
    lubinTateSMul K E hπ (standardLubinTateSeries hπ) (π ^ k) x =
      Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π k) := by
  induction k with
  | zero =>
    rw [pow_zero, lubinTateSMul_one, standardLubinTatePolynomialIterate_zero,
      Polynomial.aeval_X]
  | succ k IH =>
    calc lubinTateSMul K E hπ (standardLubinTateSeries hπ) (π ^ (k + 1)) x
        = lubinTateSMul K E hπ (standardLubinTateSeries hπ) (π * π ^ k) x := by
          rw [pow_succ']
      _ = lubinTateSMul K E hπ (standardLubinTateSeries hπ) π
            (lubinTateSMul K E hπ (standardLubinTateSeries hπ) (π ^ k) x) :=
          (lubinTateSMul_smul K E hπ (standardLubinTateSeries hπ) π (π ^ k) hx).symm
      _ = Polynomial.aeval
            (lubinTateSMul K E hπ (standardLubinTateSeries hπ) (π ^ k) x)
            (standardLubinTatePolynomial ↥𝒪[K] π) :=
          standardLubinTateSMul_pi K E hπ _
      _ = Polynomial.aeval
            (Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π k))
            (standardLubinTatePolynomial ↥𝒪[K] π) := by rw [IH]
      _ = Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π (k + 1)) := by
          rw [standardLubinTatePolynomialIterate_succ, Polynomial.aeval_comp]

section PrimitiveRoot

variable (hπ : Irreducible π) {n : ℕ} {x : ↥𝒪[E]}

omit [TopologicalSpace E] [IsMixedCharLocalField E] in
include hπ in
/-- At a primitive root, the `n`-th iterate does not vanish: its `q − 1`-st power is
`−π` ([Milne 2020, Chap. I, §3, the proof of Thm. 3.6, pp.38–39][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveTorsion.lean:149`][Yamaguchi2026]). -/
theorem aeval_standardLubinTatePolynomialIterate_ne_zero
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0) :
    Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π n) ≠ 0 := by
  intro h0
  have hq : 1 < Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) :=
    Finite.one_lt_card (α := IsLocalRing.ResidueField ↥𝒪[K])
  have hthis := hroot
  rw [standardLubinTatePrimitivePolynomial, map_add, map_pow, h0, Polynomial.aeval_C,
    zero_pow (by omega : Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) - 1 ≠ 0),
    zero_add] at hthis
  refine (?_ : algebraMap ↥𝒪[K] ↥𝒪[E] π ≠ 0) hthis
  rw [← map_zero (algebraMap ↥𝒪[K] ↥𝒪[E])]
  exact fun hcontra =>
    hπ.ne_zero (FaithfulSMul.algebraMap_injective ↥𝒪[K] ↥𝒪[E] hcontra)

/-- **The `n`-th scalar of a primitive root does not vanish**
([Milne 2020, Chap. I, §3, the proof of Thm. 3.6, p.39][MilneCFT]). -/
theorem standardLubinTateSMul_pi_pow_ne_zero (hx : x ∈ 𝓂[E])
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0) :
    lubinTateSMul K E hπ (standardLubinTateSeries hπ) (π ^ n) x ≠ 0 := by
  rw [standardLubinTateSMul_pi_pow K E hπ hx n]
  exact aeval_standardLubinTatePolynomialIterate_ne_zero K E hπ hroot

/-- **A primitive root is `π ^ (n + 1)`-torsion**
([Milne 2020, Chap. I, §3, the proof of Thm. 3.6, pp.38–39][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveTorsion.lean:170`][Yamaguchi2026]). -/
theorem standardLubinTateSMul_pi_pow_succ_eq_zero (hx : x ∈ 𝓂[E])
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0) :
    lubinTateSMul K E hπ (standardLubinTateSeries hπ) (π ^ (n + 1)) x = 0 := by
  rw [standardLubinTateSMul_pi_pow K E hπ hx (n + 1),
    standardLubinTatePolynomialIterate_succ_factor, map_mul, hroot, mul_zero]

/-- Below the level, no iterate scalar vanishes
([Milne 2020, Chap. I, §3, the proof of Thm. 3.6, p.39][MilneCFT]). -/
theorem standardLubinTateSMul_pi_pow_ne_zero_of_le (hx : x ∈ 𝓂[E])
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    {k : ℕ} (hk : k ≤ n) :
    lubinTateSMul K E hπ (standardLubinTateSeries hπ) (π ^ k) x ≠ 0 := by
  intro h0
  refine standardLubinTateSMul_pi_pow_ne_zero K E hπ hx hroot ?_
  rw [show π ^ n = π ^ (n - k) * π ^ k from by rw [← pow_add]; congr 1; omega,
    ← lubinTateSMul_smul K E hπ (standardLubinTateSeries hπ) (π ^ (n - k)) (π ^ k) hx,
    h0, lubinTateSMul_zero]

/-- **The annihilator of a primitive root is exactly `𝔪 ^ (n + 1)`**: the module the
root generates is `A ⧸ 𝔪 ^ (n + 1)`
([Milne 2020, Chap. I, §3, Prop. 3.4 and Lem. 3.3, pp.37–38][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveAction.lean:360`][Yamaguchi2026]). -/
theorem standardLubinTateSMul_eq_zero_iff (hx : x ∈ 𝓂[E])
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    (w : ↥𝒪[K]) :
    lubinTateSMul K E hπ (standardLubinTateSeries hπ) w x = 0 ↔
      w ∈ (𝓂[K] ^ (n + 1) : Ideal ↥𝒪[K]) := by
  have hmax : (𝓂[K] ^ (n + 1) : Ideal ↥𝒪[K]) =
      Ideal.span {π ^ (n + 1)} := by
    rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow]
  constructor
  · intro h0
    by_contra hnot
    rcases eq_or_ne w 0 with rfl | hw0
    · exact hnot (Ideal.zero_mem _)
    obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hw0 hπ
    have hk : k ≤ n := by
      by_contra hgt
      refine hnot ?_
      rw [hmax, Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_left (pow_dvd_pow π (by omega)) _
    rw [← lubinTateSMul_smul K E hπ (standardLubinTateSeries hπ) (↑u) (π ^ k) hx] at h0
    exact standardLubinTateSMul_pi_pow_ne_zero_of_le K E hπ hx hroot hk
      ((lubinTateSMul_eq_zero_iff K E hπ (standardLubinTateSeries hπ) u.isUnit
        (lubinTateSMul_mem_maximalIdeal K E hπ (standardLubinTateSeries hπ) _ hx)).mp h0)
  · intro hmem
    rw [hmax, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, rfl⟩ := hmem
    rw [mul_comm, ← lubinTateSMul_smul K E hπ (standardLubinTateSeries hπ) c (π ^ (n + 1)) hx,
      standardLubinTateSMul_pi_pow_succ_eq_zero K E hπ hx hroot, lubinTateSMul_zero]

/-- **Two scalars agree on a primitive root iff they are congruent mod `𝔪 ^ (n + 1)`**
— stated additively on ring elements, where the source states it multiplicatively on
units, so this is the more general form
([Milne 2020, Chap. I, §3, Prop. 3.4, p.38][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveAction.lean:545`][Yamaguchi2026]). -/
theorem standardLubinTateSMul_eq_iff (hx : x ∈ 𝓂[E])
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    (u v : ↥𝒪[K]) :
    lubinTateSMul K E hπ (standardLubinTateSeries hπ) u x =
        lubinTateSMul K E hπ (standardLubinTateSeries hπ) v x ↔
      u - v ∈ (𝓂[K] ^ (n + 1) : Ideal ↥𝒪[K]) := by
  constructor
  · intro h
    exact (standardLubinTateSMul_eq_zero_iff K E hπ hx hroot _).mp
      (lubinTateSMul_sub_eq_zero K E hπ (standardLubinTateSeries hπ) hx h)
  · intro hmem
    have h0 : lubinTateSMul K E hπ (standardLubinTateSeries hπ) (u - v) x = 0 :=
      (standardLubinTateSMul_eq_zero_iff K E hπ hx hroot _).mpr hmem
    calc lubinTateSMul K E hπ (standardLubinTateSeries hπ) u x
        = lubinTateSMul K E hπ (standardLubinTateSeries hπ) (u - v + v) x := by
          rw [sub_add_cancel]
      _ = lubinTateAdd K E hπ (standardLubinTateSeries hπ)
            (lubinTateSMul K E hπ (standardLubinTateSeries hπ) (u - v) x)
            (lubinTateSMul K E hπ (standardLubinTateSeries hπ) v x) :=
          lubinTateSMul_add K E hπ (standardLubinTateSeries hπ) (u - v) v hx
      _ = lubinTateSMul K E hπ (standardLubinTateSeries hπ) v x := by
          rw [h0]
          exact zero_lubinTateAdd K E hπ (standardLubinTateSeries hπ)
            (lubinTateSMul_mem_maximalIdeal K E hπ (standardLubinTateSeries hπ) v hx)

/-- **The unit orbit of a primitive root consists of primitive roots**
([Milne 2020, Chap. I, §3, the proof of Thm. 3.6, p.39][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveAction.lean:755`][Yamaguchi2026]). -/
theorem standardLubinTateSMul_isRoot (hx : x ∈ 𝓂[E])
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    (u : 𝒪[K]ˣ) :
    Polynomial.aeval (lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑u) x)
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0 := by
  have hmem : lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑u) x ∈ 𝓂[E] :=
    lubinTateSMul_mem_maximalIdeal K E hπ (standardLubinTateSeries hπ) _ hx
  have hcomm : ∀ m : ℕ,
      lubinTateSMul K E hπ (standardLubinTateSeries hπ) (π ^ m)
        (lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑u) x) =
      lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑u)
        (lubinTateSMul K E hπ (standardLubinTateSeries hπ) (π ^ m) x) := by
    intro m
    rw [lubinTateSMul_smul K E hπ (standardLubinTateSeries hπ) (π ^ m) (↑u) hx, mul_comm,
      ← lubinTateSMul_smul K E hπ (standardLubinTateSeries hπ) (↑u) (π ^ m) hx]
  have h1 : Polynomial.aeval (lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑u) x)
      (standardLubinTatePolynomialIterate ↥𝒪[K] π (n + 1)) = 0 := by
    rw [← standardLubinTateSMul_pi_pow K E hπ hmem (n + 1), hcomm (n + 1),
      standardLubinTateSMul_pi_pow_succ_eq_zero K E hπ hx hroot, lubinTateSMul_zero]
  have h2 : Polynomial.aeval (lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑u) x)
      (standardLubinTatePolynomialIterate ↥𝒪[K] π n) ≠ 0 := by
    rw [← standardLubinTateSMul_pi_pow K E hπ hmem n, hcomm n]
    intro h0
    exact standardLubinTateSMul_pi_pow_ne_zero K E hπ hx hroot
      ((lubinTateSMul_eq_zero_iff K E hπ (standardLubinTateSeries hπ) u.isUnit
        (lubinTateSMul_mem_maximalIdeal K E hπ (standardLubinTateSeries hπ) _ hx)).mp h0)
  rw [standardLubinTatePolynomialIterate_succ_factor, map_mul] at h1
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h h2
  · exact h

end PrimitiveRoot

end Atlas.Knowledge
