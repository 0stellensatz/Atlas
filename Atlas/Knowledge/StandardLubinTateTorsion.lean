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
* `mem_maximalIdeal_of_aeval_primitive` — primitive roots lie in the maximal ideal;
  proved.
* `algebraMap_irreducible_mem_maximalIdeal` / `algebraMap_pi_ne_zero` — the
  uniformizer's image lies in the maximal ideal upstairs and is nonzero; proved.
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
the level generator satisfies by construction. The indexing follows the tree, one step
off Milne's: his bracketed `f^[n + 1] = (f/T) ∘ f ∘ ⋯ ∘ f` is
`Atlas.Knowledge.standardLubinTatePrimitivePolynomial` at level `n`, his plain iterate
`f⁽ⁿ⁾` the `standardLubinTatePolynomialIterate`, and his `Λ_n ≅ A/(πⁿ)` is this file's
annihilator `𝔪 ^ (n + 1)` at level `n`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
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
([Milne 2020, Chap. I, §2, Rem. 2.19 (a), p.35][MilneCFT]; Yamaguchi 2026,
`LubinTate/FiniteLevel/PrimitiveAction.lean:60`). -/
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
([Milne 2020, Chap. I, §3, p.37][MilneCFT]; Yamaguchi 2026,
`LubinTate/FiniteLevel/PrimitiveTorsion.lean:74`). -/
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

omit [TopologicalSpace K] [IsMixedCharLocalField K] in
/-- **The image of the uniformizer lies in the maximal ideal upstairs**: the strict
valuative inequality transports along the extension
([Serre 1979, Chap. II, §2, Prop. 3, pp.28–29][Serre1979]). -/
theorem algebraMap_irreducible_mem_maximalIdeal (hπ : Irreducible π) :
    algebraMap ↥𝒪[K] ↥𝒪[E] π ∈ 𝓂[E] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  have hK : valuation K (π : K) < 1 := by
    have hnu : ¬IsUnit π := hπ.not_isUnit
    rwa [Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hnu
  have h1 : ((π : K)) <ᵥ 1 := (Valuation.vlt_one_iff _).mpr hK
  have h2 := (ValuativeExtension.vlt_iff_vlt (A := K) (B := E)
    (a := (π : K)) (b := 1)).mpr h1
  rw [map_one] at h2
  have h3 : valuation E (algebraMap K E (π : K)) < 1 := (Valuation.vlt_one_iff _).mp h2
  have hbase : ((algebraMap ↥𝒪[K] ↥𝒪[E] π : ↥𝒪[E]) : E) = algebraMap K E (π : K) := by
    have hx := IsScalarTower.algebraMap_apply ↥𝒪[K] ↥𝒪[E] E π
    have hy := IsScalarTower.algebraMap_apply ↥𝒪[K] K E π
    rw [hx] at hy
    exact hy.symm
  rwa [hbase]

omit [TopologicalSpace K] [IsMixedCharLocalField K] [TopologicalSpace E]
  [IsMixedCharLocalField E] in
/-- **The image of the uniformizer upstairs is nonzero** — the nonvanishing every
valuation computation at a carrier consumes; injectivity of the integer algebra map. -/
theorem algebraMap_pi_ne_zero (hπ : Irreducible π) :
    algebraMap ↥𝒪[K] ↥𝒪[E] π ≠ 0 := by
  intro h0
  refine hπ.ne_zero (FaithfulSMul.algebraMap_injective ↥𝒪[K] ↥𝒪[E] ?_)
  rw [h0, map_zero]

/-- **A root of the primitive polynomial among the integers lies in the maximal
ideal**: descending through the tower, each iterate value is a maximal-ideal element
because the next one is, the ideal is prime, and the top value's `q − 1`-st power is
`−π` — the membership half of the source's exact valuation
([Milne 2020, Chap. I, §3, the proof of Prop. 3.4, p.38][MilneCFT]; Yamaguchi 2026,
`LubinTate/FiniteLevel/PrimitiveUniformizer.lean:517`). -/
theorem mem_maximalIdeal_of_aeval_primitive (hπ : Irreducible π) {n : ℕ} {x : ↥𝒪[E]}
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0) :
    x ∈ 𝓂[E] := by
  haveI hprime : (𝓂[E] : Ideal ↥𝒪[E]).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal ↥𝒪[E]).isPrime
  have hpi : algebraMap ↥𝒪[K] ↥𝒪[E] π ∈ 𝓂[E] :=
    algebraMap_irreducible_mem_maximalIdeal K E hπ
  have htop : Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π n) ∈ 𝓂[E] := by
    have hpow : Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π n) ^
        (Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) - 1) =
        -(algebraMap ↥𝒪[K] ↥𝒪[E] π) := by
      have h := hroot
      rw [standardLubinTatePrimitivePolynomial, map_add, map_pow, Polynomial.aeval_C,
        add_eq_zero_iff_eq_neg] at h
      exact h
    refine hprime.mem_of_pow_mem _ (hpow ▸ neg_mem hpi)
  have hstep : ∀ k : ℕ,
      Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π (k + 1)) ∈ 𝓂[E] →
      Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π k) ∈ 𝓂[E] := by
    intro k hk
    rw [standardLubinTatePolynomialIterate_succ, Polynomial.aeval_comp,
      standardLubinTatePolynomial] at hk
    set t := Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π k) with ht
    have hval : Polynomial.aeval t
        (Polynomial.X ^ Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) +
          Polynomial.C π * Polynomial.X) =
        t ^ Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) +
          algebraMap ↥𝒪[K] ↥𝒪[E] π * t := by
      simp
    rw [hval] at hk
    have hXq : t ^ Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) ∈ 𝓂[E] := by
      have := Ideal.sub_mem _ hk (Ideal.mul_mem_right t _ hpi)
      simpa using this
    exact hprime.mem_of_pow_mem _ hXq
  have hall : ∀ j : ℕ,
      Polynomial.aeval x (standardLubinTatePolynomialIterate ↥𝒪[K] π (n - j)) ∈ 𝓂[E] := by
    intro j
    induction j with
    | zero => simpa using htop
    | succ j IH =>
      rcases Nat.eq_zero_or_pos (n - j) with hnj | hnj
      · rwa [show n - (j + 1) = n - j from by omega]
      · have : n - j = (n - (j + 1)) + 1 := by omega
        rw [this] at IH
        exact hstep _ IH
  have h0 := hall n
  rwa [Nat.sub_self, standardLubinTatePolynomialIterate_zero, Polynomial.aeval_X] at h0

section PrimitiveRoot

variable (hπ : Irreducible π) {n : ℕ} {x : ↥𝒪[E]}

omit [TopologicalSpace E] [IsMixedCharLocalField E] in
include hπ in
/-- At a primitive root, the `n`-th iterate does not vanish: its `q − 1`-st power is
`−π` ([Milne 2020, Chap. I, §3, the proof of Thm. 3.6, pp.38–39][MilneCFT];
Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveTorsion.lean:149`). -/
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
  exact algebraMap_pi_ne_zero K E hπ hthis

/-- **The `n`-th scalar of a primitive root does not vanish**
([Milne 2020, Chap. I, §3, the proof of Thm. 3.6, p.39][MilneCFT]). -/
theorem standardLubinTateSMul_pi_pow_ne_zero (hx : x ∈ 𝓂[E])
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0) :
    lubinTateSMul K E hπ (standardLubinTateSeries hπ) (π ^ n) x ≠ 0 := by
  rw [standardLubinTateSMul_pi_pow K E hπ hx n]
  exact aeval_standardLubinTatePolynomialIterate_ne_zero K E hπ hroot

/-- **A primitive root is `π ^ (n + 1)`-torsion**
([Milne 2020, Chap. I, §3, the proof of Thm. 3.6, pp.38–39][MilneCFT];
Yamaguchi 2026,
`LubinTate/FiniteLevel/PrimitiveTorsion.lean:170`). -/
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
Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveAction.lean:360`). -/
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
— stated additively on ring elements, where the Lean counterpart states it
multiplicatively on units, so this is the more general form
([Milne 2020, Chap. I, §3, Prop. 3.4, p.38][MilneCFT]; Yamaguchi 2026,
`LubinTate/FiniteLevel/PrimitiveAction.lean:545`). -/
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
Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveAction.lean:755`). -/
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
