import Mathlib
import Atlas.Knowledge.CyclotomicIntegerBasis

/-!
# cyclotomic normalized trace bound

Tate's boundedness of the normalized trace on the cyclotomic tower over `ℚ_[p]`: for `ζ` a
primitive `p ^ m`-th root of unity in `PadicAlgCl p` and `ζ ^ p ^ (m - n)` the primitive
`p ^ n`-th root below it, `Algebra.normalizedTrace` from the algebraic closure down to
`ℚ_[p]⟮ζ ^ p ^ (m - n)⟯` moves the norm of an element of `ℚ_[p]⟮ζ⟯` by at most a factor of
`p`—a bound independent of `m`. This is the analytic heart of the Tate–Sen method: the
normalized traces are uniformly bounded projections onto the finite levels of the tower, so
they extend to the completion and split off each level as a closed subspace.

## Main statements

* `cyclotomicNormalizedTraceBound` — the headline: for `x ∈ ℚ_[p]⟮ζ⟯` the norm of the
  normalized trace down to level `n` is bounded by `(p : ℝ) * ‖x‖`.
* `CyclotomicNormalizedTraceBound.norm_normalizedTrace_le_one` — the integral case: on the
  unit ball `Algebra.adjoin ℤ_[p] {ζ}` the normalized trace has norm at most one.
* `CyclotomicNormalizedTraceBound.minpoly_eq_X_pow_sub_C` — the relative minimal polynomial:
  `minpoly` of `ζ` over the level-`n` field is `X ^ p ^ (m - n) - C a`, with `a` the
  generator of the level-`n` field.
* `CyclotomicNormalizedTraceBound.finrank_adjoin_adjoin` — the relative degree of the tower
  step is `p ^ (m - n)`.

## Implementation notes

Brinon–Conrad prove the bound by estimating the different along the tower; here the integral
structure is already in hand, so the proof instead expands an integral element in the power
basis of `ζ` over `ℤ_[p]` (`Atlas.Knowledge.cyclotomicIntegerBasis`) and computes the trace
through the embedding sum: over the level-`n` field, the embeddings of the tower step into
the closure send `ζ` to the products `ζ * (ζ ^ p ^ n) ^ t`, and summing the powers of the
primitive `p ^ (m - n)`-th root `ζ ^ p ^ n` kills every monomial `ζ ^ i` except those with
`p ^ (m - n) ∣ i`, which land in the level-`n` integers. So the normalized trace of an
integral element is integral with no loss at all, and the factor `p` in the headline is only
the cost of scaling a general element into the unit ball, by a power of `p` whose norms
reach only the integer powers of `p`. The normalized trace itself is
`Algebra.normalizedTrace`; `Algebra.normalizedTrace_intermediateField` and
`Algebra.normalizedTrace_eq_of_finiteDimensional_apply` reduce its computation to the finite
tower step, and the `Algebra.IsAlgebraic` instance recorded here feeds it the integrality of
the closure over every intermediate field.

## References

* [BrinonConrad2009] O. Brinon, B. Conrad, *CMI Summer School notes on p-adic Hodge theory
  (preliminary version)*, available at math.stanford.edu/~conrad/papers/notes.pdf, 2009.
* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open Polynomial

open scoped IntermediateField

namespace Atlas.Knowledge

namespace CyclotomicNormalizedTraceBound

variable {p : ℕ} [Fact p.Prime]

/-- The algebraic closure of `ℚ_[p]` is algebraic over every intermediate field: algebraicity
ascends from the base of the tower. Recorded as an instance so that
`Algebra.normalizedTrace` down to an intermediate field elaborates. -/
instance isAlgebraic (F : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Algebra.IsAlgebraic ↥F (PadicAlgCl p) :=
  Algebra.IsAlgebraic.tower_top (K := ℚ_[p]) ↥F

/-- The norm of `p` in the algebraic closure is `p⁻¹`: the spectral norm extends the `p`-adic
one. -/
theorem norm_natCast_p : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, ← PadicAlgCl.spectralNorm_eq,
    spectralNorm_extends, Padic.norm_p]

/-- The image of a `p`-adic integer in the algebraic closure has norm at most one. -/
theorem norm_algebraMap_le_one (c : ℤ_[p]) : ‖algebraMap ℤ_[p] (PadicAlgCl p) c‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), ← PadicAlgCl.spectralNorm_eq,
    spectralNorm_extends]
  exact c.2

/-- Descending the tower: the `p ^ (m - n)`-th power of a primitive `p ^ m`-th root of unity
is a primitive `p ^ n`-th root of unity. -/
theorem isPrimitiveRoot_pow_sub {m n : ℕ} {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ m)) (hnm : n ≤ m) :
    IsPrimitiveRoot (ζ ^ p ^ (m - n)) (p ^ n) := by
  refine hζ.pow (pow_pos (Fact.out : p.Prime).pos m) ?_
  rw [← pow_add]
  congr 1
  omega

/-- The complementary power: `ζ ^ p ^ n` is a primitive `p ^ (m - n)`-th root of unity, the
generator of the roots of unity of the tower step. -/
theorem isPrimitiveRoot_pow {m n : ℕ} {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ m)) (hnm : n ≤ m) :
    IsPrimitiveRoot (ζ ^ p ^ n) (p ^ (m - n)) := by
  refine hζ.pow (pow_pos (Fact.out : p.Prime).pos m) ?_
  rw [← pow_add]
  congr 1
  omega

/-- Summing the `j`-th powers of all `D`-th roots of unity: the sum is `D` when `D ∣ j` and
vanishes otherwise—the cancellation that isolates every `D`-th monomial in a trace. -/
theorem sum_pow_eq {η : PadicAlgCl p} {D : ℕ} (hη : IsPrimitiveRoot η D) (j : ℕ) :
    ∑ t ∈ Finset.range D, (η ^ j) ^ t = if D ∣ j then (D : PadicAlgCl p) else 0 := by
  by_cases h : D ∣ j
  · rw [if_pos h, (hη.pow_eq_one_iff_dvd j).mpr h]
    simp
  · rw [if_neg h]
    have h1 : η ^ j ≠ 1 := fun he => h ((hη.pow_eq_one_iff_dvd j).mp he)
    have h2 : (η ^ j) ^ D = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hη.pow_eq_one, one_pow]
    rw [geom_sum_eq h1, h2, sub_self, zero_div]

/-- Averaging an integral polynomial value over the fiber `z * η ^ t` of the tower step: only
the monomials of exponent divisible by `D` survive, each multiplied by `D`. This is the
embedding sum of the trace, computed before any field theory enters. -/
theorem sum_aeval_eq {η : PadicAlgCl p} {D : ℕ} (hη : IsPrimitiveRoot η D) (Q : ℤ_[p][X])
    (z : PadicAlgCl p) :
    ∑ t ∈ Finset.range D, Polynomial.aeval (z * η ^ t) Q
      = (D : PadicAlgCl p) * ∑ i ∈ (Finset.range (Q.natDegree + 1)).filter (fun i => D ∣ i),
          algebraMap ℤ_[p] (PadicAlgCl p) (Q.coeff i) * z ^ i := by
  simp_rw [Polynomial.aeval_eq_sum_range, Algebra.smul_def]
  rw [Finset.sum_comm]
  have key : ∀ i ∈ Finset.range (Q.natDegree + 1),
      ∑ t ∈ Finset.range D, algebraMap ℤ_[p] (PadicAlgCl p) (Q.coeff i) * (z * η ^ t) ^ i
        = algebraMap ℤ_[p] (PadicAlgCl p) (Q.coeff i) * z ^ i
            * (if D ∣ i then (D : PadicAlgCl p) else 0) := by
    intro i _
    have h1 : ∀ t, (z * η ^ t) ^ i = z ^ i * (η ^ i) ^ t := by
      intro t
      rw [mul_pow, ← pow_mul, mul_comm t i, pow_mul]
    simp_rw [h1]
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_pow_eq hη i, mul_assoc]
  rw [Finset.sum_congr rfl key]
  simp_rw [mul_ite, mul_zero]
  rw [← Finset.sum_filter, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The tower step of the cyclotomic tower has degree `p ^ (m - n)`: the level-`m` field is
the simple extension of the level-`n` field by `ζ`, and the absolute degrees are the
totients ([Brinon–Conrad 2009, §14.1, p.238][BrinonConrad2009], the display computing the
degree of the tower step; the absolute degrees are
[Serre 1979, Chap. IV, §4, Prop. 17, p.78][Serre1979]). -/
theorem finrank_adjoin_adjoin {m n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ m))
    (hn : n ≠ 0) (hnm : n ≤ m) :
    Module.finrank ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯) = p ^ (m - n) := by
  have hp' : p.Prime := Fact.out
  have hζ' := isPrimitiveRoot_pow_sub hζ hnm
  have hm : m ≠ 0 := by omega
  have hres : (ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯).restrictScalars ℚ_[p] = ℚ_[p]⟮ζ⟯ := by
    rw [IntermediateField.adjoin_simple_adjoin_simple]
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
      (IntermediateField.adjoin.mono _ _ _ (Set.subset_insert _ _))
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) _,
      IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ⟩
  have h1 : Module.finrank ℚ_[p] ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) = (p ^ n).totient :=
    CyclotomicIntegerBasis.finrank_adjoin hζ' hn
  have h2 : Module.finrank ℚ_[p] ↥(ℚ_[p]⟮ζ⟯) = (p ^ m).totient :=
    CyclotomicIntegerBasis.finrank_adjoin hζ hm
  have h4 : Module.finrank ℚ_[p] ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯) = (p ^ m).totient := by
    have h3 : Module.finrank ℚ_[p]
        ↥((ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯).restrictScalars ℚ_[p]) = (p ^ m).totient := by
      rw [hres]
      exact h2
    exact h3
  have h5 := Module.finrank_mul_finrank ℚ_[p] ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯)
    ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯)
  rw [h1, h4] at h5
  have h6 : (p ^ n).totient * p ^ (m - n) = (p ^ m).totient := by
    rw [Nat.totient_prime_pow hp' (Nat.pos_of_ne_zero hn),
      Nat.totient_prime_pow hp' (Nat.pos_of_ne_zero hm), mul_right_comm, ← pow_add]
    congr 2
    omega
  exact Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.mpr (pow_pos hp'.pos n)) (h5.trans h6.symm)

/-- The relative minimal polynomial of the cyclotomic tower step: over the level-`n` field,
`ζ` has minimal polynomial `X ^ p ^ (m - n) - C ζ'` with `ζ'` the level-`n` root—a monic
polynomial of the right degree vanishing at `ζ`
([Serre 1979, Chap. IV, §4, Prop. 17, p.78][Serre1979], where the degrees force it). -/
theorem minpoly_eq_X_pow_sub_C {m n : ℕ} {ζ : PadicAlgCl p} (hζ : IsPrimitiveRoot ζ (p ^ m))
    (hn : n ≠ 0) (hnm : n ≤ m) :
    minpoly ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) ζ
      = X ^ p ^ (m - n)
          - C (IntermediateField.AdjoinSimple.gen ℚ_[p] (ζ ^ p ^ (m - n))) := by
  have hp' : p.Prime := Fact.out
  have hd : p ^ (m - n) ≠ 0 := (pow_pos hp'.pos _).ne'
  have hW : (X ^ p ^ (m - n)
      - C (IntermediateField.AdjoinSimple.gen ℚ_[p] (ζ ^ p ^ (m - n)))).Monic :=
    monic_X_pow_sub_C _ hd
  have hζint : IsIntegral ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) ζ := Algebra.IsIntegral.isIntegral ζ
  have haev : Polynomial.aeval ζ (X ^ p ^ (m - n)
      - C (IntermediateField.AdjoinSimple.gen ℚ_[p] (ζ ^ p ^ (m - n)))) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      IntermediateField.AdjoinSimple.algebraMap_gen, sub_self]
  have hdeg : (minpoly ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) ζ).natDegree = p ^ (m - n) := by
    rw [← IntermediateField.adjoin.finrank hζint]
    exact finrank_adjoin_adjoin hζ hn hnm
  refine Polynomial.eq_of_monic_of_associated (minpoly.monic hζint) hW
    (Polynomial.associated_of_dvd_of_natDegree_le (minpoly.dvd _ ζ haev) hW.ne_zero ?_)
  rw [Polynomial.natDegree_X_pow_sub_C, hdeg]

/-- The integral case of Tate's bound: the normalized trace from the algebraic closure down
to the level-`n` cyclotomic field sends `Algebra.adjoin ℤ_[p] {ζ}` into the unit ball. The
trace is computed through the embedding sum: expanding in powers of `ζ` and averaging over
the roots `ζ * (ζ ^ p ^ n) ^ t` of the tower step leaves exactly the monomials `ζ ^ i` with
`p ^ (m - n) ∣ i`, a `ℤ_[p]`-combination of powers of the level-`n` root
([Brinon–Conrad 2009, §14.1, Lem. 14.1.4, p.238][BrinonConrad2009], the integral heart of the
estimate). -/
theorem norm_normalizedTrace_le_one {m n : ℕ} {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ m)) (hn : n ≠ 0) (hnm : n ≤ m) {x : PadicAlgCl p}
    (hx : x ∈ Algebra.adjoin ℤ_[p] {ζ}) :
    ‖algebraMap ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) (PadicAlgCl p)
      (Algebra.normalizedTrace ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) (PadicAlgCl p) x)‖ ≤ 1 := by
  have hp' : p.Prime := Fact.out
  have hd0 : p ^ (m - n) ≠ 0 := (pow_pos hp'.pos _).ne'
  have hη := isPrimitiveRoot_pow hζ hnm
  have hζne : ζ ≠ 0 := hζ.ne_zero (pow_pos hp'.pos m).ne'
  haveI : CharZero (PadicAlgCl p) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[p] (PadicAlgCl p)).injective
  haveI : IsScalarTower ℤ_[p] ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) (PadicAlgCl p) :=
    ⟨fun a b c => smul_assoc a (b : PadicAlgCl p) c⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ_[p][X], Polynomial.aeval ζ Q = x := by
    rwa [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hx
  have hζint : IsIntegral ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) ζ := Algebra.IsIntegral.isIntegral ζ
  haveI hFD : FiniteDimensional ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯) :=
    IntermediateField.adjoin.finiteDimensional hζint
  set pb := IntermediateField.adjoin.powerBasis hζint with hpb
  have hgen_map : algebraMap ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯) (PadicAlgCl p) pb.gen = ζ :=
    IntermediateField.AdjoinSimple.algebraMap_gen _ _
  -- the minimal polynomial of the generator, seen inside the adjoin
  have hminp : minpoly ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) pb.gen
      = X ^ p ^ (m - n)
          - C (IntermediateField.AdjoinSimple.gen ℚ_[p] (ζ ^ p ^ (m - n))) := by
    have h1 := minpoly.algebraMap_eq (A := ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯))
      (algebraMap ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯) (PadicAlgCl p)).injective pb.gen
    rw [hgen_map] at h1
    rw [← h1]
    exact minpoly_eq_X_pow_sub_C hζ hn hnm
  -- the element, lifted into the adjoin
  set x' := Polynomial.aeval pb.gen
    (Q.map (algebraMap ℤ_[p] ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯))) with hx'
  have hx'_map : algebraMap ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯) (PadicAlgCl p) x' = x := by
    have h1 := Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯)
        (PadicAlgCl p))
      pb.gen (Q.map (algebraMap ℤ_[p] ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯)))
    rw [IsScalarTower.coe_toAlgHom'] at h1
    rw [hx', ← h1, hgen_map, Polynomial.aeval_map_algebraMap, hQ]
  have hx'_coe : (x' : PadicAlgCl p) = x := by
    rw [← IntermediateField.algebraMap_apply]
    exact hx'_map
  -- the trace through the sum over embeddings
  have htr := trace_eq_sum_embeddings (E := PadicAlgCl p)
    (K := ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯)) (L := ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯)) (x := x')
  -- the embeddings biject with the roots `ζ * (ζ ^ p ^ n) ^ t`
  have hroot : ∀ t : Fin (p ^ (m - n)),
      Polynomial.aeval (ζ * (ζ ^ p ^ n) ^ (t : ℕ))
        (minpoly ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) pb.gen) = 0 := by
    intro t
    rw [hminp, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      IntermediateField.AdjoinSimple.algebraMap_gen, mul_pow, ← pow_mul,
      mul_comm (t : ℕ) (p ^ (m - n)), pow_mul, hη.pow_eq_one, one_pow, mul_one, sub_self]
  set e : Fin (p ^ (m - n))
      → (↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯) →ₐ[↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯)] PadicAlgCl p) :=
    fun t => pb.lift (ζ * (ζ ^ p ^ n) ^ (t : ℕ)) (hroot t) with he_def
  have he_gen : ∀ t, e t pb.gen = ζ * (ζ ^ p ^ n) ^ (t : ℕ) := fun t => pb.lift_gen _ _
  have he_bij : Function.Bijective e := by
    constructor
    · intro t₁ t₂ h12
      have h13 := congrArg (fun σ => σ pb.gen) h12
      simp only [he_gen] at h13
      exact Fin.ext (hη.pow_inj t₁.2 t₂.2 (mul_left_cancel₀ hζne h13))
    · intro σ
      have h4 : Polynomial.aeval (σ pb.gen)
          (minpoly ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) pb.gen) = 0 := by
        rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
      rw [hminp, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        IntermediateField.AdjoinSimple.algebraMap_gen, sub_eq_zero] at h4
      have h5 : (σ pb.gen * ζ⁻¹) ^ p ^ (m - n) = 1 := by
        rw [mul_pow, h4, inv_pow, mul_inv_cancel₀ (pow_ne_zero _ hζne)]
      haveI : NeZero (p ^ (m - n)) := ⟨hd0⟩
      obtain ⟨t, ht, hteq⟩ := hη.eq_pow_of_pow_eq_one h5
      refine ⟨⟨t, ht⟩, pb.algHom_ext ?_⟩
      rw [he_gen, hteq, mul_comm ζ _, inv_mul_cancel_right₀ hζne]
  -- evaluate the embedding sum through the root-of-unity cancellation
  have h6 : ∀ t : Fin (p ^ (m - n)),
      e t x' = Polynomial.aeval (ζ * (ζ ^ p ^ n) ^ (t : ℕ)) Q := by
    intro t
    rw [hx', ← Polynomial.aeval_algHom_apply, he_gen, Polynomial.aeval_map_algebraMap]
  have hsum : (∑ σ : ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯)
        →ₐ[↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯)] PadicAlgCl p, σ x')
      = ((p ^ (m - n) : ℕ) : PadicAlgCl p)
          * ∑ i ∈ (Finset.range (Q.natDegree + 1)).filter (fun i => p ^ (m - n) ∣ i),
              algebraMap ℤ_[p] (PadicAlgCl p) (Q.coeff i) * ζ ^ i := by
    calc (∑ σ : ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯⟮ζ⟯)
          →ₐ[↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯)] PadicAlgCl p, σ x')
        = ∑ t : Fin (p ^ (m - n)), Polynomial.aeval (ζ * (ζ ^ p ^ n) ^ (t : ℕ)) Q :=
          (Fintype.sum_bijective e he_bij _ _ fun t => (h6 t).symm).symm
      _ = ∑ t ∈ Finset.range (p ^ (m - n)), Polynomial.aeval (ζ * (ζ ^ p ^ n) ^ t) Q :=
          Fin.sum_univ_eq_sum_range
            (fun t => Polynomial.aeval (ζ * (ζ ^ p ^ n) ^ t) Q) (p ^ (m - n))
      _ = _ := sum_aeval_eq hη Q ζ
  -- assemble the normalized trace and bound the surviving sum
  have hcast : ((p : PadicAlgCl p)) ^ (m - n) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr hp'.ne_zero)
  rw [← hx'_coe, Algebra.normalizedTrace_intermediateField,
    Algebra.normalizedTrace_eq_of_finiteDimensional_apply, smul_eq_mul, map_mul, map_inv₀,
    map_natCast, finrank_adjoin_adjoin hζ hn hnm, htr, hsum, Nat.cast_pow,
    inv_mul_cancel_left₀ hcast]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
  rw [norm_mul, norm_pow, CyclotomicIntegerBasis.norm_eq_one hζ, one_pow, mul_one]
  exact norm_algebraMap_le_one _

end CyclotomicNormalizedTraceBound

/-- **Tate's normalized trace bound** on the cyclotomic tower: for `ζ` a primitive
`p ^ m`-th root of unity over `ℚ_[p]` and `x` in `ℚ_[p]⟮ζ⟯`, the normalized trace down to
the level-`n` field `ℚ_[p]⟮ζ ^ p ^ (m - n)⟯` has norm at most `(p : ℝ) * ‖x‖`—an operator
bound independent of `m`, the analytic input of the Tate–Sen method
([Brinon–Conrad 2009, §14.1, Lem. 14.1.4, p.238][BrinonConrad2009]). On the unit ball the
trace loses nothing (`CyclotomicNormalizedTraceBound.norm_normalizedTrace_le_one`); the
factor `p` is the cost of scaling into the unit ball by a power of `p`. -/
theorem cyclotomicNormalizedTraceBound (p : ℕ) [Fact p.Prime] {m n : ℕ} {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ m)) (hn : n ≠ 0) (hnm : n ≤ m)
    {x : PadicAlgCl p} (hx : x ∈ ℚ_[p]⟮ζ⟯) :
    ‖algebraMap ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) (PadicAlgCl p)
        (Algebra.normalizedTrace ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) (PadicAlgCl p) x)‖
      ≤ (p : ℝ) * ‖x‖ := by
  have hp' : p.Prime := Fact.out
  have hpR0 : (0 : ℝ) < p := by exact_mod_cast hp'.pos
  have hp1R : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  have hr0 : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  set k := ⌈Real.logb p ‖x‖⌉ with hk
  have hk1 : ‖x‖ ≤ (p : ℝ) ^ (k : ℤ) := by
    calc ‖x‖ = (p : ℝ) ^ Real.logb p ‖x‖ := (Real.rpow_logb hpR0 (by linarith) hr0).symm
      _ ≤ (p : ℝ) ^ ((k : ℤ) : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hp1R.le (Int.le_ceil _)
      _ = (p : ℝ) ^ (k : ℤ) := Real.rpow_intCast p k
  have hk2 : (p : ℝ) ^ (k : ℤ) < (p : ℝ) * ‖x‖ := by
    calc (p : ℝ) ^ (k : ℤ) = (p : ℝ) ^ ((k : ℤ) : ℝ) := (Real.rpow_intCast p k).symm
      _ < (p : ℝ) ^ (Real.logb p ‖x‖ + 1) :=
        Real.rpow_lt_rpow_of_exponent_lt hp1R (Int.ceil_lt_add_one _)
      _ = (p : ℝ) * ‖x‖ := by
        rw [Real.rpow_add hpR0, Real.rpow_logb hpR0 (by linarith) hr0, Real.rpow_one,
          mul_comm]
  -- scale into the unit ball by a power of `p`
  have hnormy : ‖(p : PadicAlgCl p) ^ (k : ℤ) * x‖ ≤ 1 := by
    rw [norm_mul, norm_zpow, CyclotomicNormalizedTraceBound.norm_natCast_p, inv_zpow]
    calc ((p : ℝ) ^ (k : ℤ))⁻¹ * ‖x‖ ≤ ((p : ℝ) ^ (k : ℤ))⁻¹ * (p : ℝ) ^ (k : ℤ) :=
          mul_le_mul_of_nonneg_left hk1 (by positivity)
      _ = 1 := inv_mul_cancel₀ (zpow_pos hpR0 k).ne'
  have hymem : (p : PadicAlgCl p) ^ (k : ℤ) * x ∈ ℚ_[p]⟮ζ⟯ :=
    mul_mem (zpow_mem (natCast_mem _ p) k) hx
  have hyadj : (p : PadicAlgCl p) ^ (k : ℤ) * x ∈ Algebra.adjoin ℤ_[p] {ζ} :=
    cyclotomicIntegerBasis hζ (by omega) hymem hnormy
  have hbound := CyclotomicNormalizedTraceBound.norm_normalizedTrace_le_one hζ hn hnm hyadj
  -- undo the scaling
  have hcmap : algebraMap ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) (PadicAlgCl p)
      ((p : ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯)) ^ (k : ℤ)) = (p : PadicAlgCl p) ^ (k : ℤ) := by
    rw [map_zpow₀, map_natCast]
  have hlin : Algebra.normalizedTrace ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) (PadicAlgCl p)
      ((p : PadicAlgCl p) ^ (k : ℤ) * x)
      = (p : ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯)) ^ (k : ℤ)
          • Algebra.normalizedTrace ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) (PadicAlgCl p) x := by
    rw [← map_smul, Algebra.smul_def, hcmap]
  rw [hlin, smul_eq_mul, map_mul, hcmap, norm_mul, norm_zpow,
    CyclotomicNormalizedTraceBound.norm_natCast_p, inv_zpow] at hbound
  have hA : ‖algebraMap ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) (PadicAlgCl p)
      (Algebra.normalizedTrace ↥(ℚ_[p]⟮ζ ^ p ^ (m - n)⟯) (PadicAlgCl p) x)‖
      ≤ (p : ℝ) ^ (k : ℤ) := by
    have h7 := mul_le_mul_of_nonneg_left hbound (zpow_pos hpR0 k).le
    rwa [← mul_assoc, mul_inv_cancel₀ (zpow_pos hpR0 k).ne', one_mul, mul_one] at h7
  exact hA.trans hk2.le

end Atlas.Knowledge
