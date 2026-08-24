import Mathlib

/-!
# Hilbert's theorem 90

The cyclic Hilbert 90 of a finite Galois extension, at `Type*`: a norm-one element of `L` is
`y / σ y` for any generator `σ` of the cyclic Galois group. Mathlib carries this statement
(`groupCohomology.exists_div_of_norm_eq_one`) with both fields pinned to universe zero,
which the layer's `Type*` carriers cannot meet, so the item re-proves it universe-generally
— by the same argument the literature uses: Serre's Poincaré series over the running partial
norms, nonzero somewhere by Dedekind's linear independence of characters. The enumeration of
the Galois group by the powers of a generator is proved on the way and shared: it is also
what identifies the layer's cyclic norm with the field norm.

## Main statements

* `hilbertNinety` — the cyclic Hilbert 90 at `Type*`; proved.
* `prod_pow_apply_eq_norm` — the powers of a generator below its order multiply out to the
  field norm; proved.

## Implementation notes

The witness is produced as a unit together with the field-level equation `y / σ y = x`, the
shape the graded-piece consumer `Atlas.Knowledge.galUnits_ker_norm_le_range_diff` inverts
into difference-range membership. The coefficients `aᵢ = ∏_{j < i} σʲ x` are kept as a
private `partialNorm` with its two defining laws; the closing law `a_n = 1` is the
enumeration lemma read at the norm-one hypothesis. Dedekind's independence enters as
Mathlib's `linearIndependent_monoidHom` restricted along the injective family
`i ↦ σ^i` on units — injective on `Fin (orderOf σ)` because a field automorphism is
determined by its unit values.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]

/-- The product of a generator's powers applied to `z` is the norm of `z`: the powers below
the order enumerate the Galois group
([Serre 1979, Chap. X, §1, p.150][Serre1979]). -/
theorem prod_pow_apply_eq_norm (σ : L ≃ₐ[K] L) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (z : L) :
    ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) z = algebraMap K L (Algebra.norm K z) := by
  rw [Algebra.norm_eq_prod_automorphisms]
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  have hbij : Function.Bijective (fun i : Fin (orderOf σ) => σ ^ (i : ℕ)) := by
    constructor
    · intro i j hij
      exact Fin.ext (pow_injOn_Iio_orderOf (Set.mem_Iio.mpr i.2) (Set.mem_Iio.mpr j.2) hij)
    · intro τ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
      have hpos : 0 < (orderOf σ : ℤ) := by
        exact_mod_cast hfin.orderOf_pos
      set m := (k % (orderOf σ : ℤ)).toNat with hm
      have hmlt : m < orderOf σ := by
        have h1 : k % (orderOf σ : ℤ) < (orderOf σ : ℤ) := Int.emod_lt_of_pos k hpos
        have h2 : 0 ≤ k % (orderOf σ : ℤ) := Int.emod_nonneg k hpos.ne'
        omega
      refine ⟨⟨m, hmlt⟩, ?_⟩
      have h3 : σ ^ (m : ℕ) = σ ^ ((m : ℕ) : ℤ) := (zpow_natCast σ m).symm
      have h4 : ((m : ℕ) : ℤ) = k % (orderOf σ : ℤ) := by
        rw [hm]
        exact Int.toNat_of_nonneg (Int.emod_nonneg k hpos.ne')
      calc σ ^ (m : ℕ) = σ ^ (k % (orderOf σ : ℤ)) := by rw [h3, h4]
        _ = σ ^ k := zpow_mod_orderOf σ k
        _ = τ := hk
  let e : Fin (orderOf σ) ≃ (L ≃ₐ[K] L) := Equiv.ofBijective _ hbij
  rw [← Fin.prod_univ_eq_prod_range (fun i => (σ ^ i) z) (orderOf σ)]
  exact Fintype.prod_equiv e (fun i => (σ ^ (i : ℕ)) z) (fun τ => τ z) (fun i => rfl)

section Telescope

variable (σ : L ≃ₐ[K] L)

/- The running partial norms. -/
private def partialNorm (x : L) (i : ℕ) : L := ∏ j ∈ Finset.range i, (σ ^ j) x

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem partialNorm_zero (x : L) : partialNorm σ x 0 = 1 := rfl

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem partialNorm_succ (x : L) (i : ℕ) :
    partialNorm σ x (i + 1) = x * σ (partialNorm σ x i) := by
  unfold partialNorm
  rw [Finset.prod_range_succ', map_prod]
  have h : ∀ j, (σ ^ (j + 1)) x = σ ((σ ^ j) x) := by
    intro j
    rw [pow_succ']
    rfl
  rw [Finset.prod_congr rfl fun j _ => h j,
    show (σ ^ (0 : ℕ)) x = x from rfl, mul_comm]

end Telescope

section Hilbert90

variable {σ : L ≃ₐ[K] L}

/-- **Hilbert's Theorem 90 for a cyclic extension**: a norm-one element is `y / σ y` for a
generator `σ` — Serre's Corollary verbatim, proved by his own Poincaré-series argument: the
twisted sum `∑ aᵢ σⁱ(c)` with the running partial norms as coefficients is nonzero at some
`c` by Dedekind's independence of characters, and `x` shifts it onto itself. Stated and
proved at `Type*`: Mathlib's `groupCohomology.exists_div_of_norm_eq_one` pins `K L : Type`,
which the layer's carriers do not satisfy
([Serre 1979, Chap. X, §1, Prop. 2, p.150, and Cor., p.151][Serre1979];
[Yamaguchi 2026, `LocalClassFieldTheory/ClassFormation/Hilbert90.lean:17`]
[Yamaguchi2026]). -/
theorem hilbertNinety (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ)
    {x : L} (hx : Algebra.norm K x = 1) :
    ∃ y : Lˣ, (y : L) / σ (y : L) = x := by
  set n := orderOf σ with hn
  have hn0 : 0 < n := (isOfFinOrder_of_finite σ).orderOf_pos
  have hclose : partialNorm σ x n = 1 := by
    unfold partialNorm
    rw [prod_pow_apply_eq_norm σ hgen x, hx, map_one]
  set F : L → L := fun c => ∑ i ∈ Finset.range n, partialNorm σ x i * (σ ^ i) c with hF
  have hexists : ∃ c : L, F c ≠ 0 := by
    by_contra hall
    push Not at hall
    set fam : Fin n → (Lˣ →* L) := fun i =>
      ((σ ^ (i : ℕ) : L ≃ₐ[K] L) : L →* L).comp (Units.coeHom L) with hfam
    have hinj : Function.Injective fam := by
      intro i j hij
      refine Fin.ext (pow_injOn_Iio_orderOf (Set.mem_Iio.mpr i.2) (Set.mem_Iio.mpr j.2) ?_)
      ext z
      rcases eq_or_ne z 0 with rfl | hz
      · rw [map_zero, map_zero]
      · have hz' := DFunLike.congr_fun hij (Units.mk0 z hz)
        simpa [hfam] using hz'
    have hli : LinearIndependent L (fun i : Fin n => ⇑(fam i)) :=
      (linearIndependent_monoidHom Lˣ L).comp fam hinj
    have hcomb : ∑ i : Fin n, partialNorm σ x (i : ℕ) • ⇑(fam i) = 0 := by
      funext u
      have hu : ∑ i ∈ Finset.range n, partialNorm σ x i * (σ ^ i) (u : L) = 0 :=
        hall (u : L)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [← Fin.sum_univ_eq_sum_range
        (fun i => partialNorm σ x i * (σ ^ i) (u : L)) n] at hu
      exact hu
    have hzero := Fintype.linearIndependent_iff.mp hli
      (fun i => partialNorm σ x (i : ℕ)) hcomb ⟨0, hn0⟩
    rw [partialNorm_zero] at hzero
    exact one_ne_zero hzero
  obtain ⟨c, hc⟩ := hexists
  have hkey : x * σ (F c) = F c := by
    rw [hF]
    simp only [map_sum, map_mul, Finset.mul_sum]
    have hterm : ∀ i, x * (σ (partialNorm σ x i) * σ ((σ ^ i) c)) =
        partialNorm σ x (i + 1) * (σ ^ (i + 1)) c := by
      intro i
      rw [partialNorm_succ]
      have hstep : σ ((σ ^ i) c) = (σ ^ (i + 1)) c := by
        rw [pow_succ']
        rfl
      rw [hstep]
      ring
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    have hshift := Finset.sum_range_succ' (fun i => partialNorm σ x i * (σ ^ i) c) n
    have hlast := Finset.sum_range_succ (fun i => partialNorm σ x i * (σ ^ i) c) n
    have hfn : partialNorm σ x n * (σ ^ n) c = c := by
      rw [hclose, one_mul, hn, pow_orderOf_eq_one σ]
      rfl
    have hf0 : partialNorm σ x 0 * (σ ^ (0 : ℕ)) c = c := by
      rw [partialNorm_zero, one_mul]
      rfl
    rw [hf0] at hshift
    rw [hfn] at hlast
    linear_combination hlast - hshift
  have hσc : σ (F c) ≠ 0 := by
    intro h0
    exact hc (by simpa using σ.injective (h0.trans (map_zero σ).symm))
  refine ⟨Units.mk0 (F c) hc, ?_⟩
  rw [Units.val_mk0, div_eq_iff hσc]
  exact hkey.symm

end Hilbert90

end Atlas.Knowledge
