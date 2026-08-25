import Mathlib
import Atlas.Knowledge.IntegerValuation
import Atlas.Knowledge.StandardLubinTateTorsion

/-!
# ramification bound

The fundamental inequality of a finite extension of mixed-characteristic local fields:
the value of a base uniformizer downstairs — the ramification index — is at most the
degree, `ν_E(π) ≤ [E : K]`. The proof is the classical independence argument: the powers
`ϖ⁰, …, ϖ^{e−1}` of a uniformizer downstairs are linearly independent over the base,
because a base coefficient moves a value only by a multiple of `e`, so the nonzero terms
of a combination have pairwise distinct values and their sum cannot vanish. This is the
upper half that pins the Lubin–Tate primitive valuation: against
`Atlas.Knowledge.standardLubinTatePrimitiveValuation` and the level degree it forces the
primitive root to be a uniformizer.

## Main statements

* `ramificationBound` — `ν_E(π) ≤ [E : K]`; proved.

## Implementation notes

The classical statement is the fundamental identity `e f = n`; this item records only
the `e ≤ n` half, which is what the squeeze consumes, and takes it by the independence
route rather than through the Dedekind machinery of `e f = n` — no finiteness of the
integer ring upstairs, no factorization of the extended maximal ideal. The ultrametric
input is a private finite-sum lemma: a nonvanishing sum of elements with pairwise
distinct valuations takes the dominant value. The transfer of comparisons along the
extension rides `ValuativeExtension.vlt_iff_vlt` through `Valuation.vlt_iff_lt`, and the
`ℤ`-side distinctness converts back through `Atlas.Knowledge.normalizedValuation_lt_iff`.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- Distinct normalized values force distinct multiplicative values. -/
private theorem valuation_ne_of_nv_ne {x y : Kˣ}
    (h : normalizedValuation K x ≠ normalizedValuation K y) :
    valuation K (x : K) ≠ valuation K (y : K) := by
  rcases lt_or_gt_of_ne h with h1 | h1
  · exact ((normalizedValuation_lt_iff K x y).mp h1).ne'
  · exact ((normalizedValuation_lt_iff K y x).mp h1).ne

omit [TopologicalSpace K] [IsMixedCharLocalField K] in
/-- A finite sum of nonzero elements with pairwise distinct valuations is nonzero. -/
private theorem sum_ne_zero_of_valuation_distinct {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → K) (h0 : ∀ i ∈ s, f i ≠ 0)
    (hdist : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → valuation K (f i) ≠ valuation K (f j)) :
    ∑ i ∈ s, f i ≠ 0 := by
  classical
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image s (fun i => valuation K (f i)) hs
  have hvb : valuation K (f b) ≠ 0 := (valuation K).ne_zero_iff.mpr (h0 b hb)
  have hrest : valuation K (∑ i ∈ s.erase b, f i) < valuation K (f b) := by
    refine Valuation.map_sum_lt _ hvb ?_
    intro i hi
    have hib : i ≠ b := Finset.ne_of_mem_erase hi
    have his : i ∈ s := Finset.mem_of_mem_erase hi
    exact lt_of_le_of_ne (hmax i his) (hdist i his b hb hib)
  have hsum : valuation K (∑ i ∈ s, f i) = valuation K (f b) := by
    rw [← Finset.add_sum_erase s f hb]
    exact Valuation.map_add_eq_of_lt_left _ hrest
  intro hzero
  rw [hzero, map_zero] at hsum
  exact hvb hsum.symm

section Ramification

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [Algebra K E]
  [ValuativeExtension K E] [IsMixedCharLocalField E]

omit [TopologicalSpace K] [IsMixedCharLocalField K] [TopologicalSpace E]
  [IsMixedCharLocalField E] in
/-- Strict comparison transfers along the extension. -/
private theorem valuation_algebraMap_lt_iff (x y : K) :
    valuation E (algebraMap K E x) < valuation E (algebraMap K E y) ↔
      valuation K x < valuation K y := by
  rw [← Valuation.vlt_iff_lt, ← Valuation.vlt_iff_lt]
  exact ValuativeExtension.vlt_iff_vlt

omit [TopologicalSpace K] [IsMixedCharLocalField K] [TopologicalSpace E]
  [IsMixedCharLocalField E] in
/-- Valuation-one elements stay valuation-one along the extension. -/
private theorem valuation_algebraMap_eq_one {c : K} (h : valuation K c = 1) :
    valuation E (algebraMap K E c) = 1 := by
  rcases lt_trichotomy (valuation E (algebraMap K E c)) 1 with h1 | h1 | h1
  · exfalso
    rw [show (1 : ValueGroupWithZero E) = valuation E (algebraMap K E 1) by simp] at h1
    have := (valuation_algebraMap_lt_iff K E c 1).mp h1
    rw [h] at this
    simp at this
  · exact h1
  · exfalso
    rw [show (1 : ValueGroupWithZero E) = valuation E (algebraMap K E 1) by simp] at h1
    have := (valuation_algebraMap_lt_iff K E 1 c).mp h1
    rw [h] at this
    simp at this

variable {π : ↥𝒪[K]} (hπ : Irreducible π)

include hπ in
/-- The normalized value downstairs of a base-field element is a multiple of the
uniformizer's value: factor through the discrete valuation upstairs. -/
private theorem exists_nv_algebraMap {c : K} (hc : c ≠ 0)
    (himg : algebraMap K E c ≠ 0) (hπimg : algebraMap K E ((π : ↥𝒪[K]) : K) ≠ 0) :
    ∃ k : ℤ, normalizedValuation E (Units.mk0 (algebraMap K E c) himg) =
      k * normalizedValuation E (Units.mk0 (algebraMap K E ((π : ↥𝒪[K]) : K)) hπimg) := by
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hc
  refine ⟨n, ?_⟩
  have huKne : ((u : ↥𝒪[K]) : K) ≠ 0 := by
    intro h1
    exact Units.ne_zero u (Subtype.ext h1)
  have hu0ne : algebraMap K E ((u : ↥𝒪[K]) : K) ≠ 0 := by
    intro h0
    exact huKne ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K E)).mp h0)
  have hueq : Units.mk0 (algebraMap K E c) himg =
      Units.mk0 (algebraMap K E ((u : ↥𝒪[K]) : K)) hu0ne *
        (Units.mk0 (algebraMap K E ((π : ↥𝒪[K]) : K)) hπimg) ^ n := by
    ext
    simp only [Units.val_mul, Units.val_mk0]
    rw [show ((Units.mk0 (algebraMap K E ((π : ↥𝒪[K]) : K)) hπimg ^ n : Eˣ) : E) =
      (algebraMap K E ((π : ↥𝒪[K]) : K)) ^ n by
        rw [Units.val_zpow_eq_zpow_val, Units.val_mk0]]
    rw [hu, Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀]
    rfl
  rw [hueq, normalizedValuation_mul, normalizedValuation_zpow]
  have hu0 : normalizedValuation E
      (Units.mk0 (algebraMap K E ((u : ↥𝒪[K]) : K)) hu0ne) = 0 := by
    refine normalizedValuation_eq_zero_of_valuation_eq_one E _ ?_
    refine valuation_algebraMap_eq_one K E ?_
    exact (Valuation.integer.integers (v := valuation K)).valuation_unit u
  rw [hu0]
  ring

include hπ in
/-- **The ramification bound** `ν_E(π) ≤ [E : K]`: a base uniformizer's value
downstairs is at most the degree, because the powers of a uniformizer downstairs
strictly under that value are linearly independent over the base
([Serre 1979, Chap. I, §4, Prop. 10, p.14][Serre1979] — the `e ≤ n` half of the
fundamental identity; [Yamaguchi 2026,
`ValuationTheory/DiscreteValuationField/FiniteIntegralClosure.lean:625`, which carries
the full identity][Yamaguchi2026]). -/
theorem ramificationBound [FiniteDimensional K E] :
    integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) ≤ (Module.finrank K E : ℤ) := by
  classical
  have hπK : ((π : ↥𝒪[K]) : K) ≠ 0 := fun h => hπ.ne_zero (Subtype.ext h)
  have hπimg : algebraMap K E ((π : ↥𝒪[K]) : K) ≠ 0 := by
    intro h0
    exact hπK ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K E)).mp h0)
  set e := normalizedValuation E (Units.mk0 (algebraMap K E ((π : ↥𝒪[K]) : K)) hπimg)
    with he
  have hecoe : integerValuation E (algebraMap ↥𝒪[K] ↥𝒪[E] π) = e := by
    rw [integerValuation_of_ne_zero E hπimg]
    rfl
  have hπEint : algebraMap ↥𝒪[K] ↥𝒪[E] π ≠ 0 := by
    intro h0
    refine hπ.ne_zero (FaithfulSMul.algebraMap_injective ↥𝒪[K] ↥𝒪[E] ?_)
    rw [h0, map_zero]
  have epos : 0 < e := by
    rw [← hecoe]
    exact (integerValuation_pos_iff E hπEint).mpr
      (algebraMap_irreducible_mem_maximalIdeal K E hπ)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[E])
  have hϖE : ((ϖ : ↥𝒪[E]) : E) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
  have hϖν : normalizedValuation E (Units.mk0 ((ϖ : ↥𝒪[E]) : E) hϖE) = 1 :=
    normalizedValuation_irreducible E ϖ hϖ _ rfl
  -- the uniformizer powers below `e` are independent over the base
  have hind : LinearIndependent K (fun j : Fin e.toNat => ((ϖ : ↥𝒪[E]) : E) ^ (j : ℕ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hsum
    by_contra hex
    obtain ⟨j₀, hj₀⟩ := not_forall.mp hex
    set s : Finset (Fin e.toNat) := Finset.univ.filter (fun j => g j ≠ 0) with hs
    have hsne : s.Nonempty := ⟨j₀, by simp [hs, hj₀]⟩
    have hsub : ∑ j ∈ s, g j • ((ϖ : ↥𝒪[E]) : E) ^ (j : ℕ) =
        ∑ j : Fin e.toNat, g j • ((ϖ : ↥𝒪[E]) : E) ^ (j : ℕ) := by
      refine Finset.sum_subset (Finset.filter_subset _ _) ?_
      intro j _ hj
      have hgz : g j = 0 := by
        by_contra hgj
        exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hgj⟩)
      rw [hgz, zero_smul]
    have himgne : ∀ j ∈ s, algebraMap K E (g j) ≠ 0 := by
      intro j hj
      have hgj : g j ≠ 0 := (Finset.mem_filter.mp hj).2
      intro h0
      exact hgj ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective K E)).mp h0)
    have hterm : ∀ j ∈ s, ∀ (hj' : algebraMap K E (g j) ≠ 0),
        g j • ((ϖ : ↥𝒪[E]) : E) ^ (j : ℕ) =
          ((Units.mk0 (algebraMap K E (g j)) hj' *
            (Units.mk0 ((ϖ : ↥𝒪[E]) : E) hϖE) ^ (j : ℕ) : Eˣ) : E) := by
      intro j _ hj'
      rw [Algebra.smul_def]
      simp [Units.val_mul, Units.val_mk0, Units.val_pow_eq_pow_val]
    have hnv : ∀ j ∈ s, ∀ (hj' : algebraMap K E (g j) ≠ 0), ∃ k : ℤ,
        normalizedValuation E (Units.mk0 (algebraMap K E (g j)) hj' *
          (Units.mk0 ((ϖ : ↥𝒪[E]) : E) hϖE) ^ (j : ℕ)) = k * e + (j : ℕ) := by
      intro j hj hj'
      have hgj : g j ≠ 0 := (Finset.mem_filter.mp hj).2
      obtain ⟨k, hk⟩ := exists_nv_algebraMap K E hπ hgj hj' hπimg
      refine ⟨k, ?_⟩
      rw [normalizedValuation_mul, hk, ← zpow_natCast, normalizedValuation_zpow, hϖν]
      ring
    -- the sum over `s` is nonzero: valuations are pairwise distinct
    refine sum_ne_zero_of_valuation_distinct E s hsne _ ?_ ?_ (by rw [hsub]; exact hsum)
    · intro j hj
      rw [hterm j hj (himgne j hj)]
      exact Units.ne_zero _
    · intro i hi j hj hij
      rw [hterm i hi (himgne i hi), hterm j hj (himgne j hj)]
      refine valuation_ne_of_nv_ne E ?_
      obtain ⟨ki, hki⟩ := hnv i hi (himgne i hi)
      obtain ⟨kj, hkj⟩ := hnv j hj (himgne j hj)
      rw [hki, hkj]
      intro habs
      -- `ki e + i = kj e + j` with `0 ≤ i, j < e` forces `i = j`
      have hkey : (ki - kj) * e = ((j : ℕ) : ℤ) - ((i : ℕ) : ℤ) := by
        linear_combination habs
      have hi2 : ((i : ℕ) : ℤ) < e := by
        have h1 : (i : ℕ) < e.toNat := i.2
        omega
      have hj2 : ((j : ℕ) : ℤ) < e := by
        have h1 : (j : ℕ) < e.toNat := j.2
        omega
      have hnni : (0 : ℤ) ≤ ((i : ℕ) : ℤ) := Int.natCast_nonneg _
      have hnnj : (0 : ℤ) ≤ ((j : ℕ) : ℤ) := Int.natCast_nonneg _
      have ht0 : ki - kj = 0 := by
        by_contra htne
        rcases lt_or_gt_of_ne htne with hneg | hpos
        · have hle : (ki - kj) * e ≤ (-1) * e :=
            mul_le_mul_of_nonneg_right (by omega) (le_of_lt epos)
          rw [neg_one_mul] at hle
          linarith
        · have hge : 1 * e ≤ (ki - kj) * e :=
            mul_le_mul_of_nonneg_right (by omega) (le_of_lt epos)
          rw [one_mul] at hge
          linarith
      rw [ht0, zero_mul] at hkey
      exact hij (Fin.ext (by omega))
  have hcard := hind.fintype_card_le_finrank
  rw [Fintype.card_fin] at hcard
  rw [hecoe]
  have hcast : (e.toNat : ℤ) ≤ (Module.finrank K E : ℤ) := by exact_mod_cast hcard
  rwa [Int.toNat_of_nonneg (le_of_lt epos)] at hcast

end Ramification

end Atlas.Knowledge
