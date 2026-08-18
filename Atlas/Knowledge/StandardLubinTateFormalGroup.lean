import Mathlib
import Atlas.Knowledge.LubinTateIntertwiner
import Atlas.Knowledge.StandardLubinTateSeries

/-!
# standard Lubin–Tate formal group

The formal group law of the standard series, landing in Mathlib's own `FormalGroup`: the
unique two-variable intertwiner of `π X + X ^ q` with itself with linear term `X + Y`.
Associativity and commutativity are exactly what the fundamental lemma's uniqueness
gives — both sides of each law intertwine the standard series with itself and carry the
same linear term, so they are equal — and every proof here is closed: the `FormalGroup`
value bundles its associativity, so this item is the payoff of paying for the
recursive-intertwiner argument up front. Everything here is proved.

## Main definitions

* `standardLubinTateFormalGroupPowerSeries` — the intertwiner with linear term `X + Y`.
* `standardLubinTateFormalGroup` — the `FormalGroup` it defines.

## Main statements

* `existsUnique_standardLubinTateFormalGroupPowerSeries` — the characterizing property.
* `standardLubinTateFormalGroup_isComm` — commutativity, as Mathlib's `IsComm` instance.

## Implementation notes

The closure lemmas — intertwining and prescribed linear terms are preserved by
substitution of an intertwining family — are the file's private machinery, Milne's
"formal group law from uniqueness" argument run through Mathlib's
`subst_comp_subst_apply`. The source proves the same closure in its
`SubstitutionClosure` section (`LubinTate/FormalModule/StandardFormalGroup.lean`); the
degree-one exponent classification `eq_single_of_degree_eq_one` replaces its
list-indexed bookkeeping. Mathlib's `FormalGroup` fields are matched literally — the
`assoc` field is the three-variable uniqueness instance, `IsComm` the two-variable
swapped one.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open MvPowerSeries

namespace Atlas.Knowledge

section Closure

variable {A : Type*} [CommRing A] [IsLocalRing A] {π : A} {σ τ : Type*}

omit [IsLocalRing A] in
private theorem le_order_pow_of_one_le' {f : MvPowerSeries σ A} (hf : (1 : ℕ∞) ≤ f.order)
    (k : ℕ) : (k : ℕ∞) ≤ (f ^ k).order := by
  refine le_trans ?_ (le_order_pow k)
  calc (k : ℕ∞) = k • (1 : ℕ∞) := by simp
    _ ≤ k • f.order := nsmul_le_nsmul_right hf k

omit [IsLocalRing A] in
private theorem le_order_finset_prod' {ι : Type*} (s : Finset ι)
    (f : ι → MvPowerSeries σ A) (n : ι → ℕ) (h : ∀ i ∈ s, ((n i : ℕ∞)) ≤ (f i).order) :
    ((∑ i ∈ s, n i : ℕ) : ℕ∞) ≤ (∏ i ∈ s, f i).order := by
  refine le_trans ?_ (le_weightedOrder_prod _ f s)
  rw [Nat.cast_sum]
  exact Finset.sum_le_sum h

omit [IsLocalRing A] in
private theorem mvSubst_powerSeries_subst {H : MvPowerSeries σ A}
    (hHs : PowerSeries.HasSubst H) {g : σ → MvPowerSeries τ A}
    (hg : MvPowerSeries.HasSubst g) (e : PowerSeries A) :
    MvPowerSeries.subst g (PowerSeries.subst H e) =
      PowerSeries.subst (MvPowerSeries.subst g H) e :=
  MvPowerSeries.subst_comp_subst_apply (PowerSeries.hasSubst_iff.mp hHs) hg e

private theorem intertwines_X [Finite σ] (e : LubinTateSeries A π) (i : σ) :
    LubinTateIntertwines e e (MvPowerSeries.X i : MvPowerSeries σ A) := by
  rw [LubinTateIntertwines, subst_X (hasSubst_lubinTateInVariable e)]
  rfl

private theorem intertwines_subst [Finite σ] [Finite τ] (e : LubinTateSeries A π)
    {H : MvPowerSeries σ A} (hH0 : constantCoeff H = 0)
    (hH : LubinTateIntertwines e e H)
    {g : σ → MvPowerSeries τ A} (hg0 : ∀ i, constantCoeff (g i) = 0)
    (hgI : ∀ i, LubinTateIntertwines e e (g i)) :
    LubinTateIntertwines e e (MvPowerSeries.subst g H) := by
  have hgs : MvPowerSeries.HasSubst g := hasSubst_of_constantCoeff_zero hg0
  have hevσ := hasSubst_lubinTateInVariable (σ := σ) e
  have hevτ := hasSubst_lubinTateInVariable (σ := τ) e
  have hHs : PowerSeries.HasSubst H := PowerSeries.HasSubst.of_constantCoeff_zero hH0
  rw [LubinTateIntertwines, ← mvSubst_powerSeries_subst hHs hgs e.toPowerSeries, hH,
    MvPowerSeries.subst_comp_subst_apply hevσ hgs,
    MvPowerSeries.subst_comp_subst_apply hgs hevτ]
  congr 1
  funext i
  rw [show lubinTateInVariable e i =
      PowerSeries.subst (MvPowerSeries.X i) e.toPowerSeries from rfl,
    mvSubst_powerSeries_subst (PowerSeries.HasSubst.X i) hgs e.toPowerSeries,
    subst_X hgs]
  exact hgI i

private theorem eq_single_of_degree_eq_one {u : σ →₀ ℕ} (hu : u.degree = 1) :
    ∃ i, u = Finsupp.single i 1 := by
  classical
  rw [Finsupp.degree_apply] at hu
  have hne : u.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.sum_empty] at hu
    omega
  obtain ⟨i, hi⟩ := hne
  have hui : 1 ≤ u i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  have hsupp : u.support = {i} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hi, ?_⟩
    intro j hj
    by_contra hji
    have huj : 1 ≤ u j := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
    have hsub : ({j, i} : Finset σ) ⊆ u.support := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hj
      · rwa [Finset.mem_singleton.mp hx]
    have h2 : 2 ≤ ∑ x ∈ u.support, u x := by
      calc 2 ≤ ∑ x ∈ ({j, i} : Finset σ), u x := by
            rw [Finset.sum_insert (by simpa using hji), Finset.sum_singleton]
            omega
        _ ≤ _ := Finset.sum_le_sum_of_subset hsub
    omega
  have hii : u i = 1 := by
    rw [hsupp, Finset.sum_singleton] at hu
    exact hu
  refine ⟨i, ?_⟩
  ext j
  rcases eq_or_ne j i with rfl | hji
  · rw [hii, Finsupp.single_eq_same]
  · rw [Finsupp.single_eq_of_ne hji]
    by_contra h
    have : j ∈ u.support := Finsupp.mem_support_iff.mpr h
    rw [hsupp, Finset.mem_singleton] at this
    exact hji this

omit [IsLocalRing A] in
private theorem hasLinearTerm_subst [Fintype σ] [Fintype τ]
    {H : MvPowerSeries σ A} {L : σ → A} (hH : HasLinearTerm H L)
    {g : σ → MvPowerSeries τ A} {M : σ → τ → A}
    (hg : ∀ i, HasLinearTerm (g i) (M i)) :
    HasLinearTerm (MvPowerSeries.subst g H) (fun j => ∑ i, L i * M i j) := by
  classical
  have hgs : MvPowerSeries.HasSubst g :=
    hasSubst_of_constantCoeff_zero fun i => (hg i).constantCoeff_eq_zero
  rw [HasLinearTerm]
  apply le_order
  intro d hd
  have hd1 : d.degree ≤ 1 := by
    have : d.degree < 2 := by exact_mod_cast hd
    omega
  rw [map_sub, MvPowerSeries.coeff_subst hgs]
  have hval : ∑ᶠ (u : σ →₀ ℕ), coeff u H • coeff d (u.prod fun s k => g s ^ k) =
      ∑ i, L i * coeff d (g i) := by
    have hsupp : (Function.support fun u : σ →₀ ℕ =>
        coeff u H • coeff d (u.prod fun s k => g s ^ k)) ⊆
        ↑(Finset.univ.image fun i : σ => Finsupp.single i 1) := by
      intro u hu
      rw [Function.mem_support] at hu
      rcases Nat.lt_or_ge u.degree 2 with hu2 | hu2
      · interval_cases hdu : u.degree
        · exfalso
          apply hu
          have : u = 0 := by rwa [← Finsupp.degree_eq_zero_iff (d := u)]
          rw [this, coeff_zero_eq_constantCoeff_apply, hH.constantCoeff_eq_zero, zero_smul]
        · obtain ⟨i, rfl⟩ := eq_single_of_degree_eq_one hdu
          simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe]
          exact ⟨i, by simp, rfl⟩
      · exfalso
        apply hu
        have hprod : ((u.degree : ℕ) : ℕ∞) ≤ (u.prod fun s k => g s ^ k).order := by
          rw [Finsupp.prod, Finsupp.degree_apply]
          apply le_order_finset_prod' _ _ (fun s => u s)
          intro s _
          exact le_order_pow_of_one_le' (hg s).one_le_order (u s)
        rw [coeff_of_lt_order (lt_of_le_of_lt
          (by exact_mod_cast hd1 : (d.degree : ℕ∞) ≤ (1 : ℕ∞))
          (lt_of_lt_of_le (by exact_mod_cast hu2) hprod)), smul_zero]
    rw [finsum_eq_finsetSum_of_support_subset _ hsupp, Finset.sum_image
      (fun i _ j _ h => by
        simpa using (Finsupp.single_left_injective one_ne_zero) h)]
    apply Finset.sum_congr rfl
    intro i _
    rw [hH.coeff_single i, Finsupp.prod_single_index (by rw [pow_zero]), pow_one,
      smul_eq_mul]
  rw [hval]
  interval_cases hdd : d.degree
  · have hd0 : d = 0 := by rwa [← Finsupp.degree_eq_zero_iff (d := d)]
    rw [hd0]
    rw [coeff_zero_eq_constantCoeff_apply, constantCoeff_lubinTateLinearForm]
    have : ∀ i, coeff (0 : τ →₀ ℕ) (g i) = 0 := fun i => by
      rw [coeff_zero_eq_constantCoeff_apply, (hg i).constantCoeff_eq_zero]
    simp [this]
  · obtain ⟨j, rfl⟩ := eq_single_of_degree_eq_one hdd
    rw [coeff_lubinTateLinearForm_single]
    have : ∀ i, coeff (Finsupp.single j 1) (g i) = M i j := fun i => (hg i).coeff_single j
    simp [this]

omit [IsLocalRing A] in
private theorem hasLinearTerm_X [Fintype σ] [DecidableEq σ] (j : σ) :
    HasLinearTerm (MvPowerSeries.X j : MvPowerSeries σ A)
      (fun i => if i = j then 1 else 0) := by
  rw [HasLinearTerm]
  have : lubinTateLinearForm (fun i : σ => if i = j then (1 : A) else 0) =
      MvPowerSeries.X j := by
    rw [lubinTateLinearForm, Finset.sum_eq_single j]
    · rw [if_pos rfl, map_one, one_mul]
    · intro i _ hij
      rw [if_neg hij, map_zero, zero_mul]
    · simp
  rw [this, sub_self, order_zero]
  exact le_top

end Closure

section FormalGroupAssembly

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)] {π : A}

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] in
private theorem hasLinearTerm_congr {σ : Type*} [Fintype σ] {H : MvPowerSeries σ A}
    {L L' : σ → A} (h : HasLinearTerm H L) (hLL : L = L') : HasLinearTerm H L' :=
  hLL ▸ h

/-- The **standard Lubin–Tate formal group series**: the unique two-variable intertwiner
of the standard series with itself with linear term `X + Y`
([Milne 2020, Chap. I, §2, Prop. 2.12, p.33][MilneCFT];
[Yamaguchi 2026, `LubinTate/FormalModule/StandardFormalGroup.lean:331`]
[Yamaguchi2026]). -/
noncomputable def standardLubinTateFormalGroupPowerSeries (hπ : Irreducible π) :
    MvPowerSeries (Fin 2) A :=
  lubinTateIntertwiner hπ (standardLubinTateSeries hπ) (standardLubinTateSeries hπ)
    (fun _ => 1)

/-- The characterizing property of the standard formal-group series
([Milne 2020, Chap. I, §2, Lem. 2.11 and Prop. 2.12, pp.32–33][MilneCFT];
[Yamaguchi 2026, `LubinTate/FormalModule/StandardFormalGroup.lean:353`]
[Yamaguchi2026]). -/
theorem existsUnique_standardLubinTateFormalGroupPowerSeries (hπ : Irreducible π) :
    ∃! H : MvPowerSeries (Fin 2) A,
      HasLinearTerm H (fun _ => 1) ∧
        LubinTateIntertwines (standardLubinTateSeries hπ)
          (standardLubinTateSeries hπ) H :=
  existsUnique_lubinTateIntertwiner hπ _ _ _

private theorem hLT_std (hπ : Irreducible π) :
    HasLinearTerm (standardLubinTateFormalGroupPowerSeries hπ)
      (fun _ : Fin 2 => (1 : A)) :=
  lubinTateIntertwiner_hasLinearTerm hπ _ _ _

private theorem hI_std (hπ : Irreducible π) :
    LubinTateIntertwines (standardLubinTateSeries hπ) (standardLubinTateSeries hπ)
      (standardLubinTateFormalGroupPowerSeries hπ) :=
  lubinTateIntertwiner_intertwines hπ _ _ _

private theorem hF0_std (hπ : Irreducible π) :
    constantCoeff (standardLubinTateFormalGroupPowerSeries hπ) = 0 :=
  (hLT_std hπ).constantCoeff_eq_zero

private theorem intertwines_pair (hπ : Irreducible π) {n : ℕ}
    (g : Fin 2 → MvPowerSeries (Fin n) A)
    (hg0 : ∀ i, constantCoeff (g i) = 0)
    (hgI : ∀ i, LubinTateIntertwines (standardLubinTateSeries hπ)
      (standardLubinTateSeries hπ) (g i)) :
    LubinTateIntertwines (standardLubinTateSeries hπ) (standardLubinTateSeries hπ)
      (MvPowerSeries.subst g (standardLubinTateFormalGroupPowerSeries hπ)) :=
  intertwines_subst _ (hF0_std hπ) (hI_std hπ) hg0 hgI

private theorem hasLinearTerm_pair (hπ : Irreducible π) {n : ℕ}
    (g : Fin 2 → MvPowerSeries (Fin n) A) (M : Fin 2 → Fin n → A)
    (hg : ∀ i, HasLinearTerm (g i) (M i)) :
    HasLinearTerm (MvPowerSeries.subst g (standardLubinTateFormalGroupPowerSeries hπ))
      (fun j => ∑ i, M i j) := by
  have := hasLinearTerm_subst (hLT_std hπ) hg
  refine hasLinearTerm_congr this ?_
  funext j
  simp

set_option maxHeartbeats 1000000 in
-- The two triple-substitution sides both elaborate against the full intertwiner term.
private theorem assoc_std (hπ : Irreducible π) :
    MvPowerSeries.subst
        ![MvPowerSeries.subst
            ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A),
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) A)]
            (standardLubinTateFormalGroupPowerSeries hπ),
          (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) A)]
        (standardLubinTateFormalGroupPowerSeries hπ) =
      MvPowerSeries.subst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A),
          MvPowerSeries.subst
            ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) A),
              (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) A)]
            (standardLubinTateFormalGroupPowerSeries hπ)]
        (standardLubinTateFormalGroupPowerSeries hπ) := by
  classical
  have hXlt : ∀ j : Fin 3,
      HasLinearTerm (MvPowerSeries.X j : MvPowerSeries (Fin 3) A)
        (fun i => if i = j then (1 : A) else 0) := fun j => hasLinearTerm_X j
  have hG₁lt : HasLinearTerm
      (MvPowerSeries.subst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A),
          (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) A)]
        (standardLubinTateFormalGroupPowerSeries hπ))
      (fun j : Fin 3 => ∑ i : Fin 2,
        ![fun k : Fin 3 => if k = 0 then (1 : A) else 0,
          fun k : Fin 3 => if k = 1 then (1 : A) else 0] i j) := by
    refine hasLinearTerm_pair hπ _ _ ?_
    intro i
    fin_cases i
    · simpa using hXlt 0
    · simpa using hXlt 1
  have hG₂lt : HasLinearTerm
      (MvPowerSeries.subst
        ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) A),
          (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) A)]
        (standardLubinTateFormalGroupPowerSeries hπ))
      (fun j : Fin 3 => ∑ i : Fin 2,
        ![fun k : Fin 3 => if k = 1 then (1 : A) else 0,
          fun k : Fin 3 => if k = 2 then (1 : A) else 0] i j) := by
    refine hasLinearTerm_pair hπ _ _ ?_
    intro i
    fin_cases i
    · simpa using hXlt 1
    · simpa using hXlt 2
  have hG₁I : LubinTateIntertwines (standardLubinTateSeries hπ)
      (standardLubinTateSeries hπ)
      (MvPowerSeries.subst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A),
          (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) A)]
        (standardLubinTateFormalGroupPowerSeries hπ)) := by
    refine intertwines_pair hπ _ ?_ ?_
    · intro i
      fin_cases i <;> simp
    · intro i
      fin_cases i
      · simpa using intertwines_X (σ := Fin 3) (standardLubinTateSeries hπ) 0
      · simpa using intertwines_X (σ := Fin 3) (standardLubinTateSeries hπ) 1
  have hG₂I : LubinTateIntertwines (standardLubinTateSeries hπ)
      (standardLubinTateSeries hπ)
      (MvPowerSeries.subst
        ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) A),
          (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) A)]
        (standardLubinTateFormalGroupPowerSeries hπ)) := by
    refine intertwines_pair hπ _ ?_ ?_
    · intro i
      fin_cases i <;> simp
    · intro i
      fin_cases i
      · simpa using intertwines_X (σ := Fin 3) (standardLubinTateSeries hπ) 1
      · simpa using intertwines_X (σ := Fin 3) (standardLubinTateSeries hπ) 2
  have hLlt : HasLinearTerm
      (MvPowerSeries.subst
        ![MvPowerSeries.subst
            ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A),
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) A)]
            (standardLubinTateFormalGroupPowerSeries hπ),
          (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) A)]
        (standardLubinTateFormalGroupPowerSeries hπ)) (fun _ : Fin 3 => (1 : A)) := by
    refine hasLinearTerm_congr (hasLinearTerm_pair hπ _
      (![fun j : Fin 3 => ∑ i : Fin 2,
          ![fun k : Fin 3 => if k = 0 then (1 : A) else 0,
            fun k : Fin 3 => if k = 1 then (1 : A) else 0] i j,
        fun k : Fin 3 => if k = 2 then (1 : A) else 0]) ?_) ?_
    · intro i
      fin_cases i
      · simpa using hG₁lt
      · simpa using hXlt 2
    · funext j
      fin_cases j <;> simp [Fin.sum_univ_two]
  have hRlt : HasLinearTerm
      (MvPowerSeries.subst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A),
          MvPowerSeries.subst
            ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) A),
              (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) A)]
            (standardLubinTateFormalGroupPowerSeries hπ)]
        (standardLubinTateFormalGroupPowerSeries hπ)) (fun _ : Fin 3 => (1 : A)) := by
    refine hasLinearTerm_congr (hasLinearTerm_pair hπ _
      (![fun k : Fin 3 => if k = 0 then (1 : A) else 0,
        fun j : Fin 3 => ∑ i : Fin 2,
          ![fun k : Fin 3 => if k = 1 then (1 : A) else 0,
            fun k : Fin 3 => if k = 2 then (1 : A) else 0] i j]) ?_) ?_
    · intro i
      fin_cases i
      · simpa using hXlt 0
      · simpa using hG₂lt
    · funext j
      fin_cases j <;> simp [Fin.sum_univ_two]
  have hLI : LubinTateIntertwines (standardLubinTateSeries hπ)
      (standardLubinTateSeries hπ)
      (MvPowerSeries.subst
        ![MvPowerSeries.subst
            ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A),
              (MvPowerSeries.X 1 : MvPowerSeries (Fin 3) A)]
            (standardLubinTateFormalGroupPowerSeries hπ),
          (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) A)]
        (standardLubinTateFormalGroupPowerSeries hπ)) := by
    refine intertwines_pair hπ _ ?_ ?_
    · intro i
      fin_cases i
      · simpa using hG₁lt.constantCoeff_eq_zero
      · simp
    · intro i
      fin_cases i
      · simpa using hG₁I
      · simpa using intertwines_X (σ := Fin 3) (standardLubinTateSeries hπ) 2
  have hRI : LubinTateIntertwines (standardLubinTateSeries hπ)
      (standardLubinTateSeries hπ)
      (MvPowerSeries.subst
        ![(MvPowerSeries.X 0 : MvPowerSeries (Fin 3) A),
          MvPowerSeries.subst
            ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 3) A),
              (MvPowerSeries.X 2 : MvPowerSeries (Fin 3) A)]
            (standardLubinTateFormalGroupPowerSeries hπ)]
        (standardLubinTateFormalGroupPowerSeries hπ)) := by
    refine intertwines_pair hπ _ ?_ ?_
    · intro i
      fin_cases i
      · simp
      · simpa using hG₂lt.constantCoeff_eq_zero
    · intro i
      fin_cases i
      · simpa using intertwines_X (σ := Fin 3) (standardLubinTateSeries hπ) 0
      · simpa using hG₂I
  exact LubinTateIntertwines.eq_of_hasLinearTerm hπ hLlt hLI hRlt hRI

set_option maxHeartbeats 1000000 in
-- The swapped substitution side elaborates against the full intertwiner term.
private theorem comm_std (hπ : Irreducible π) :
    standardLubinTateFormalGroupPowerSeries hπ =
      MvPowerSeries.subst
        ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A),
          (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A)]
        (standardLubinTateFormalGroupPowerSeries hπ) := by
  classical
  have hXlt : ∀ j : Fin 2,
      HasLinearTerm (MvPowerSeries.X j : MvPowerSeries (Fin 2) A)
        (fun i => if i = j then (1 : A) else 0) := fun j => hasLinearTerm_X j
  have hRlt : HasLinearTerm
      (MvPowerSeries.subst
        ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A),
          (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A)]
        (standardLubinTateFormalGroupPowerSeries hπ)) (fun _ : Fin 2 => (1 : A)) := by
    refine hasLinearTerm_congr (hasLinearTerm_pair hπ _
      (![fun k : Fin 2 => if k = 1 then (1 : A) else 0,
        fun k : Fin 2 => if k = 0 then (1 : A) else 0]) ?_) ?_
    · intro i
      fin_cases i
      · simpa using hXlt 1
      · simpa using hXlt 0
    · funext j
      fin_cases j <;> simp [Fin.sum_univ_two]
  have hRI : LubinTateIntertwines (standardLubinTateSeries hπ)
      (standardLubinTateSeries hπ)
      (MvPowerSeries.subst
        ![(MvPowerSeries.X 1 : MvPowerSeries (Fin 2) A),
          (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) A)]
        (standardLubinTateFormalGroupPowerSeries hπ)) := by
    refine intertwines_pair hπ _ ?_ ?_
    · intro i
      fin_cases i <;> simp
    · intro i
      fin_cases i
      · simpa using intertwines_X (σ := Fin 2) (standardLubinTateSeries hπ) 1
      · simpa using intertwines_X (σ := Fin 2) (standardLubinTateSeries hπ) 0
  exact LubinTateIntertwines.eq_of_hasLinearTerm hπ (hLT_std hπ) (hI_std hπ) hRlt hRI

/-- The **standard Lubin–Tate formal group**, landing in Mathlib's `FormalGroup`: the
formal group law admitting the standard series as an endomorphism
([Milne 2020, Chap. I, §2, Prop. 2.12, p.33][MilneCFT];
[Yamaguchi 2026, `LubinTate/FormalModule/StandardFormalGroup.lean:673`]
[Yamaguchi2026]). -/
noncomputable def standardLubinTateFormalGroup (hπ : Irreducible π) : FormalGroup A where
  toPowerSeries := standardLubinTateFormalGroupPowerSeries hπ
  zero_constantCoeff := hF0_std hπ
  lin_coeff_X := by
    have := (hLT_std hπ).coeff_single 0
    simpa using this
  lin_coeff_Y := by
    have := (hLT_std hπ).coeff_single 1
    simpa using this
  assoc := by
    have := assoc_std hπ
    simpa using this

/-- The standard Lubin–Tate formal group is commutative
([Milne 2020, Chap. I, §2, Prop. 2.12, p.33][MilneCFT];
[Yamaguchi 2026, `LubinTate/FormalModule/StandardFormalGroup.lean:688`]
[Yamaguchi2026]). -/
instance standardLubinTateFormalGroup_isComm (hπ : Irreducible π) :
    (standardLubinTateFormalGroup hπ).IsComm where
  comm := by
    have := comm_std hπ
    simpa [standardLubinTateFormalGroup] using this

end FormalGroupAssembly

end Atlas.Knowledge
