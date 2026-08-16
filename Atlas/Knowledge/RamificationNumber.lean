import Mathlib
import Atlas.Knowledge.LowerRamificationGroup

/-!
# ramification number

The ramification number `i_G (σ)` of an automorphism of an algebraic extension of a valued
field: the largest `n` such that `σ` moves every integral element by an element of the `n`-th
power of the Jacobson radical, with `i_G (1) = ∞`. The function is the numbering of the lower
filtration read pointwise—`σ ∈ G_i` if and only if `i + 1 ≤ i_G (σ)`—and it is what the proof
of Herbrand's theorem in `Atlas.Knowledge.HerbrandPhi` manipulates in place of the groups
themselves. This file defines `i_G` and proves its interface: the characterization of the
filtration, `i_G (σ) = ∞` exactly at the identity, invariance under conjugation and inverse,
and the two ultrametric laws for a product.

## Main definitions

* `ramificationNumber` — `i_G (σ) ∈ ℕ∞`, the depth of `σ` in the radical filtration.

## Main statements

* `natCast_le_ramificationNumber_iff` — `n ≤ i_G (σ)` iff `σ` moves every integral element
  into the `n`-th radical power.
* `natCast_le_ramificationNumber_iff_of_adjoin_eq_top` — at a generator of the integral
  closure the quantifier collapses to the single element: the source's definition
  `i_G (σ) = v_L (σ x - x)`, recovered as a theorem.
* `mem_lowerRamificationGroup_iff_le_ramificationNumber` — `σ ∈ G_i ↔ i + 1 ≤ i_G (σ)`.
* `mem_lowerRamificationGroup_sub_one_iff` — the `ℕ`-indexed form `σ ∈ G_{n - 1} ↔ n ≤ i_G (σ)`,
  the shape every argument through the levels uses.
* `ramificationNumber_eq_top_iff` — `i_G (σ) = ∞ ↔ σ = 1`.
* `ramificationNumber_conj`, `ramificationNumber_inv` — invariance.
* `min_ramificationNumber_le_mul`, `ramificationNumber_mul_eq_min_of_ne` — the ultrametric
  laws.
* `exists_maximal_ramificationNumber_representative`,
  `ramificationNumber_mul_eq_min_of_maximal` — the maximal representative of a coset and the
  truncation identity it satisfies, the group-theoretic step of Herbrand's theorem.

## Implementation notes

The source defines `i_G (σ) = v_L (σ x₀ - x₀)` at a monogenic generator `x₀` of the ring of
integers and derives the filtration from it; here the dependence is reversed. `i_G` is the
supremum of the radical powers that absorb every difference `σ x - x`, a definition available
without monogenicity and without a valuation on `L`—indeed nothing is asked of the extension
beyond algebraicity: no Galois hypothesis, no finiteness, no local-field structure on `K`—and
the source's description at a generator becomes the theorem
`natCast_le_ramificationNumber_iff_of_adjoin_eq_top`, whose generator
`Atlas.Knowledge.monogenicIntegralClosure` supplies. The supremum is taken in `ℕ∞`, where the
set of absorbing exponents is downward closed, so `natCast_le_ramificationNumber_iff` pins the
value exactly; `= ∞` at the identity is the
separatedness of the radical powers already carried by
`Atlas.Knowledge.exists_lowerRamificationGroup_eq_bot`, and the classical hypotheses enter
only there. The ultrametric equal-case law is proved from the group laws alone—`σ` recovered
as `(σ τ) τ⁻¹`—rather than from valuation theory.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- The **ramification number** `i_G (σ)`: the supremum of the exponents `n` such that
`σ x - x` lies in the `n`-th power of the Jacobson radical for every `x` in the integral
closure of `𝒪[K]` in `L`—the source's `i_G (σ) = v_L (σ x₀ - x₀)`, freed of the choice of a
generator ([Serre 1979, Chap. IV, §1, pp.61–62][Serre1979]). -/
noncomputable def ramificationNumber (σ : L ≃ₐ[K] L) : ℕ∞ :=
  sSup ((↑) '' {m : ℕ | ∀ x : integralClosure 𝒪[K] L,
    galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ x - x ∈
      Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) ^ m})

namespace RamificationNumber

variable {K L}

/-- The set of absorbing exponents is downward closed. -/
private theorem absorbs_of_le {σ : L ≃ₐ[K] L} {m m' : ℕ} (hm' : m' ≤ m)
    (hm : ∀ x : integralClosure 𝒪[K] L,
      galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ x - x ∈
        Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) ^ m) :
    ∀ x : integralClosure 𝒪[K] L,
      galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ x - x ∈
        Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) ^ m' :=
  fun x => Ideal.pow_le_pow_right hm' (hm x)

end RamificationNumber

/-- `n ≤ i_G (σ)` if and only if `σ` moves every element of the integral closure by an element
of the `n`-th radical power ([Serre 1979, Chap. IV, §1, Lem. 1, pp.61–62][Serre1979]). -/
theorem natCast_le_ramificationNumber_iff {σ : L ≃ₐ[K] L} {n : ℕ} :
    (n : ℕ∞) ≤ ramificationNumber K L σ ↔
      ∀ x : integralClosure 𝒪[K] L,
        galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ x - x ∈
          Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) ^ n := by
  constructor
  · intro h
    by_contra hn
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hn fun x => by simp
    have hlt : ramificationNumber K L σ < (n : ℕ∞) :=
      calc ramificationNumber K L σ ≤ ((n - 1 : ℕ) : ℕ∞) := by
            apply sSup_le
            rintro _ ⟨m, hm, rfl⟩
            have hmn : m < n := by
              by_contra hge
              exact hn (RamificationNumber.absorbs_of_le (le_of_not_gt hge) hm)
            exact_mod_cast Nat.le_sub_one_of_lt hmn
        _ < (n : ℕ∞) := by
            exact_mod_cast Nat.sub_lt (Nat.pos_of_ne_zero hn0) one_pos
    exact absurd h (not_le.mpr hlt)
  · intro h
    exact le_sSup ⟨n, h, rfl⟩

/-- At a generator of the integral closure the ramification number is read off the single
element: `n ≤ i_G (σ)` if and only if `σ x - x` lies in the `n`-th radical power. Every other
difference `σ y - y` is a multiple of `σ x - x`, since `y` is a polynomial in `x` over the
fixed base—this is the source's definition `i_G (σ) = v_L (σ x - x)` recovered from the
generator-free one, at the generator `Atlas.Knowledge.monogenicIntegralClosure` supplies
([Serre 1979, Chap. IV, §1, p.62][Serre1979]). -/
theorem natCast_le_ramificationNumber_iff_of_adjoin_eq_top
    {x : integralClosure 𝒪[K] L}
    (hx : Algebra.adjoin 𝒪[K] ({x} : Set (integralClosure 𝒪[K] L)) = ⊤)
    {σ : L ≃ₐ[K] L} {n : ℕ} :
    (n : ℕ∞) ≤ ramificationNumber K L σ ↔
      galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ x - x ∈
        Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) ^ n := by
  rw [natCast_le_ramificationNumber_iff]
  refine ⟨fun h => h x, fun h y => ?_⟩
  have hy : y ∈ Algebra.adjoin 𝒪[K] ({x} : Set (integralClosure 𝒪[K] L)) := by
    rw [hx]; exact Algebra.mem_top
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hy
  obtain ⟨P, rfl⟩ := hy
  obtain ⟨c, hc⟩ := Polynomial.sub_dvd_eval_sub
    (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ x) x
    (P.map (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)))
  have key : galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ (Polynomial.aeval x P) -
      Polynomial.aeval x P =
      (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ x - x) * c := by
    rw [← Polynomial.aeval_algHom_apply, ← Polynomial.eval_map_algebraMap,
      ← Polynomial.eval_map_algebraMap]
    exact hc
  rw [key]
  exact Ideal.mul_mem_right c _ h

/-- Membership in the lower filtration through the ramification number:
`σ ∈ G_i ↔ i + 1 ≤ i_G (σ)`
([Serre 1979, Chap. IV, §1, Lem. 1 and Prop. 1, pp.61–62][Serre1979]). -/
theorem mem_lowerRamificationGroup_iff_le_ramificationNumber {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔
      (((i + 1).toNat : ℕ) : ℕ∞) ≤ ramificationNumber K L σ := by
  rw [mem_lowerRamificationGroup_iff, natCast_le_ramificationNumber_iff]

/-- The `ℕ`-indexed form of the filtration characterization: `σ ∈ G_{n - 1} ↔ n ≤ i_G (σ)`,
the shape every argument through the levels uses—the first displayed law of `i_G`, reindexed
([Serre 1979, Chap. IV, §1, p.62][Serre1979]). -/
theorem mem_lowerRamificationGroup_sub_one_iff {n : ℕ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L ((n : ℤ) - 1) ↔
      (n : ℕ∞) ≤ ramificationNumber K L σ := by
  rw [mem_lowerRamificationGroup_iff_le_ramificationNumber,
    show ((n : ℤ) - 1 + 1).toNat = n by omega]

/-- The ramification number is infinite exactly at the identity—the pointwise form of the
eventual triviality of the filtration ([Serre 1979, Chap. IV, §1, p.62][Serre1979]). -/
theorem ramificationNumber_eq_top_iff [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] {σ : L ≃ₐ[K] L} :
    ramificationNumber K L σ = ⊤ ↔ σ = 1 := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := exists_lowerRamificationGroup_eq_bot K L
    have hmem : σ ∈ lowerRamificationGroup K L n := by
      rw [mem_lowerRamificationGroup_iff_le_ramificationNumber K L, h]
      exact le_top
    rwa [hn, Subgroup.mem_bot] at hmem
  · rintro rfl
    apply top_unique
    apply ENat.forall_natCast_le_iff_le.mp
    intro n _
    rw [natCast_le_ramificationNumber_iff]
    intro x
    simp

/-- The ramification number is invariant under conjugation
([Serre 1979, Chap. IV, §1, p.62][Serre1979]). -/
theorem ramificationNumber_conj (τ σ : L ≃ₐ[K] L) :
    ramificationNumber K L (τ * σ * τ⁻¹) = ramificationNumber K L σ := by
  have key : ∀ (σ' τ' : L ≃ₐ[K] L) (n : ℕ),
      (n : ℕ∞) ≤ ramificationNumber K L σ' →
      (n : ℕ∞) ≤ ramificationNumber K L (τ' * σ' * τ'⁻¹) := by
    intro σ' τ' n h
    exact (mem_lowerRamificationGroup_sub_one_iff K L).mp
      ((inferInstance : (lowerRamificationGroup K L ((n : ℤ) - 1)).Normal).conj_mem σ'
        ((mem_lowerRamificationGroup_sub_one_iff K L).mpr h) τ')
  apply le_antisymm
  · apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    have h := key (τ * σ * τ⁻¹) τ⁻¹ n hn
    rwa [show τ⁻¹ * (τ * σ * τ⁻¹) * τ⁻¹⁻¹ = σ by group] at h
  · apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    exact key σ τ n hn

/-- The ramification number of an inverse—unstated in the source and, like the equal-case
law, proved from the group laws alone ([Serre 1979, Chap. IV, §1, p.62][Serre1979]). -/
theorem ramificationNumber_inv (σ : L ≃ₐ[K] L) :
    ramificationNumber K L σ⁻¹ = ramificationNumber K L σ := by
  have key : ∀ (σ' : L ≃ₐ[K] L) (n : ℕ),
      (n : ℕ∞) ≤ ramificationNumber K L σ' →
      (n : ℕ∞) ≤ ramificationNumber K L σ'⁻¹ := by
    intro σ' n h
    exact (mem_lowerRamificationGroup_sub_one_iff K L).mp
      (inv_mem ((mem_lowerRamificationGroup_sub_one_iff K L).mpr h))
  apply le_antisymm
  · apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    have h := key σ⁻¹ n hn
    rwa [inv_inv] at h
  · apply ENat.forall_natCast_le_iff_le.mp
    intro n hn
    exact key σ n hn

/-- The ramification number of a product is at least the minimum of the factors'—the first
ultrametric law ([Serre 1979, Chap. IV, §1, p.62][Serre1979]). -/
theorem min_ramificationNumber_le_mul (σ τ : L ≃ₐ[K] L) :
    min (ramificationNumber K L σ) (ramificationNumber K L τ) ≤
      ramificationNumber K L (σ * τ) := by
  apply ENat.forall_natCast_le_iff_le.mp
  intro n hn
  exact (mem_lowerRamificationGroup_sub_one_iff K L).mp
    (mul_mem ((mem_lowerRamificationGroup_sub_one_iff K L).mpr (hn.trans (min_le_left _ _)))
      ((mem_lowerRamificationGroup_sub_one_iff K L).mpr (hn.trans (min_le_right _ _))))

/-- Factors of unequal ramification number multiply to the minimum—the second ultrametric
law, unstated in the source and here proved from the group laws alone
([Serre 1979, Chap. IV, §1, p.62][Serre1979]). -/
theorem ramificationNumber_mul_eq_min_of_ne {σ τ : L ≃ₐ[K] L}
    (h : ramificationNumber K L σ ≠ ramificationNumber K L τ) :
    ramificationNumber K L (σ * τ) =
      min (ramificationNumber K L σ) (ramificationNumber K L τ) := by
  apply le_antisymm ?_ (min_ramificationNumber_le_mul K L σ τ)
  rcases lt_or_gt_of_ne h with hlt | hgt
  · rw [min_eq_left hlt.le]
    by_contra hgt'
    have h1 : min (ramificationNumber K L (σ * τ)) (ramificationNumber K L τ⁻¹) ≤
        ramificationNumber K L σ := by
      have h2 := min_ramificationNumber_le_mul K L (σ * τ) τ⁻¹
      rwa [show σ * τ * τ⁻¹ = σ by group] at h2
    rw [ramificationNumber_inv K L] at h1
    exact absurd h1 (not_le.mpr (lt_min (not_le.mp hgt') hlt))
  · rw [min_eq_right hgt.le]
    by_contra hgt'
    have h1 : min (ramificationNumber K L σ⁻¹) (ramificationNumber K L (σ * τ)) ≤
        ramificationNumber K L τ := by
      have h2 := min_ramificationNumber_le_mul K L σ⁻¹ (σ * τ)
      rwa [show σ⁻¹ * (σ * τ) = τ by group] at h2
    rw [ramificationNumber_inv K L] at h1
    exact absurd h1 (not_le.mpr (lt_min hgt (not_le.mp hgt')))

/-- Every coset of a normal subgroup of the Galois group contains a representative of maximal
ramification number—the element Serre takes with `i_G (s) = j (σ)`
([Serre 1979, Chap. IV, §3, proof of Lem. 4, pp.74–75][Serre1979]). -/
theorem exists_maximal_ramificationNumber_representative [FiniteDimensional K L]
    (H : Subgroup (L ≃ₐ[K] L)) [H.Normal] (q : (L ≃ₐ[K] L) ⧸ H) :
    ∃ σ : L ≃ₐ[K] L, QuotientGroup.mk' H σ = q ∧
      ∀ γ : L ≃ₐ[K] L, QuotientGroup.mk' H γ = q →
        ramificationNumber K L γ ≤ ramificationNumber K L σ := by
  have hne : Nonempty {σ : L ≃ₐ[K] L // QuotientGroup.mk' H σ = q} := by
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective H q
    exact ⟨⟨σ, hσ⟩⟩
  obtain ⟨⟨σ, hσ⟩, hmax⟩ := Finite.exists_max
    (fun γ : {σ : L ≃ₐ[K] L // QuotientGroup.mk' H σ = q} =>
      ramificationNumber K L (γ : L ≃ₐ[K] L))
  exact ⟨σ, hσ, fun γ hγ => hmax ⟨γ, hγ⟩⟩

/-- A representative of maximal ramification number in its coset truncates the whole coset:
`i_G (σ τ) = min (i_G (τ), i_G (σ))` for every `τ` in the subgroup—Serre's "in either case,
`i_G (s t) = Inf (i_G (t), m)`"
([Serre 1979, Chap. IV, §3, proof of Lem. 4, pp.74–75][Serre1979]). -/
theorem ramificationNumber_mul_eq_min_of_maximal {H : Subgroup (L ≃ₐ[K] L)} [H.Normal]
    {σ : L ≃ₐ[K] L}
    (hmax : ∀ γ : L ≃ₐ[K] L, QuotientGroup.mk' H γ = QuotientGroup.mk' H σ →
      ramificationNumber K L γ ≤ ramificationNumber K L σ)
    (τ : H) :
    ramificationNumber K L (σ * τ) =
      min (ramificationNumber K L (τ : L ≃ₐ[K] L)) (ramificationNumber K L σ) := by
  have hfiber : QuotientGroup.mk' H (σ * (τ : L ≃ₐ[K] L)) = QuotientGroup.mk' H σ := by
    rw [map_mul]
    simp [(QuotientGroup.eq_one_iff (τ : L ≃ₐ[K] L)).mpr τ.property]
  by_cases hne : ramificationNumber K L σ = ramificationNumber K L (τ : L ≃ₐ[K] L)
  · rw [← hne, min_self]
    apply le_antisymm (hmax _ hfiber)
    have h := min_ramificationNumber_le_mul K L σ (τ : L ≃ₐ[K] L)
    rwa [← hne, min_self] at h
  · rw [ramificationNumber_mul_eq_min_of_ne K L hne, min_comm]

end Atlas.Knowledge
