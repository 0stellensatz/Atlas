import Mathlib
import Atlas.Knowledge.JumpSetVector
import Atlas.Knowledge.JumpSetExtremal
import Atlas.Knowledge.FiltAut
import Atlas.Knowledge.FilteredBreak

/-!
# filt-ord of a vector

The filtered order of a vector of a free model: the jump set attached to the `≤_ρ`-minimal
points of its coordinate graph. This is the source's coordinate recipe—as `ord (v)` is the
least valuation of the coordinates of `v`, so `filt-ord (v)` is the minimal-point set of their
graph—taken here as the *definition*, which makes it total and computable-in-principle; the
source's Theorem 3.36, that `filt-ord` is a complete invariant of the orbit of `v ∈ π M_ρ^f`
under the filtered automorphism group (resp. of `π (M_ρ^{f - 1} ⊕ M_ρ^*)`, against extended
jump sets), becomes the pair of claims recorded at the end. What is proved here: the recipe
lands on jump sets, and on a normal form `Atlas.Knowledge.JumpSetVector` it returns exactly the
jump set of the pair it was built from—the identification `filt-ord (v_{(I, β)}) = A_{(I, β)}`.

## Main definitions

* `filtOrd` — the jump set attached to the minimal points of the coordinate graph.

## Main statements

* `isJumpSet_filtOrd`, `isJumpSet_filtOrd_star` — the recipe lands on jump sets, plain and
  extended.
* `coordGraph_jumpSetVector`, `filtOrd_jumpSetVector` — the recipe recovers the jump set of a
  normal form.
* `filtOrd_eq_iff_exists_filtAut`, `filtOrd_star_eq_iff_exists_filtAut` — `filt-ord` is a
  complete orbit invariant: the source's classification theorem, recorded ahead of its proof.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The **filtered order** of a vector of a free model: the jump set attached to the
`≤_ρ`-minimal points of its coordinate graph—the source's coordinate recipe for `filt-ord`,
taken as the definition ([Pagano 2022, §1.2, p.405][Pagano2022];
[Pagano 2022, Thm. 3.36, p.433][Pagano2022]). -/
noncomputable def filtOrd (ρ : Shift) {D : Finset (ℕ+ × ℕ)} (v : ↥D → R) : Finset ℕ+ :=
  jumpSetOf ρ (jumpMin ρ (coordGraph v))

/-- Over `M_ρ^f` the recipe lands on jump sets
([Pagano 2022, Thm. 3.36, p.433][Pagano2022]). -/
theorem isJumpSet_filtOrd {ρ : Shift} (hρ : (Shift.T ρ).Finite) {f : ℕ+}
    (v : ↥(Shift.freeIndex hρ f) → R) : IsJumpSet ρ (Shift.T ρ) (filtOrd ρ v) :=
  (isJumpPair_jumpMin ρ fun _ hp => coordGraph_fst_mem_T hρ hp).isJumpSet_jumpSetOf

/-- Over `M_ρ^{f - 1} ⊕ M_ρ^*` the recipe lands on extended jump sets
([Pagano 2022, Thm. 3.36, p.433][Pagano2022]). -/
theorem isJumpSet_filtOrd_star {ρ : Shift} (hρ : (Shift.T ρ).Finite) {f : ℕ+}
    (v : ↥(Shift.starIndex hρ f) → R) :
    IsJumpSet ρ (Shift.T_star ρ hρ) (filtOrd ρ v) :=
  (isJumpPair_jumpMin ρ fun _ hp => coordGraph_fst_mem_T_star hρ hp).isJumpSet_jumpSetOf

private theorem toPNat'_toNat_addVal_pi_pow {π : R} (hπ : Irreducible π) (b : ℕ+) :
    ((addVal R (π ^ (b : ℕ))).toNat).toPNat' = b := by
  rw [(addVal R).map_pow, addVal_uniformizer hπ, nsmul_eq_mul, mul_one, ENat.toNat_coe]
  exact PNat.coe_injective (by rw [Nat.toPNat'_coe, if_pos b.pos])

/-- The coordinate graph of a normal form is the jump pair it was built from, whenever the
model's index carries a first copy of each level of the pair
([Pagano 2022, §1.2, p.405][Pagano2022]). -/
theorem coordGraph_jumpSetVector {ρ : Shift} {S : Set ℕ+} {D : Finset (ℕ+ × ℕ)} {π : R}
    (hπ : Irreducible π) {P : Finset (ℕ+ × ℕ+)} (hP : IsJumpPair ρ S P)
    (hD : ∀ p ∈ P, ((p : ℕ+ × ℕ+).1, 0) ∈ D) :
    coordGraph (jumpSetVector π D P) = P := by
  ext p
  rw [mem_coordGraph]
  constructor
  · rintro ⟨j, hj0, h1, h2⟩
    by_cases hcond : j.1.2 = 0 ∧ j.1.1 ∈ P.image Prod.fst
    · obtain ⟨q, hq, hq1⟩ := Finset.mem_image.mp hcond.2
      have hval : jumpSetVector π D P j = π ^ ((q.2 : ℕ+) : ℕ) := by
        rw [jumpSetVector, if_pos hcond, ← hq1, jumpSetVector.beta_eq hP hq]
      have h2' : ((addVal R (jumpSetVector π D P j)).toNat).toPNat' = q.2 := by
        rw [hval]
        exact toPNat'_toNat_addVal_pi_pow hπ q.2
      have hpq : p = q := by
        refine (Prod.ext ?_ ?_).symm
        · rw [hq1, h1]
        · rw [← h2, h2']
      rw [hpq]
      exact hq
    · exact absurd (by rw [jumpSetVector, if_neg hcond]) hj0
  · intro hp
    refine ⟨⟨(p.1, 0), hD p hp⟩, ?_, rfl, ?_⟩
    · have hcond : (0 : ℕ) = 0 ∧ p.1 ∈ P.image Prod.fst :=
        ⟨rfl, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
      rw [jumpSetVector, if_pos hcond, jumpSetVector.beta_eq hP hp]
      exact pow_ne_zero _ hπ.ne_zero
    · have hcond : (0 : ℕ) = 0 ∧ p.1 ∈ P.image Prod.fst :=
        ⟨rfl, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩
      rw [jumpSetVector, if_pos hcond, jumpSetVector.beta_eq hP hp]
      exact toPNat'_toNat_addVal_pi_pow hπ p.2

/-- Each level of a jump pair over `T_ρ` has its first copy in the free index. -/
theorem freeIndex_fst_mem {ρ : Shift} (hρ : (Shift.T ρ).Finite) {f : ℕ+}
    {S : Set ℕ+} (hS : S ⊆ Shift.T ρ) {P : Finset (ℕ+ × ℕ+)} (hP : IsJumpPair ρ S P) :
    ∀ p ∈ P, ((p : ℕ+ × ℕ+).1, 0) ∈ Shift.freeIndex hρ f := by
  intro p hp
  change (p.1, 0) ∈ hρ.toFinset ×ˢ Finset.range (f : ℕ)
  rw [Finset.mem_product]
  exact ⟨hρ.mem_toFinset.mpr (hS (hP.fst_mem hp)), Finset.mem_range.mpr f.pos⟩

/-- Each level of an extended jump pair has its first copy in the star index. -/
theorem starIndex_fst_mem {ρ : Shift} (hρ : (Shift.T ρ).Finite) {f : ℕ+}
    {P : Finset (ℕ+ × ℕ+)} (hP : IsJumpPair ρ (Shift.T_star ρ hρ) P) :
    ∀ p ∈ P, ((p : ℕ+ × ℕ+).1, 0) ∈ Shift.starIndex hρ f := by
  intro p hp
  change (p.1, 0) ∈ Shift.freeIndex hρ f ∪ {(Shift.e_star ρ hρ, 0)}
  rw [Finset.mem_union]
  rcases hP.fst_mem hp with hT | he
  · left
    change (p.1, 0) ∈ hρ.toFinset ×ˢ Finset.range (f : ℕ)
    rw [Finset.mem_product]
    exact ⟨hρ.mem_toFinset.mpr hT, Finset.mem_range.mpr f.pos⟩
  · right
    rw [Finset.mem_singleton]
    exact Prod.ext he rfl

/-- The recipe recovers the jump set of a normal form: `filt-ord (v_{(I, β)}) = A_{(I, β)}`,
whenever the model's index carries a first copy of each level of the pair. This is the
identification that makes the recipe compute the classification of
[Pagano 2022, Thm. 3.36, p.433][Pagano2022] ([Pagano 2022, §1.2, p.405][Pagano2022]). -/
theorem filtOrd_jumpSetVector {ρ : Shift} {S : Set ℕ+} {D : Finset (ℕ+ × ℕ)} {π : R}
    (hπ : Irreducible π) {P : Finset (ℕ+ × ℕ+)} (hP : IsJumpPair ρ S P)
    (hD : ∀ p ∈ P, ((p : ℕ+ × ℕ+).1, 0) ∈ D) :
    filtOrd ρ (jumpSetVector π D P) = jumpSetOf ρ P := by
  rw [filtOrd, coordGraph_jumpSetVector hπ hP hD, hP.jumpMin_eq_self]

section Claims

/-- The summit of the tranche, plain form: over `M_ρ^f`, `filt-ord` is a complete invariant of
the orbits of `π M_ρ^f` under the filtered automorphism group, so orbits are parametrized by
jump sets. Claim recorded ahead of its proof
([Pagano 2022, Thm. 3.36, p.433][Pagano2022]; also Thm. 1.4, p.404). -/
theorem filtOrd_eq_iff_exists_filtAut {ρ : Shift} (hρ : (Shift.T ρ).Finite) (f : ℕ+) {π : R}
    (hπ : Irreducible π) {v w : ↥(Shift.freeIndex hρ f) → R}
    (hv : v ∈ Ideal.span {π} • (⊤ : Submodule R (↥(Shift.freeIndex hρ f) → R)))
    (hw : w ∈ Ideal.span {π} • (⊤ : Submodule R (↥(Shift.freeIndex hρ f) → R))) :
    filtOrd ρ v = filtOrd ρ w ↔
      ∃ e ∈ (freeFiltered (R := R) ρ (Shift.freeIndex hρ f)).filtAut, e v = w := by
  sorry

/-- The summit of the tranche, extended form: over `M_ρ^{f - 1} ⊕ M_ρ^*`, `filt-ord` is a
complete invariant of the orbits of the π-divisible vectors, so orbits are parametrized by
extended jump sets. Claim recorded ahead of its proof
([Pagano 2022, Thm. 3.36, p.433][Pagano2022]; also Thm. 1.4, p.404). -/
theorem filtOrd_star_eq_iff_exists_filtAut {ρ : Shift} (hρ : (Shift.T ρ).Finite) (f : ℕ+)
    {π : R} (hπ : Irreducible π) {v w : ↥(Shift.starIndex hρ f) → R}
    (hv : v ∈ Ideal.span {π} • (⊤ : Submodule R (↥(Shift.starIndex hρ f) → R)))
    (hw : w ∈ Ideal.span {π} • (⊤ : Submodule R (↥(Shift.starIndex hρ f) → R))) :
    filtOrd ρ v = filtOrd ρ w ↔
      ∃ e ∈ (freeFiltered (R := R) ρ (Shift.starIndex hρ f)).filtAut, e v = w := by
  sorry

end Claims

end Atlas.Knowledge
