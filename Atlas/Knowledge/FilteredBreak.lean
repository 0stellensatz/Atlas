import Mathlib
import Atlas.Knowledge.FiltAut
import Atlas.Knowledge.JumpSetVector

/-!
# break function of a vector

The invariant that separates the orbits: for a vector `v` of a filtered module, `g_v (m)` is
the weight of `v` in the quotient by `π^m M`—here, the largest index `i` with
`v ∈ filt i + π^m M`, so no quotient filtration needs constructing. The function is constant
under the filtered automorphism group, and on the jump-set vector `v_{(I, β)}` of
`Atlas.Knowledge.JumpSetVector` it breaks exactly at the multiplicities `β (I)`, with the
recorded values returning the jump set—so each orbit holds at most one normal form. Those two
computations are the source's Proposition 3.34 and Corollary 3.35, recorded as claims ahead of
their proofs; the invariance is proved here.

## Main definitions

* `FilteredModule.breakFn` — the function `g_v`.
* `FilteredModule.BreaksAt` — where it jumps.

## Main statements

* `FilteredModule.breakFn_filtAut` — invariance of `g_v` along the filtered automorphism group.
* `breaksAt_jumpSetVector`, `breaksAt_jumpSetVector_star` — the break behavior of the normal
  forms, claims recorded ahead of their proofs.
* `jumpSetVector_eq_of_filtAut`, `jumpSetVector_star_eq_of_filtAut` — at most one normal form
  per orbit, claims recorded ahead of their proofs.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- Membership in `c • M`, coset-free: the ideal-times-top submodule is the set of multiples. -/
theorem mem_span_singleton_smul_top_iff {c : R} {x : M} :
    x ∈ Ideal.span {c} • (⊤ : Submodule R M) ↔ ∃ y, x = c • y := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on hx ?_ ?_
    · rintro r hr m -
      rw [Ideal.mem_span_singleton] at hr
      obtain ⟨a, rfl⟩ := hr
      exact ⟨a • m, by rw [smul_smul]⟩
    · rintro x y ⟨u, rfl⟩ ⟨w, rfl⟩
      exact ⟨u + w, by rw [smul_add]⟩
  · rintro ⟨y, rfl⟩
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self c) Submodule.mem_top

namespace FilteredModule

variable (F : FilteredModule R M)

/-- The **break function** of a vector: `g_v (m)` is the weight of `v` in the quotient by
`π^m M`, that is, the largest `i` with `v ∈ filt i + π^m M`
([Pagano 2022, Prop. 3.34, p.432][Pagano2022]). -/
noncomputable def breakFn (π : R) (v : M) (m : ℕ) : WithTop ℕ+ :=
  maxIndex fun i => v ∈ F.filt i ⊔ Ideal.span {π ^ m} • (⊤ : Submodule R M)

theorem le_breakFn_iff {π : R} {v : M} {m : ℕ} {i : ℕ+} :
    (i : WithTop ℕ+) ≤ F.breakFn π v m ↔
      v ∈ F.filt i ⊔ Ideal.span {π ^ m} • (⊤ : Submodule R M) :=
  le_maxIndex_iff
    (fun _ _ hij hj => sup_le_sup_right (F.antitone_filt hij) _ hj)
    (Submodule.mem_sup_left (F.filt_one ▸ Submodule.mem_top))

/-- `g_v` **breaks at** `m` when it moves between `m` and `m + 1`
([Pagano 2022, Prop. 3.34, p.432][Pagano2022]). -/
def BreaksAt (π : R) (v : M) (m : ℕ) : Prop :=
  F.breakFn π v m ≠ F.breakFn π v (m + 1)

/-- The break function is constant along the filtered automorphism group, which is what makes
it an invariant of the orbit ([Pagano 2022, Cor. 3.35, p.433][Pagano2022]). -/
theorem breakFn_filtAut {e : M ≃ₗ[R] M} (he : e ∈ F.filtAut) (π : R) (v : M) (m : ℕ) :
    F.breakFn π (e v) m = F.breakFn π v m := by
  have key : ∀ f : M ≃ₗ[R] M, f ∈ F.filtAut → ∀ (w : M) (i : ℕ+),
      w ∈ F.filt i ⊔ Ideal.span {π ^ m} • (⊤ : Submodule R M) →
      f w ∈ F.filt i ⊔ Ideal.span {π ^ m} • (⊤ : Submodule R M) := by
    intro f hf w i hw
    rw [Submodule.mem_sup] at hw ⊢
    obtain ⟨a, ha, x, hx, rfl⟩ := hw
    obtain ⟨y, rfl⟩ := mem_span_singleton_smul_top_iff.mp hx
    refine ⟨f a, (mem_filtAut_iff.mp hf i a).mp ha, π ^ m • f y, ?_, ?_⟩
    · exact mem_span_singleton_smul_top_iff.mpr ⟨f y, rfl⟩
    · rw [map_add, map_smul]
  refine le_antisymm ?_ ?_
  · refine le_of_forall_coe_le fun i hi => ?_
    rw [le_breakFn_iff] at hi ⊢
    have hsymm : e.symm ∈ F.filtAut := F.filtAut.inv_mem he
    have h1 := key e.symm hsymm (e v) i hi
    rwa [e.symm_apply_apply] at h1
  · refine le_of_forall_coe_le fun i hi => ?_
    rw [le_breakFn_iff] at hi ⊢
    exact key e he v i hi

end FilteredModule

section Claims

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The break behavior of the normal form over `M_ρ^f`: `g` breaks exactly at the
multiplicities of the jump pair, and the value one past a multiplicity is the iterate that
recovers the jump set. Claim recorded ahead of its proof
([Pagano 2022, Prop. 3.34, p.432][Pagano2022]). -/
theorem breaksAt_jumpSetVector {ρ : Shift} (hρ : (Shift.T ρ).Finite) (f : ℕ+) {π : R}
    (hπ : Irreducible π) {P : Finset (ℕ+ × ℕ+)} (hP : IsJumpPair ρ (Shift.T ρ) P) :
    (∀ m : ℕ, (freeFiltered (R := R) ρ (Shift.freeIndex hρ f)).BreaksAt π
        (jumpSetVector π (Shift.freeIndex hρ f) P) m ↔ ∃ p ∈ P, ((p.2 : ℕ+) : ℕ) = m) ∧
      ∀ p ∈ P, (freeFiltered (R := R) ρ (Shift.freeIndex hρ f)).breakFn π
          (jumpSetVector π (Shift.freeIndex hρ f) P) ((p.2 : ℕ) + 1)
        = (((⇑ρ)^[(p.2 : ℕ)] p.1 : ℕ+) : WithTop ℕ+) := by
  sorry

/-- The break behavior of the normal form over the presenting module `M_ρ^{f - 1} ⊕ M_ρ^*`,
for extended jump pairs. Claim recorded ahead of its proof
([Pagano 2022, Prop. 3.34, p.432][Pagano2022]). -/
theorem breaksAt_jumpSetVector_star {ρ : Shift} (hρ : (Shift.T ρ).Finite) (f : ℕ+) {π : R}
    (hπ : Irreducible π) {P : Finset (ℕ+ × ℕ+)}
    (hP : IsJumpPair ρ (Shift.T_star ρ hρ) P) :
    (∀ m : ℕ, (freeFiltered (R := R) ρ (Shift.starIndex hρ f)).BreaksAt π
        (jumpSetVector π (Shift.starIndex hρ f) P) m ↔ ∃ p ∈ P, ((p.2 : ℕ+) : ℕ) = m) ∧
      ∀ p ∈ P, (freeFiltered (R := R) ρ (Shift.starIndex hρ f)).breakFn π
          (jumpSetVector π (Shift.starIndex hρ f) P) ((p.2 : ℕ) + 1)
        = (((⇑ρ)^[(p.2 : ℕ)] p.1 : ℕ+) : WithTop ℕ+) := by
  sorry

/-- Each orbit of `π M_ρ^f` holds at most one normal form: two jump pairs whose vectors are
conjugate under the filtered automorphism group coincide. Claim recorded ahead of its proof,
which reads the pair off the break function ([Pagano 2022, Cor. 3.35, p.433][Pagano2022]). -/
theorem jumpSetVector_eq_of_filtAut {ρ : Shift} (hρ : (Shift.T ρ).Finite) (f : ℕ+) {π : R}
    (hπ : Irreducible π) {P Q : Finset (ℕ+ × ℕ+)} (hP : IsJumpPair ρ (Shift.T ρ) P)
    (hQ : IsJumpPair ρ (Shift.T ρ) Q)
    {e : (↥(Shift.freeIndex hρ f) → R) ≃ₗ[R] (↥(Shift.freeIndex hρ f) → R)}
    (he : e ∈ (freeFiltered (R := R) ρ (Shift.freeIndex hρ f)).filtAut)
    (h : e (jumpSetVector π (Shift.freeIndex hρ f) P)
      = jumpSetVector π (Shift.freeIndex hρ f) Q) : P = Q := by
  sorry

/-- The extended version: each orbit of `π (M_ρ^{f - 1} ⊕ M_ρ^*)` holds at most one normal
form. Claim recorded ahead of its proof ([Pagano 2022, Cor. 3.35, p.433][Pagano2022]). -/
theorem jumpSetVector_star_eq_of_filtAut {ρ : Shift} (hρ : (Shift.T ρ).Finite) (f : ℕ+) {π : R}
    (hπ : Irreducible π) {P Q : Finset (ℕ+ × ℕ+)} (hP : IsJumpPair ρ (Shift.T_star ρ hρ) P)
    (hQ : IsJumpPair ρ (Shift.T_star ρ hρ) Q)
    {e : (↥(Shift.starIndex hρ f) → R) ≃ₗ[R] (↥(Shift.starIndex hρ f) → R)}
    (he : e ∈ (freeFiltered (R := R) ρ (Shift.starIndex hρ f)).filtAut)
    (h : e (jumpSetVector π (Shift.starIndex hρ f) P)
      = jumpSetVector π (Shift.starIndex hρ f) Q) : P = Q := by
  sorry

end Claims

end Atlas.Knowledge
