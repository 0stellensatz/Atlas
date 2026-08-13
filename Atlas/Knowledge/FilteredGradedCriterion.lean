import Mathlib
import Atlas.Knowledge.FilteredGradedPiece
import Atlas.Knowledge.FilteredComplete

/-!
# graded criteria for filtered morphisms

The technical heart of the source's §3.2: what the sequence of graded maps `F_i (φ)` of
`Atlas.Knowledge.FilteredGradedPiece` knows about a filtered morphism `φ`. Graded injectivity at
every step says exactly that `φ` preserves weights, hence forces injectivity; graded
surjectivity at every step forces surjectivity once the source is complete in the sense of
`Atlas.Knowledge.FilteredComplete`, by the successive-approximation argument; and so a filtered
morphism out of a complete module whose graded maps are all bijective is a bijection. The
completeness hypothesis in the surjectivity direction is not removable, which is the point of
the source's Remark 3.13.

## Main statements

* `FilteredModule.surjective_of_graded_surjective` — part (a): graded surjectivity plus a
  complete source gives surjectivity.
* `FilteredModule.graded_injective_iff_weight_eq` — part (b): graded injectivity everywhere is
  weight preservation.
* `FilteredModule.injective_of_graded_injective` — part (c): graded injectivity everywhere gives
  injectivity.
* `FilteredModule.graded_bijective_of_iso`, `FilteredModule.bijective_of_graded_bijective` —
  part (d): a filtered isomorphism is graded-bijective, and conversely over a complete source.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

namespace FilteredModule

variable {F : FilteredModule R M} {G : FilteredModule R N}

/-- Part (a) of the criterion: a filtered morphism out of a *complete* filtered module whose
graded maps are all surjective is surjective, by successive approximation
([Pagano 2022, Prop. 3.6, p.421][Pagano2022]). -/
theorem surjective_of_graded_surjective (hM : F.IsComplete) {f : M →ₗ[R] N}
    (hf : IsFilteredHom F G f) (h : ∀ i, Function.Surjective (gradedMap hf i)) :
    Function.Surjective f := by
  intro z
  have hstep : ∀ (i : ℕ+) (y : N), y ∈ G.filt i → ∃ u ∈ F.filt i, y - f u ∈ G.filt (i + 1) :=
    fun i y hy => (gradedMap_surjective_iff hf i).mp (h i) y hy
  choose u hu_mem hu_close using hstep
  -- the successive approximations, with the invariant `z - f s ∈ filt (n + 1)` carried along
  have hsucc : ∀ n : ℕ, (n + 1).succPNat = n.succPNat + 1 := fun n =>
    PNat.coe_injective (by simp [Nat.succPNat_coe, PNat.add_coe])
  let T : ℕ → Type _ := fun n => {s : M // z - f s ∈ G.filt n.succPNat}
  let base : T 0 := ⟨0, by simp [show (0 : ℕ).succPNat = 1 from rfl, G.filt_one]⟩
  let step : ∀ n, T n → T (n + 1) := fun n s =>
    ⟨s.1 + u n.succPNat (z - f s.1) s.2, by
      rw [hsucc n, map_add, ← sub_sub]
      exact hu_close n.succPNat (z - f s.1) s.2⟩
  let seq : ∀ n, T n := fun n => Nat.rec base step n
  have hconsec : ∀ n : ℕ, (seq (n + 1)).1 - (seq n).1 ∈ F.filt n.succPNat := fun n => by
    have : (seq (n + 1)).1 = (seq n).1 + u n.succPNat (z - f (seq n).1) (seq n).2 := rfl
    rw [this, add_sub_cancel_left]
    exact hu_mem n.succPNat _ _
  have haux : ∀ m n : ℕ, m ≤ n → (seq n).1 - (seq m).1 ∈ F.filt m.succPNat := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp [(F.filt m.succPNat).zero_mem]
    | succ n hmn ih =>
      have h1 : (seq (n + 1)).1 - (seq m).1
          = ((seq (n + 1)).1 - (seq n).1) + ((seq n).1 - (seq m).1) := by abel
      rw [h1]
      refine (F.filt m.succPNat).add_mem ?_ ih
      exact F.antitone_filt (by rw [← PNat.coe_le_coe]; simp [Nat.succPNat_coe]; omega)
        (hconsec n)
  set c : ℕ+ → M := fun i => (seq ((i : ℕ) - 1)).1 with hc
  have hcoh : ∀ i j : ℕ+, i ≤ j → c j - c i ∈ F.filt i := by
    intro i j hij
    have h2 : (i : ℕ) - 1 ≤ (j : ℕ) - 1 := by
      have h3 : (i : ℕ) ≤ (j : ℕ) := by exact_mod_cast hij
      omega
    exact le_of_eq (congrArg F.filt (succPNat_sub_one_coe i)) (haux _ _ h2)
  obtain ⟨y, hy⟩ := hM c hcoh
  refine ⟨y, ?_⟩
  have hmem : z - f y ∈ ⨅ i, G.filt i := by
    refine Submodule.mem_iInf _ |>.mpr fun i => ?_
    have h1 : z - f (c i) ∈ G.filt i := by
      have h0 : z - f (c i) ∈ G.filt (((i : ℕ) - 1).succPNat) := (seq ((i : ℕ) - 1)).2
      exact le_of_eq (congrArg G.filt (succPNat_sub_one_coe i)) h0
    have h2 : f (y - c i) ∈ G.filt i := hf i _ (hy i)
    have h3 : z - f y = (z - f (c i)) - f (y - c i) := by
      rw [map_sub]
      abel
    rw [h3]
    exact (G.filt i).sub_mem h1 h2
  rw [G.iInf_filt_eq_bot, Submodule.mem_bot, sub_eq_zero] at hmem
  exact hmem.symm

/-- Part (b) of the criterion: the graded maps are all injective exactly when the morphism
preserves weights ([Pagano 2022, Prop. 3.6, p.421][Pagano2022]). -/
theorem graded_injective_iff_weight_eq {f : M →ₗ[R] N} (hf : IsFilteredHom F G f) :
    (∀ i, Function.Injective (gradedMap hf i)) ↔ ∀ x, G.weight (f x) = F.weight x := by
  constructor
  · intro h x
    refine le_antisymm ?_ (hf.weight_le x)
    have key : ∀ j : ℕ+, f x ∈ G.filt j → x ∈ F.filt j := by
      intro j
      induction j with
      | one => exact fun _ => F.filt_one ▸ Submodule.mem_top
      | succ k ih =>
        intro hj
        have hk : f x ∈ G.filt k := G.antitone_filt (le_of_lt (PNat.lt_add_right k 1)) hj
        exact (gradedMap_injective_iff hf k).mp (h k) x (ih hk) hj
    refine le_of_forall_coe_le fun j hj => ?_
    exact F.le_weight_iff.mpr (key j (G.le_weight_iff.mp hj))
  · intro h i
    rw [gradedMap_injective_iff hf i]
    intro x _ hfx
    rw [← F.le_weight_iff, ← h x, G.le_weight_iff]
    exact hfx

/-- Part (c) of the criterion: graded injectivity at every step forces injectivity
([Pagano 2022, Prop. 3.6, p.421][Pagano2022]). -/
theorem injective_of_graded_injective {f : M →ₗ[R] N} (hf : IsFilteredHom F G f)
    (h : ∀ i, Function.Injective (gradedMap hf i)) : Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hw := (graded_injective_iff_weight_eq hf).mp h x
  rw [hx, G.weight_zero] at hw
  exact F.weight_eq_top_iff.mp hw.symm

/-- The forward half of part (d): a filtered isomorphism—both directions filtered—has bijective
graded maps ([Pagano 2022, Prop. 3.6, p.421][Pagano2022]). -/
theorem graded_bijective_of_iso (e : M ≃ₗ[R] N) (he : IsFilteredHom F G (e : M →ₗ[R] N))
    (he' : IsFilteredHom G F (e.symm : N →ₗ[R] M)) (i : ℕ+) :
    Function.Bijective (gradedMap he i) := by
  constructor
  · rw [gradedMap_injective_iff]
    intro x _ hex
    have := he' (i + 1) _ hex
    simpa using this
  · rw [gradedMap_surjective_iff]
    intro y hy
    refine ⟨e.symm y, he' i y hy, ?_⟩
    simp

/-- The converse half of part (d): a filtered morphism out of a complete filtered module whose
graded maps are all bijective is itself bijective
([Pagano 2022, Prop. 3.6, p.421][Pagano2022]). -/
theorem bijective_of_graded_bijective (hM : F.IsComplete) {f : M →ₗ[R] N}
    (hf : IsFilteredHom F G f) (h : ∀ i, Function.Bijective (gradedMap hf i)) :
    Function.Bijective f :=
  ⟨injective_of_graded_injective hf fun i => (h i).1,
    surjective_of_graded_surjective hM hf fun i => (h i).2⟩

end FilteredModule

end Atlas.Knowledge
