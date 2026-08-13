import Mathlib

/-!
# filtered module

A **filtered module** over a commutative ring `R` is an `R`-module carrying a decreasing chain of
submodules indexed by the positive integers, meeting in `⊥`. The source states the notion twice
over: as the chain, and as a *weight map* sending each element to the largest index whose
submodule contains it, with `⊤` reserved for `0`. The two carry the same information, and this
file states both and proves the equivalence—`FilteredModule.weight` reads the weight off the
chain, `FilteredModule.ofWeight` rebuilds the chain from a weight map, and the two roundtrips
close. Everything the source's §3 does with a filtered module—morphisms
`Atlas.Knowledge.IsFilteredHom`, products `Atlas.Knowledge.FilteredModulePi`, graded pieces
`Atlas.Knowledge.FilteredGradedPiece`, the ρ-map `Atlas.Knowledge.FilteredRhoMap`—is built on
this structure.

## Main definitions

* `FilteredModule` — the chain form: an antitone `ℕ+`-indexed family of submodules starting at
  `⊤` with infimum `⊥`.
* `FilteredModule.weight` — the weight map into `WithTop ℕ+` attached to the chain.
* `FilteredModule.ofWeight` — the chain rebuilt from a weight map with the three properties the
  source lists.

## Main statements

* `FilteredModule.le_weight_iff` — membership in the chain is comparison against the weight.
* `FilteredModule.weight_eq_top_iff`, `FilteredModule.min_weight_le_add`,
  `FilteredModule.weight_le_smul` — the three properties of the weight map.
* `FilteredModule.weight_ofWeight`, `FilteredModule.ofWeight_weight` — the two roundtrips, which
  make the chain form and the weight form interchangeable.

## Implementation notes

The index is `ℕ+`, matching the domain the project's `Atlas.Knowledge.Shift` already uses, and
weights live in `WithTop ℕ+`. That order is not a complete lattice in Mathlib, so the weight is
not a `sSup`: `FilteredModule.maxIndex` extracts the largest index satisfying a downward-closed
condition by a `Nat.find`, and everything else goes through its characterization
`FilteredModule.le_maxIndex_iff` rather than through the definition.

The chain starts at `⊤` because the source's weight map is everywhere at least `1`: the module
*is* its first filtration step. A filtered submodule in the source's sense is then a filtered
module structure on the submodule itself rather than a substructure here.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- A **filtered module**: a decreasing chain of submodules indexed by `ℕ+`, starting at the
whole module and meeting in `⊥` ([Pagano 2022, Def. 3.1, p.419][Pagano2022]). -/
structure FilteredModule (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] where
  filt : ℕ+ → Submodule R M
  filt_one : filt 1 = ⊤
  antitone_filt : Antitone filt
  iInf_filt_eq_bot : ⨅ i, filt i = ⊥

namespace FilteredModule

@[ext]
theorem ext {F G : FilteredModule R M} (h : ∀ i, F.filt i = G.filt i) : F = G := by
  cases F; cases G; congr; exact funext h

open Classical in
/-- The largest index satisfying a downward-closed condition, as a value in `WithTop ℕ+`; `⊤`
when the condition never fails, and junk `1` when it fails already at `1`. The characterization
is `FilteredModule.le_maxIndex_iff`, and nothing else unfolds this. -/
noncomputable def maxIndex (P : ℕ+ → Prop) : WithTop ℕ+ :=
  if h : ∃ n : ℕ, ¬P n.succPNat then (((Nat.find h).toPNat' : ℕ+) : WithTop ℕ+) else ⊤

theorem succPNat_sub_one_coe (i : ℕ+) : ((i : ℕ) - 1).succPNat = i := by
  have h1 : 0 < (i : ℕ) := i.pos
  exact PNat.coe_injective (by rw [Nat.succPNat_coe]; omega)

theorem maxIndex_eq_top {P : ℕ+ → Prop} (h : ∀ i, P i) : maxIndex P = ⊤ := by
  simp only [maxIndex]
  exact dif_neg fun hex => hex.choose_spec (h _)

theorem forall_of_maxIndex_eq_top {P : ℕ+ → Prop} (h : maxIndex P = ⊤) (i : ℕ+) : P i := by
  classical
  by_contra hi
  have hex : ∃ n : ℕ, ¬P n.succPNat := ⟨(i : ℕ) - 1, by rwa [succPNat_sub_one_coe]⟩
  simp only [maxIndex, dif_pos hex] at h
  exact WithTop.coe_ne_top h

/-- Comparison against `maxIndex` is the condition itself, whenever the condition is
downward-closed and holds at `1`. -/
theorem le_maxIndex_iff {P : ℕ+ → Prop} (hmono : ∀ ⦃i j : ℕ+⦄, i ≤ j → P j → P i) (hP1 : P 1)
    {i : ℕ+} : (i : WithTop ℕ+) ≤ maxIndex P ↔ P i := by
  classical
  simp only [maxIndex]
  split_ifs with h
  · have hspec : ¬P (Nat.find h).succPNat := Nat.find_spec h
    have hfind_pos : 0 < Nat.find h := by
      rcases Nat.eq_zero_or_pos (Nat.find h) with h0 | h1
      · refine absurd hP1 ?_
        rwa [h0, show (0 : ℕ).succPNat = 1 from rfl] at hspec
      · exact h1
    have hcoe : ((Nat.find h).toPNat' : ℕ) = Nat.find h := by
      rw [Nat.toPNat'_coe, if_pos hfind_pos]
    rw [WithTop.coe_le_coe, ← PNat.coe_le_coe, hcoe]
    constructor
    · intro hik
      have hlt : (i : ℕ) - 1 < Nat.find h := by omega
      have := Nat.find_min h hlt
      rw [not_not] at this
      rwa [succPNat_sub_one_coe] at this
    · intro hPi
      by_contra hik
      refine hspec (hmono ?_ hPi)
      rw [← PNat.coe_le_coe, Nat.succPNat_coe]
      omega
  · exact iff_of_true le_top (by
      have := not_exists.mp h ((i : ℕ) - 1)
      rw [not_not, succPNat_sub_one_coe] at this
      exact this)

/-- In `WithTop ℕ+`, an order relation can be tested against every coercion from below. -/
theorem le_of_forall_coe_le {a b : WithTop ℕ+} (h : ∀ i : ℕ+, (i : WithTop ℕ+) ≤ a → ↑i ≤ b) :
    a ≤ b := by
  cases a with
  | top =>
    cases b with
    | top => exact le_rfl
    | coe n =>
      have h2 := h (n + 1) le_top
      rw [WithTop.coe_le_coe, ← PNat.coe_le_coe, PNat.add_coe, PNat.one_coe] at h2
      omega
  | coe n => exact h n le_rfl

variable (F : FilteredModule R M)

/-- The **weight map** of a filtered module: the largest index whose filtration step contains the
element, `⊤` on `0` alone ([Pagano 2022, Def. 3.1, p.419][Pagano2022]). -/
noncomputable def weight (x : M) : WithTop ℕ+ :=
  maxIndex fun i => x ∈ F.filt i

/-- Membership in the chain is comparison against the weight: `x ∈ filt i ↔ i ≤ weight x`. This
is the equivalence of the chain form and the weight form of a filtered module, read pointwise
([Pagano 2022, Def. 3.1, p.419][Pagano2022]). -/
theorem le_weight_iff {x : M} {i : ℕ+} : (i : WithTop ℕ+) ≤ F.weight x ↔ x ∈ F.filt i :=
  le_maxIndex_iff (fun _ _ hij hj => F.antitone_filt hij hj)
    (F.filt_one ▸ Submodule.mem_top)

theorem weight_eq_top_iff {x : M} : F.weight x = ⊤ ↔ x = 0 := by
  constructor
  · intro h
    have hx : x ∈ ⨅ i, F.filt i :=
      Submodule.mem_iInf _ |>.mpr fun i => forall_of_maxIndex_eq_top h i
    rwa [F.iInf_filt_eq_bot, Submodule.mem_bot] at hx
  · rintro rfl
    exact maxIndex_eq_top fun i => (F.filt i).zero_mem

@[simp]
theorem weight_zero : F.weight 0 = ⊤ := F.weight_eq_top_iff.mpr rfl

/-- The weight of a sum is at least the smaller of the weights
([Pagano 2022, Def. 3.1, p.419][Pagano2022]). -/
theorem min_weight_le_add (x y : M) : min (F.weight x) (F.weight y) ≤ F.weight (x + y) :=
  le_of_forall_coe_le fun i hi => F.le_weight_iff.mpr <|
    (F.filt i).add_mem (F.le_weight_iff.mp (hi.trans (min_le_left _ _)))
      (F.le_weight_iff.mp (hi.trans (min_le_right _ _)))

/-- Scaling does not decrease the weight ([Pagano 2022, Def. 3.1, p.419][Pagano2022]). -/
theorem weight_le_smul (a : R) (x : M) : F.weight x ≤ F.weight (a • x) :=
  le_of_forall_coe_le fun _ hi => F.le_weight_iff.mpr <|
    (F.filt _).smul_mem a (F.le_weight_iff.mp hi)

theorem weight_neg (x : M) : F.weight (-x) = F.weight x := by
  refine le_antisymm ?_ ?_
  · simpa using F.weight_le_smul (-1 : R) (-x)
  · simpa using F.weight_le_smul (-1 : R) x

/-- The chain rebuilt from a weight map with the source's three properties: `⊤` exactly on `0`,
superadditivity under `min`, and monotonicity under scaling
([Pagano 2022, Def. 3.1, p.419][Pagano2022]). -/
def ofWeight (w : M → WithTop ℕ+) (h0 : ∀ x, w x = ⊤ ↔ x = 0)
    (hadd : ∀ x y, min (w x) (w y) ≤ w (x + y)) (hsmul : ∀ (a : R) (x : M), w x ≤ w (a • x)) :
    FilteredModule R M where
  filt i :=
    { carrier := {x | (i : WithTop ℕ+) ≤ w x}
      zero_mem' := by simp [(h0 0).mpr rfl]
      add_mem' := fun hx hy => le_trans (le_min hx hy) (hadd _ _)
      smul_mem' := fun a x hx => le_trans hx (hsmul a x) }
  filt_one := by
    rw [Submodule.eq_top_iff']
    intro x
    change (((1 : ℕ+) : WithTop ℕ+)) ≤ w x
    cases hw : w x with
    | top => exact le_top
    | coe n => exact WithTop.coe_le_coe.mpr one_le
  antitone_filt := fun i j hij x hx => le_trans (WithTop.coe_le_coe.mpr hij) hx
  iInf_filt_eq_bot := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_iInf] at hx
    rw [Submodule.mem_bot, ← h0]
    cases hw : w x with
    | top => rfl
    | coe n =>
      exfalso
      have h2 : (((n + 1 : ℕ+)) : WithTop ℕ+) ≤ w x := hx (n + 1)
      rw [hw, WithTop.coe_le_coe, ← PNat.coe_le_coe, PNat.add_coe, PNat.one_coe] at h2
      omega

@[simp]
theorem mem_ofWeight_filt {w : M → WithTop ℕ+} {h0 hadd hsmul} {x : M} {i : ℕ+} :
    x ∈ (ofWeight (R := R) w h0 hadd hsmul).filt i ↔ (i : WithTop ℕ+) ≤ w x :=
  Iff.rfl

/-- First roundtrip of the equivalence: the weight of the chain built from a weight map is that
weight map ([Pagano 2022, Def. 3.1, p.419][Pagano2022]). -/
theorem weight_ofWeight {w : M → WithTop ℕ+} {h0 hadd hsmul} (x : M) :
    (ofWeight (R := R) w h0 hadd hsmul).weight x = w x := by
  refine le_antisymm (le_of_forall_coe_le fun i hi => ?_) (le_of_forall_coe_le fun i hi => ?_)
  · exact (ofWeight w h0 hadd hsmul).le_weight_iff.mp hi
  · exact (ofWeight w h0 hadd hsmul).le_weight_iff.mpr hi

/-- Second roundtrip of the equivalence: the chain built from the weight of a chain is that
chain ([Pagano 2022, Def. 3.1, p.419][Pagano2022]). -/
theorem ofWeight_weight :
    ofWeight F.weight (fun _ => F.weight_eq_top_iff) F.min_weight_le_add F.weight_le_smul = F :=
  ext fun i => by
    ext x
    rw [mem_ofWeight_filt, F.le_weight_iff]

end FilteredModule

end Atlas.Knowledge
