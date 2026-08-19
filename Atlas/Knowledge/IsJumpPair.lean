import Mathlib
import Atlas.Knowledge.Shift
import Atlas.Knowledge.ShiftTStar

/-!
# jump pair

The pair side of the parametrization of jump sets: a **jump pair** for a shift `ρ`, relative to a
set `S` of admissible indices, is the graph of a pair `(I, β)` in the source's sense—a finite set
of points `(i, β i)` with distinct first components drawn from `S`, second components strictly
decreasing in the first, and `ρ` iterated `β i`-many times from `i` strictly increasing in `i`.
Working with the graph rather than with a function on a `Finset` is the source's own move: its
`Max (A, b)` and `Min (A, b)` of `Atlas.Knowledge.JumpSetExtremal` are subsets of `Graph (b)`, and
graphs make equality of pairs plain `Finset` equality, which is what the equivalence
`Atlas.Knowledge.JumpSetEquiv` needs.

## Main definitions

* `IsJumpPair` — graphs of the pairs `(I, β)` with `I ⊆ S`, `β` strictly decreasing, and
  `i ↦ ρ^[β i] i` strictly increasing.

## Main statements

* `IsJumpPair.T_star` — a jump pair over `T ρ` is one over `T_star ρ`: the index set enters
  one clause, and the extended set contains the plain one.
* `IsJumpPair.subset` — a subset of a jump-pair graph is a jump-pair graph: every clause
  quantifies over members only.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- A **jump pair** for the shift `ρ` relative to the index set `S`: the graph of a pair
`(I, β)` with `I ⊆ S`, with `β` strictly decreasing, and with `i ↦ ρ^[β i] i` strictly
increasing. The four clauses are: distinct points have distinct first components, first
components lie in `S`, second components reverse strict order, iterates preserve it
([Pagano 2022, Prop. 2.3, p.416][Pagano2022]). -/
def IsJumpPair (ρ : Shift) (S : Set ℕ+) (P : Finset (ℕ+ × ℕ+)) : Prop :=
  (∀ p ∈ P, ∀ q ∈ P, p.1 = q.1 → p.2 = q.2) ∧
  (∀ p ∈ P, p.1 ∈ S) ∧
  (∀ p ∈ P, ∀ q ∈ P, p.1 < q.1 → q.2 < p.2) ∧
  ∀ p ∈ P, ∀ q ∈ P, p.1 < q.1 → (⇑ρ)^[(p.2 : ℕ)] p.1 < (⇑ρ)^[(q.2 : ℕ)] q.1

namespace IsJumpPair

variable {ρ : Shift} {S : Set ℕ+} {P : Finset (ℕ+ × ℕ+)}

theorem empty (ρ : Shift) (S : Set ℕ+) : IsJumpPair ρ S ∅ := by simp [IsJumpPair]

theorem eq_of_fst_eq (h : IsJumpPair ρ S P) {p q : ℕ+ × ℕ+} (hp : p ∈ P) (hq : q ∈ P)
    (h1 : p.1 = q.1) : p = q :=
  Prod.ext h1 (h.1 p hp q hq h1)

theorem fst_mem (h : IsJumpPair ρ S P) {p : ℕ+ × ℕ+} (hp : p ∈ P) : p.1 ∈ S :=
  h.2.1 p hp

theorem snd_lt_snd (h : IsJumpPair ρ S P) {p q : ℕ+ × ℕ+} (hp : p ∈ P) (hq : q ∈ P)
    (hlt : p.1 < q.1) : q.2 < p.2 :=
  h.2.2.1 p hp q hq hlt

theorem iterate_lt_iterate (h : IsJumpPair ρ S P) {p q : ℕ+ × ℕ+} (hp : p ∈ P) (hq : q ∈ P)
    (hlt : p.1 < q.1) : (⇑ρ)^[(p.2 : ℕ)] p.1 < (⇑ρ)^[(q.2 : ℕ)] q.1 :=
  h.2.2.2 p hp q hq hlt

/-- The iterate comparison of a jump pair, reflected down to the base of the higher point:
`ρ^[p.2 - q.2] p.1` and everything below it stay strictly below `q.1`. -/
theorem iterate_sub_lt (h : IsJumpPair ρ S P) {p q : ℕ+ × ℕ+} (hp : p ∈ P) (hq : q ∈ P)
    (hlt : p.1 < q.1) {n : ℕ} (hn : n ≤ (p.2 : ℕ) - (q.2 : ℕ)) : (⇑ρ)^[n] p.1 < q.1 := by
  have h2 : ((q.2 : ℕ+) : ℕ) < ((p.2 : ℕ+) : ℕ) := by
    exact_mod_cast h.snd_lt_snd hp hq hlt
  have h3 := h.iterate_lt_iterate hp hq hlt
  have hsplit : (p.2 : ℕ) = (q.2 : ℕ) + ((p.2 : ℕ) - (q.2 : ℕ)) := by omega
  rw [hsplit, Function.iterate_add_apply] at h3
  exact lt_of_le_of_lt (ρ.iterate_le_iterate_right p.1 hn)
    ((ρ.strict_mono.iterate (q.2 : ℕ)).lt_iff_lt.mp h3)

/-- A jump pair over `T ρ` is one over `T_star ρ`: the index set enters only the membership
clause, and the extended set contains the plain one. This is the bridge from the plain
membership statements to the extended quantifications of the classification layer. -/
theorem T_star {ρ : Shift} {hρ : (Shift.T ρ).Finite} {P : Finset (ℕ+ × ℕ+)}
    (h : IsJumpPair ρ (Shift.T ρ) P) : IsJumpPair ρ (Shift.T_star ρ hρ) P :=
  ⟨h.1, fun p hp => Or.inl (h.2.1 p hp), h.2.2.1, h.2.2.2⟩

/-- A subset of a jump-pair graph is a jump-pair graph: every clause of the definition
quantifies over members only, so all four restrict. -/
theorem subset {ρ : Shift} {S : Set ℕ+} {P Q : Finset (ℕ+ × ℕ+)}
    (h : IsJumpPair ρ S P) (hsub : Q ⊆ P) : IsJumpPair ρ S Q :=
  ⟨fun a ha b hb => h.1 a (hsub ha) b (hsub hb),
   fun a ha => h.2.1 a (hsub ha),
   fun a ha b hb => h.2.2.1 a (hsub ha) b (hsub hb),
   fun a ha b hb => h.2.2.2 a (hsub ha) b (hsub hb)⟩

end IsJumpPair

end Atlas.Knowledge
