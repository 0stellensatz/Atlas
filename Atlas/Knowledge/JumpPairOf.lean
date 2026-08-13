import Mathlib
import Atlas.Knowledge.IsJumpSet
import Atlas.Knowledge.IsJumpPair

/-!
# jump pair of a jump set

The forward direction of the parametrization of jump sets: to a finite set `A` of positive
integers, attach the graph of the pair `(I_A, β_A)`—the index set `I_A = A \ ρ '' A` of members
not hit by `ρ` from inside `A`, each carrying its `Atlas.Knowledge.JumpMultiplicity`. When `A` is
a jump set `Atlas.Knowledge.IsJumpSet`, the result is a jump pair `Atlas.Knowledge.IsJumpPair`;
that closure is `IsJumpSet.jumpPairOf` below, and the mutually inverse construction is
`Atlas.Knowledge.JumpSetOf`, the two roundtrips living in `Atlas.Knowledge.JumpSetEquiv`.

## Main definitions

* `jumpPairOf` — the graph of `(I_A, β_A)`.

## Main statements

* `mem_jumpPairOf` — membership in the graph, componentwise.
* `IsJumpSet.jumpPairOf` — the graph of a jump set is a jump pair.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- The pair `(I_A, β_A)` of a finite set `A`, as a graph: the members of `A` not hit by `ρ` from
inside `A`, each paired with its `jumpMultiplicity`
([Pagano 2022, Def. 2.2, p.416][Pagano2022]). -/
def jumpPairOf (ρ : Shift) (A : Finset ℕ+) : Finset (ℕ+ × ℕ+) :=
  (A \ A.image ⇑ρ).attach.image fun i =>
    (i.1, ⟨jumpMultiplicity A i.1, jumpMultiplicity_pos (Finset.mem_sdiff.mp i.2).1⟩)

theorem mem_jumpPairOf {ρ : Shift} {A : Finset ℕ+} {q : ℕ+ × ℕ+} :
    q ∈ jumpPairOf ρ A
      ↔ q.1 ∈ A ∧ q.1 ∉ A.image ⇑ρ ∧ (q.2 : ℕ) = jumpMultiplicity A q.1 := by
  constructor
  · intro hq
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp hq
    have hmem := Finset.mem_sdiff.mp i.2
    rw [← hi]
    exact ⟨hmem.1, hmem.2, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    refine Finset.mem_image.mpr ⟨⟨q.1, Finset.mem_sdiff.mpr ⟨h1, h2⟩⟩, Finset.mem_attach _ _, ?_⟩
    exact Prod.ext rfl (Subtype.ext h3.symm)

/-- The graph of `(I_A, β_A)` of a jump set is a jump pair: indices land in `S` by the second
jump-set condition, multiplicities strictly decrease by counting, and the iterate comparison is
the strict walking lemma `IsJumpSet.iterate_jumpMultiplicity_lt`
([Pagano 2022, Prop. 2.3, p.416][Pagano2022]). -/
theorem IsJumpSet.jumpPairOf {ρ : Shift} {S : Set ℕ+} {A : Finset ℕ+} (h : IsJumpSet ρ S A) :
    IsJumpPair ρ S (jumpPairOf ρ A) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp q hq h1
    rw [mem_jumpPairOf] at hp hq
    apply PNat.coe_injective
    rw [hp.2.2, hq.2.2, h1]
  · intro p hp
    rw [mem_jumpPairOf] at hp
    exact h.mem_of_not_mem_image hp.1 hp.2.1
  · intro p hp q hq hlt
    rw [mem_jumpPairOf] at hp hq
    rw [← PNat.coe_lt_coe, hp.2.2, hq.2.2]
    exact jumpMultiplicity_lt_of_lt hp.1 hlt
  · intro p hp q hq hlt
    rw [mem_jumpPairOf] at hp hq
    have hmlt : jumpMultiplicity A q.1 < jumpMultiplicity A p.1 :=
      jumpMultiplicity_lt_of_lt hp.1 hlt
    have hk : (p.2 : ℕ)
        = (q.2 : ℕ) + (jumpMultiplicity A p.1 - jumpMultiplicity A q.1) := by
      rw [hp.2.2, hq.2.2]
      omega
    rw [hk, Function.iterate_add_apply]
    exact (ρ.strict_mono.iterate (q.2 : ℕ))
      (hq.2.2 ▸ h.iterate_jumpMultiplicity_lt hp.1 hq.1 hlt hq.2.1)

end Atlas.Knowledge
