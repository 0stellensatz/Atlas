import Mathlib

/-!
# finite commutative group cyclic factors

Coordinate characters obtained from the structure theorem separate the
elements of a finite commutative group: a jointly faithful finite family
of surjections onto cyclic `ZMod` groups, the group-theoretic source of
the reduction to cyclic subextensions (#104).

## Main statements

* `finiteCommGroup_exists_jointlyFaithful_cyclic_factors` — the family
  exists; proved from Mathlib's structure theorem.

## Implementation notes

A straight port: the theorem is pure Mathlib group theory, and the
source file's remaining declarations — the pullback machinery for the
Kummer decomposition — have no consumer inside `Reciprocity/Main.lean`'s
import closure and stay unported.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

/-- **Coordinate characters obtained from the structure theorem separate
the elements of a finite commutative group** ([Yamaguchi 2026,
`KummerTheory/Abstract/KummerAbelianCyclicFactors.lean:28`]
[Yamaguchi2026]). -/
theorem finiteCommGroup_exists_jointlyFaithful_cyclic_factors
    (Q : Type*) [CommGroup Q] [Finite Q] :
    ∃ (ι : Type 0) (_ : Fintype ι) (m : ι → ℕ),
      (∀ i, 1 < m i) ∧
      ∃ f : ∀ i, Q →* Multiplicative (ZMod (m i)),
        (∀ i, Function.Surjective (f i)) ∧
        (⨅ i, MonoidHom.ker (f i)) = ⊥ := by
  obtain ⟨ι, hι, m, hm, ⟨e⟩⟩ :=
    CommGroup.equiv_prod_multiplicative_zmod_of_finite Q
  let f : ∀ i, Q →* Multiplicative (ZMod (m i)) := fun i =>
    (Pi.evalMonoidHom (fun j => Multiplicative (ZMod (m j))) i).comp e
  refine ⟨ι, hι, m, hm, f, ?_, ?_⟩
  · intro i
    exact (Function.surjective_eval i).comp e.surjective
  · apply le_antisymm
    · intro x hx
      rw [Subgroup.mem_bot]
      apply e.injective
      ext i
      have hxi : x ∈ MonoidHom.ker (f i) :=
        (Subgroup.mem_iInf.mp hx) i
      simpa [f] using MonoidHom.mem_ker.mp hxi
    · exact bot_le

end

end Atlas.Knowledge
