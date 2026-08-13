import Mathlib
import Atlas.Knowledge.Shift

/-!
# jump order

The partial order `≤_ρ` on pairs of positive integers that organizes jump sets: `(a₁, b₁) ≤_ρ
(a₂, b₂)` when `b₁ ≤ b₂` and `ρ^[b₁] a₁ ≤ ρ^[b₂] a₂`. Its role is Prop. 2.7 of the source,
`Atlas.Knowledge.JumpSetExtremal`: the graphs of jump pairs `Atlas.Knowledge.IsJumpPair` are
exactly the finite antichains of `≤_ρ` with first components in the index set, so the maximal or
minimal points of any graph are the graph of a unique jump set.

## Main definitions

* `JumpOrder` — the relation `≤_ρ`, with reflexivity, transitivity, antisymmetry.

## Implementation notes

The source's display reads `b₂ ⩾ b₂`, a typo for `b₂ ⩾ b₁`: this direction is the one Prop. 2.7
forces, being the one for which the graph of a jump pair is an antichain—with the other reading
those graphs are chains and a set of maximal points is a single point.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

/-- The order `≤_ρ` on pairs: `(a₁, b₁) ≤_ρ (a₂, b₂)` when `b₁ ≤ b₂` and
`ρ^[b₁] a₁ ≤ ρ^[b₂] a₂` ([Pagano 2022, Def. 2.6, p.418][Pagano2022]). -/
def JumpOrder (ρ : Shift) (x y : ℕ+ × ℕ+) : Prop :=
  x.2 ≤ y.2 ∧ (⇑ρ)^[(x.2 : ℕ)] x.1 ≤ (⇑ρ)^[(y.2 : ℕ)] y.1

instance (ρ : Shift) (x y : ℕ+ × ℕ+) : Decidable (JumpOrder ρ x y) := by
  unfold JumpOrder
  infer_instance

namespace JumpOrder

theorem refl (ρ : Shift) (x : ℕ+ × ℕ+) : JumpOrder ρ x x :=
  ⟨le_refl _, le_refl _⟩

theorem trans {ρ : Shift} {x y z : ℕ+ × ℕ+} (hxy : JumpOrder ρ x y) (hyz : JumpOrder ρ y z) :
    JumpOrder ρ x z :=
  ⟨hxy.1.trans hyz.1, hxy.2.trans hyz.2⟩

theorem antisymm {ρ : Shift} {x y : ℕ+ × ℕ+} (hxy : JumpOrder ρ x y) (hyx : JumpOrder ρ y x) :
    x = y := by
  obtain ⟨h1, h2⟩ := hxy
  obtain ⟨h3, h4⟩ := hyx
  have hsnd : x.2 = y.2 := le_antisymm h1 h3
  have hit : (⇑ρ)^[(x.2 : ℕ)] x.1 = (⇑ρ)^[(y.2 : ℕ)] y.1 := le_antisymm h2 h4
  rw [hsnd] at hit
  exact Prod.ext ((ρ.strict_mono.iterate _).injective hit) hsnd

end JumpOrder

end Atlas.Knowledge
