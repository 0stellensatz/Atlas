import Mathlib
import Atlas.Knowledge.FilteredIso

/-!
# filtration-preserving outer isomorphism

The set of filtration-preserving outer isomorphisms between two filtered profinite groups: the
filtration-preserving isomorphisms `Atlas.Knowledge.FilteredIso`, taken modulo composition with
inner automorphisms of the target. Because the terms of a filtration are normal, an inner
automorphism carries each of them onto itself, so the filtration condition descends to the
quotient. This is the set both main theorems compute: the natural map from field isomorphisms
lands in it, and the theorems say the map is a bijection onto it.

## Main definitions

* `OutFilt` — the quotient of `Atlas.Knowledge.FilteredIso` by inner automorphisms of the target.

## Implementation notes

The sources write the quotient as a left coset space `Inn(H)\Isom_filt(G, H)`; here it is the
quotient of `FilteredIso G H` by the relation `OutFilt.setoid`, relating `f` and `g` when some
`h : H` conjugates one onto the other pointwise. There is no group structure in sight—`G` and `H`
are different groups—so this is a `Quotient` of a plain `Setoid`, not a `QuotientGroup`.

## References

* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The relation identifying two filtered isomorphisms that differ by an inner automorphism of
the target: `f ≈ g` iff some `h : H` has `g x = h * f x * h⁻¹` for all `x`
([Mochizuki 1997, Def. 2.3, p.503][Mochizuki1997]; [Hyeon 2025, §2, p.7][Hyeon2025]). -/
def OutFilt.setoid (G H : FilteredProfiniteGroup) : Setoid (FilteredIso G H) where
  r f g := ∃ h : H, ∀ x, g x = h * f x * h⁻¹
  iseqv :=
    { refl := fun f ↦ ⟨1, fun x ↦ by simp⟩
      symm := fun ⟨h, hh⟩ ↦ ⟨h⁻¹, fun x ↦ by rw [hh x]; group⟩
      trans := fun ⟨h₁, hh₁⟩ ⟨h₂, hh₂⟩ ↦ ⟨h₂ * h₁, fun x ↦ by rw [hh₂ x, hh₁ x]; group⟩ }

/-- The set of filtration-preserving outer isomorphisms between two filtered profinite groups:
filtration-preserving isomorphisms modulo inner automorphisms of the target
([Mochizuki 1997, Def. 2.3, p.503][Mochizuki1997]; [Hyeon 2025, §2, p.7][Hyeon2025]). -/
def OutFilt (G H : FilteredProfiniteGroup) : Type _ :=
  Quotient (OutFilt.setoid G H)

/-- The outer isomorphism defined by a filtration-preserving isomorphism. -/
def OutFilt.mk {G H : FilteredProfiniteGroup} (f : FilteredIso G H) : OutFilt G H :=
  Quotient.mk (OutFilt.setoid G H) f

end Atlas.Knowledge
