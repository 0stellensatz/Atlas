import Mathlib
import Atlas.Knowledge.FilteredProfiniteGroup

/-!
# isomorphism of filtered profinite groups

An isomorphism of filtered profinite groups is an isomorphism of topological groups carrying the
filtration of the source onto the filtration of the target degreewise: the image of `G.filt v` is
`H.filt v` for every index `v`. This is the "compatibility with the filtrations" that both
anabelian theorems impose, and dropping it makes them false—Yamagata and Jarden–Ritter produced
nonisomorphic mixed-characteristic local fields whose absolute Galois groups are isomorphic as
plain profinite groups ([Hyeon 2025, §1, p.2][Hyeon2025]). The quotient of these isomorphisms by
inner automorphisms of the target is `Atlas.Knowledge.OutFilt`.

## Main definitions

* `FilteredIso` — filtration-preserving continuous isomorphisms between two terms of
  `Atlas.Knowledge.FilteredProfiniteGroup`.

## Implementation notes

The sources say "isomorphism of profinite groups", meaning a continuous group isomorphism;
between profinite (compact Hausdorff) groups the inverse of a continuous isomorphism is
automatically continuous, so bundling both directions as Mathlib's `ContinuousMulEquiv` costs no
generality. The filtration condition is stated with `Subgroup.map`, whose API is what proofs
about images of subgroups run on.

## References

* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- A filtration-preserving isomorphism of filtered profinite groups: a continuous group
isomorphism sending `G.filt v` onto `H.filt v` for every `v`
([Mochizuki 1997, Def. 2.3, p.503][Mochizuki1997]; [Hyeon 2025, §2, p.6][Hyeon2025]). -/
structure FilteredIso (G H : FilteredProfiniteGroup) extends ContinuousMulEquiv G H where
  map_filt : ∀ v, (G.filt v).map toContinuousMulEquiv.toMulEquiv.toMonoidHom = H.filt v

namespace FilteredIso

variable {G H : FilteredProfiniteGroup}

instance : EquivLike (FilteredIso G H) G H where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ _ := by
    cases f
    cases g
    congr
    exact ContinuousMulEquiv.ext (congrFun h₁)

instance : MulEquivClass (FilteredIso G H) G H where
  map_mul f := f.map_mul'

@[simp]
theorem coe_toContinuousMulEquiv (f : FilteredIso G H) : ⇑f.toContinuousMulEquiv = ⇑f :=
  rfl

@[ext]
theorem ext {f g : FilteredIso G H} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

end FilteredIso

end Atlas.Knowledge
