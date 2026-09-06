import Mathlib

/-!
# quotient of a subgroup tower

The type-level equivalences of a subgroup tower `M ≤ L ≤ K`: viewing a subgroup
inside a larger one does not change its quotients, and the quotient by the bottom of
a tower splits as the product of the two successive quotient types. Mathlib's
`Subgroup.quotientEquivProdOfLE` gives the split against a subgroup of the ambient
group; these compose it with the `subgroupOf` reading so the pieces are the tower's
own quotients. The reciprocity engine (#104) counts and decomposes Galois-group
quotients through these.

## Main definitions

* `quotientSubgroupOfEquiv` — quotients are unchanged by viewing inside a larger
  subgroup.
* `quotientTowerEquiv` — `K ⧸ M ≃ (K ⧸ L) × (L ⧸ M)` as types.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

open Subgroup

/-- **Viewing a subgroup inside a larger one does not change its quotients**: the
quotient of `H.subgroupOf K` by the subgroup `M` induces is the quotient of `H`
itself by `M` (Yamaguchi 2026, `GroupTheory/QuotientTower.lean:22`). -/
def quotientSubgroupOfEquiv {G : Type*} [Group G] {H K M : Subgroup G}
    (hHK : H ≤ K) :
    (↑(H.subgroupOf K) ⧸ (M.subgroupOf K).subgroupOf (H.subgroupOf K)) ≃
      (↑H ⧸ M.subgroupOf H) where
  toFun := Quotient.map' (subgroupOfEquivOfLe hHK) (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    exact hxy)
  invFun := Quotient.map' (subgroupOfEquivOfLe hHK).symm (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    exact hxy)
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change Quotient.map' _ _ (Quotient.map' _ _ (Quotient.mk'' x)) = Quotient.mk'' x
    simpa only [Quotient.map'_mk''] using
      congrArg Quotient.mk'' ((subgroupOfEquivOfLe hHK).symm_apply_apply x)
  right_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change Quotient.map' _ _ (Quotient.map' _ _ (Quotient.mk'' x)) = Quotient.mk'' x
    simpa only [Quotient.map'_mk''] using
      congrArg Quotient.mk'' ((subgroupOfEquivOfLe hHK).apply_symm_apply x)

/-- **The quotient by the bottom of a subgroup tower splits**: for `M ≤ L ≤ K`,
`K ⧸ M ≃ (K ⧸ L) × (L ⧸ M)` as types — Mathlib's `quotientEquivProdOfLE`
composed with the `subgroupOf` reading (Yamaguchi 2026,
`GroupTheory/QuotientTower.lean:48`). -/
noncomputable def quotientTowerEquiv {G : Type*} [Group G] {M L K : Subgroup G}
    (hML : M ≤ L) (hLK : L ≤ K) :
    (K ⧸ M.subgroupOf K) ≃
      (K ⧸ L.subgroupOf K) × (L ⧸ M.subgroupOf L) :=
  (quotientEquivProdOfLE (subgroupOf_mono K hML)).trans
    (Equiv.prodCongr (Equiv.refl _) (quotientSubgroupOfEquiv hLK))

end Atlas.Knowledge
