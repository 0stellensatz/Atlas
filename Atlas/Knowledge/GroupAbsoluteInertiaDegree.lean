import Mathlib
import Atlas.Knowledge.GroupResidueCharacteristic
import Atlas.Knowledge.GroupRootOfUnityExponent

/-!
# group-theoretic absolute inertia degree

The **group-theoretic absolute inertia degree** `f(G)` of an abelian group: the base-`p(G)`
logarithm of one more than the order of the quotient of the torsion of `G` by its `p(G)`-Sylow
subgroup, for `p(G)` the group-theoretic residue characteristic
`Atlas.Knowledge.GroupResidueCharacteristic`. For `G` of MLF^ab-type that quotient has
`p ^ f - 1` elements, so `f(G)` recovers the absolute inertia degree
`Atlas.Knowledge.AbsoluteInertiaDegree` of the field, as
`Atlas.Knowledge.AbelianizedGaloisRecovery` records.

## Main definitions

* `groupAbsoluteInertiaDegree` — the base-`p(G)` logarithm of one more than the order of the
  prime-to-`p(G)` part of the torsion.

## Main statements

* `GroupAbsoluteInertiaDegree.eq_log_card_quotient_sylow` — the degree is the base-`p(G)`
  logarithm of one more than the order of the quotient of a finite torsion by any of its
  `p(G)`-Sylow subgroups: the source's definition, read off the encoding. Proved.

## Implementation notes

For a finite abelian torsion subgroup the quotient by the `p(G)`-Sylow subgroup has order the
prime-to-`p(G)` part of the order, which is `Nat.card` divided by
`p(G) ^ groupRootOfUnityExponent G`—the same encoding choice as
`Atlas.Knowledge.GroupRootOfUnityExponent`, and the reason this file imports it. The Sylow
reading is `eq_log_card_quotient_sylow`, through the order formula for the quotient by a
subgroup and the Sylow order of `GroupRootOfUnityExponent.card_sylow`; the profinite-level
vocabulary is `Atlas.Knowledge.IsProSylow`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The **group-theoretic absolute inertia degree** of an abelian group: the base-`p(G)`
logarithm of one more than the order of the quotient of the torsion by its `p(G)`-Sylow
subgroup ([Hyeon 2025, §3, p.10][Hyeon2025]). -/
noncomputable def groupAbsoluteInertiaDegree (G : Type*) [CommGroup G] : ℕ :=
  Nat.log (groupResidueCharacteristic G)
    (Nat.card (CommGroup.torsion G) /
      groupResidueCharacteristic G ^ groupRootOfUnityExponent G + 1)

namespace GroupAbsoluteInertiaDegree

/-- The degree is the base-`p(G)` logarithm of one more than the order of the quotient of a
finite torsion by any of its `p(G)`-Sylow subgroups: the encoding agrees with the source's
definition ([Hyeon 2025, §3, p.10][Hyeon2025]). -/
theorem eq_log_card_quotient_sylow (G : Type*) [CommGroup G]
    (hp : (groupResidueCharacteristic G).Prime) [Finite (CommGroup.torsion G)]
    (P : Sylow (groupResidueCharacteristic G) (CommGroup.torsion G)) :
    groupAbsoluteInertiaDegree G
      = Nat.log (groupResidueCharacteristic G)
          (Nat.card (CommGroup.torsion G ⧸ (P : Subgroup (CommGroup.torsion G))) + 1) := by
  haveI : Fact (groupResidueCharacteristic G).Prime := ⟨hp⟩
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((P : Subgroup (CommGroup.torsion G)))
  unfold groupAbsoluteInertiaDegree
  rw [h, GroupRootOfUnityExponent.card_sylow G hp P,
    Nat.mul_div_cancel _ (pow_pos hp.pos _)]

end GroupAbsoluteInertiaDegree

end Atlas.Knowledge
