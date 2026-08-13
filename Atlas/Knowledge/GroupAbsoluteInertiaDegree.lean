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

## Implementation notes

For a finite abelian torsion subgroup the quotient by the `p(G)`-Sylow subgroup has order the
prime-to-`p(G)` part of the order, which is `Nat.card` divided by
`p(G) ^ groupRootOfUnityExponent G`—the same encoding choice as
`Atlas.Knowledge.GroupRootOfUnityExponent`, and the reason this file imports it.

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

end Atlas.Knowledge
