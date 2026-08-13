import Mathlib
import Atlas.Knowledge.GroupResidueCharacteristic

/-!
# group-theoretic absolute degree

The **group-theoretic absolute degree** `d(G)` of an abelian group: one less than the
base-`p(G)` logarithm of the number of elements of the quotient of `G` by torsion reduced
modulo `p(G)`-th powers, for `p(G)` the group-theoretic residue characteristic
`Atlas.Knowledge.GroupResidueCharacteristic`. For `G` of MLF^ab-type that quotient is
`ℤ_p ^ d ⊕ ℤ-hat`, whose reduction mod `p`-th powers has `p ^ (d + 1)` elements—so `d(G)`
recovers the absolute degree `Atlas.Knowledge.AbsoluteDegree` of the field, as
`Atlas.Knowledge.AbelianizedGaloisRecovery` records.

## Main definitions

* `groupAbsoluteDegree` — the base-`p(G)` logarithm of the count, minus one.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The **group-theoretic absolute degree** of an abelian group: one less than the base-`p(G)`
logarithm of the number of elements of the torsion-free quotient reduced modulo `p(G)`-th
powers ([Hyeon 2025, §3, p.10][Hyeon2025]). -/
noncomputable def groupAbsoluteDegree (G : Type*) [CommGroup G] : ℕ :=
  Nat.log (groupResidueCharacteristic G)
    (Nat.card ((G ⧸ CommGroup.torsion G) ⧸
      (powMonoidHom (groupResidueCharacteristic G) :
        (G ⧸ CommGroup.torsion G) →* (G ⧸ CommGroup.torsion G)).range)) - 1

end Atlas.Knowledge
