import Mathlib
import Atlas.Knowledge.GroupResidueCharacteristic

/-!
# group-theoretic root-of-unity exponent

The **group-theoretic root-of-unity exponent** `a(G)` of an abelian group: the exponent of the
order of the `p(G)`-Sylow subgroup of the torsion of `G`, for `p(G)` the group-theoretic
residue characteristic `Atlas.Knowledge.GroupResidueCharacteristic`. For `G` of MLF^ab-type the
torsion is `ℤ ⧸ (p ^ f - 1) ⊕ ℤ ⧸ p ^ a`, whose `p`-Sylow subgroup has order `p ^ a`—so `a(G)`
recovers the invariant `a_K` of `Atlas.Knowledge.RootOfUnityExponent`, which is what
`Atlas.Knowledge.AbelianizedGaloisRecovery` records.

## Main definitions

* `groupRootOfUnityExponent` — the `p(G)`-adic valuation of the order of the torsion subgroup.

## Implementation notes

The source takes the base-`p(G)` logarithm of the order of the `p(G)`-Sylow subgroup; for a
finite abelian group that order is the `p(G)`-part of the group order, so the encoding is
`Nat.factorization` of `Nat.card` of the torsion at `p(G)`, which needs no `Fact` of primality
and no Sylow machinery. When the torsion is infinite `Nat.card` is `0`, whose factorization is
`0` everywhere—the junk value is `0`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The **group-theoretic root-of-unity exponent** of an abelian group: the exponent of the
order of the `p(G)`-Sylow subgroup of its torsion, encoded as the `p(G)`-adic valuation of the
order of the torsion subgroup ([Hyeon 2025, §3, p.10][Hyeon2025]). -/
noncomputable def groupRootOfUnityExponent (G : Type*) [CommGroup G] : ℕ :=
  (Nat.card (CommGroup.torsion G)).factorization (groupResidueCharacteristic G)

end Atlas.Knowledge
