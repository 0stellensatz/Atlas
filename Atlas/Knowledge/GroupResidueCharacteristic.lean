import Mathlib

/-!
# group-theoretic residue characteristic

The **group-theoretic residue characteristic** `p(G)` of an abelian group: the prime `ℓ` for
which the quotient of `G` by its torsion subgroup, reduced modulo `ℓ`-th powers, has at least
`ℓ ^ 2` elements. For `G` of MLF^ab-type `Atlas.Knowledge.IsMLFType` that quotient is
`ℤ_p ^ d ⊕ ℤ-hat` with `d ≥ 1`, so the reduction has `ℓ` elements at every prime `ℓ ≠ p` and
`p ^ (d + 1)` at `p`—the test isolates exactly one prime, and
`Atlas.Knowledge.AbelianizedGaloisRecovery` records that it is the residue characteristic
`Atlas.Knowledge.ResidueCharacteristic` of the field. It seeds every companion invariant:
`Atlas.Knowledge.GroupRootOfUnityExponent`, `Atlas.Knowledge.GroupAbsoluteDegree`,
`Atlas.Knowledge.GroupAbsoluteInertiaDegree`, `Atlas.Knowledge.GroupAbsoluteRamificationIndex`,
and the parity index `Atlas.Knowledge.ParityIndex` applied to it.

## Main definitions

* `groupResidueCharacteristic` — `sInf` of the primes passing the `ℓ ^ 2` test.

## Implementation notes

The source characterizes the prime by `log_ℓ` of the cardinality being at least `2`; since the
cardinality in question is a power of `ℓ` whenever it is honest, that is the condition
`ℓ ^ 2 ≤ Nat.card`, which avoids `Nat.log`'s own junk values. `Nat.card` of an infinite
quotient is `0`, failing the test, and `sInf` of the empty set is `0`—so the junk value of a
group not of MLF^ab-type is `0`, and uniqueness of the qualifying prime is part of what
`Atlas.Knowledge.AbelianizedGaloisRecovery` asserts rather than of the definition.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The **group-theoretic residue characteristic** of an abelian group: the least prime `ℓ`
such that the quotient by torsion, reduced modulo `ℓ`-th powers, has at least `ℓ ^ 2` elements
([Hyeon 2025, §3, p.10][Hyeon2025]). -/
noncomputable def groupResidueCharacteristic (G : Type*) [CommGroup G] : ℕ :=
  sInf {ℓ : ℕ | ℓ.Prime ∧
    ℓ ^ 2 ≤ Nat.card ((G ⧸ CommGroup.torsion G) ⧸
      (powMonoidHom ℓ : (G ⧸ CommGroup.torsion G) →* (G ⧸ CommGroup.torsion G)).range)}

end Atlas.Knowledge
