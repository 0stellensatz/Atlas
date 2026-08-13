import Mathlib

/-!
# root-of-unity exponent

The **`ℓ`-power root-of-unity exponent** of a commutative monoid: the largest `a` such that a
primitive `ℓ ^ a`-th root of unity is present. For `K` a mixed-characteristic local field and `ℓ`
its residue characteristic `Atlas.Knowledge.ResidueCharacteristic`, this is the invariant `a_K`
of the anabelian layer: `p_K ^ a_K` is the order of the `p_K`-primary torsion of `Kˣ`, the one
part of the unit group's structure not accounted for by the residue field and the free part.

## Main definitions

* `rootOfUnityExponent` — `sSup` of the set of `a` with a primitive `ℓ ^ a`-th root of unity.

## Implementation notes

Encoded as an `sSup` in `ℕ`, which takes the junk value `0` when the set of such `a` is
unbounded—no roots-of-unity finiteness is prepaid by the definition. The set always contains
`0`, since `1` is a primitive first root of unity, so the value is honest exactly when the set is
bounded; that it is bounded for a mixed-characteristic local field is for the layer to record
when the anabelian development needs it.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The **`ℓ`-power root-of-unity exponent** of a commutative monoid: the largest `a` for which a
primitive `ℓ ^ a`-th root of unity exists. For a mixed-characteristic local field and `ℓ` its
residue characteristic, this is the invariant `a_K` ([Hyeon 2025, §3, p.9][Hyeon2025]). -/
noncomputable def rootOfUnityExponent (M : Type*) [CommMonoid M] (ℓ : ℕ) : ℕ :=
  sSup {a : ℕ | ∃ ζ : M, IsPrimitiveRoot ζ (ℓ ^ a)}

end Atlas.Knowledge
