import Mathlib
import Atlas.Knowledge.AbsoluteDegree
import Atlas.Knowledge.GroupAbsoluteDegree
import Atlas.Knowledge.GroupAbsoluteInertiaDegree
import Atlas.Knowledge.GroupAbsoluteRamificationIndex
import Atlas.Knowledge.GroupResidueCharacteristic
import Atlas.Knowledge.GroupRootOfUnityExponent
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.MStepSolvableQuotient
import Atlas.Knowledge.ParityIndex
import Atlas.Knowledge.ResidueCharacteristic
import Atlas.Knowledge.RootOfUnityExponent

/-!
# recovery of the invariants from the abelianized Galois group

The six invariants of a mixed-characteristic local field are computed by the group-theoretic
invariants of the abelianization of its absolute Galois group: `p_K = p(G_K^ab)` and likewise
for `ε`, `a`, `d`, `e`, `f`. This is the source's first reconstruction result, resting on local
class field theory: `G_K^ab` is the profinite completion of `Kˣ`, i.e.
`ℤ ⧸ (p^f - 1) ⊕ ℤ ⧸ p^a ⊕ ℤ_p ^ d ⊕ ℤ-hat`, and each group invariant reads its field
counterpart off that decomposition. The `ε` recovery is not recorded separately as a claim: on
both sides `ε` is the parity index `Atlas.Knowledge.ParityIndex` of the residue characteristic,
so it follows from the `p` recovery by congruence—the one recovery that is already proved.

## Main statements

All but the last are claims recorded ahead of their proofs, which need local class field
theory.

* `residueCharacteristic_eq_groupResidueCharacteristic` — `p_K = p(G_K^ab)`.
* `rootOfUnityExponent_eq_groupRootOfUnityExponent` — `a_K = a(G_K^ab)`.
* `absoluteDegree_eq_groupAbsoluteDegree` — `d_K = d(G_K^ab)`.
* `absoluteInertiaDegree_eq_groupAbsoluteInertiaDegree` — `f_K = f(G_K^ab)`.
* `absoluteRamificationIndex_eq_groupAbsoluteRamificationIndex` — `e_K = e(G_K^ab)`.
* `parityIndex_residueCharacteristic_eq` — `ε_K = ε(G_K^ab)`, by congruence from the first.

## Implementation notes

`G_K^ab` is `mStepSolvableQuotient (Field.absoluteGaloisGroup K) 1`, whose `CommGroup`
instance—needed by every group invariant—comes from the definitional equality with Mathlib's
`TopologicalAbelianization` and lives with `Atlas.Knowledge.MStepSolvableQuotient`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- The residue characteristic of a mixed-characteristic local field is the group-theoretic
residue characteristic of its abelianized absolute Galois group. Claim recorded ahead of its
proof ([Hyeon 2025, Prop. 3.1, p.10][Hyeon2025]). -/
theorem residueCharacteristic_eq_groupResidueCharacteristic :
    residueCharacteristic K
      = groupResidueCharacteristic (mStepSolvableQuotient (Field.absoluteGaloisGroup K) 1) := by
  sorry

/-- The parity index of the residue characteristic of a mixed-characteristic local field is
the parity index of the group-theoretic residue characteristic of its abelianized absolute
Galois group—`ε_K = ε(G_K^ab)`, by congruence from the recovery of `p_K`
([Hyeon 2025, Prop. 3.1, p.10][Hyeon2025]). -/
theorem parityIndex_residueCharacteristic_eq :
    parityIndex (residueCharacteristic K)
      = parityIndex
          (groupResidueCharacteristic (mStepSolvableQuotient (Field.absoluteGaloisGroup K) 1)) :=
  congrArg parityIndex (residueCharacteristic_eq_groupResidueCharacteristic K)

/-- The root-of-unity exponent of a mixed-characteristic local field at its residue
characteristic is the group-theoretic root-of-unity exponent of its abelianized absolute
Galois group. Claim recorded ahead of its proof
([Hyeon 2025, Prop. 3.1, p.10][Hyeon2025]). -/
theorem rootOfUnityExponent_eq_groupRootOfUnityExponent :
    rootOfUnityExponent K (residueCharacteristic K)
      = groupRootOfUnityExponent (mStepSolvableQuotient (Field.absoluteGaloisGroup K) 1) := by
  sorry

/-- The absolute degree of a mixed-characteristic local field is the group-theoretic absolute
degree of its abelianized absolute Galois group. Claim recorded ahead of its proof
([Hyeon 2025, Prop. 3.1, p.10][Hyeon2025]). -/
theorem absoluteDegree_eq_groupAbsoluteDegree :
    absoluteDegree K
      = groupAbsoluteDegree (mStepSolvableQuotient (Field.absoluteGaloisGroup K) 1) := by
  sorry

/-- The absolute inertia degree of a mixed-characteristic local field is the group-theoretic
absolute inertia degree of its abelianized absolute Galois group. Claim recorded ahead of its
proof ([Hyeon 2025, Prop. 3.1, p.10][Hyeon2025]). -/
theorem absoluteInertiaDegree_eq_groupAbsoluteInertiaDegree :
    absoluteInertiaDegree K
      = groupAbsoluteInertiaDegree (mStepSolvableQuotient (Field.absoluteGaloisGroup K) 1) := by
  sorry

/-- The absolute ramification index of a mixed-characteristic local field is the
group-theoretic absolute ramification index of its abelianized absolute Galois group. Claim
recorded ahead of its proof ([Hyeon 2025, Prop. 3.1, p.10][Hyeon2025]). -/
theorem absoluteRamificationIndex_eq_groupAbsoluteRamificationIndex :
    absoluteRamificationIndex K
      = groupAbsoluteRamificationIndex (mStepSolvableQuotient (Field.absoluteGaloisGroup K) 1) := by
  sorry

end Atlas.Knowledge
