import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.ResidueCharacteristic

/-!
# absolute inertia degree

The **absolute inertia degree** `f_K` of a mixed-characteristic local field: the degree
`[𝓀[K] : 𝔽_{p_K}]` of its residue field over the prime field, for `p_K` the residue
characteristic `Atlas.Knowledge.ResidueCharacteristic`. Together with the absolute ramification
index `Atlas.Knowledge.AbsoluteRamificationIndex` it determines the absolute degree
`Atlas.Knowledge.AbsoluteDegree`, and it is one of the six invariants the anabelian layer
recovers group-theoretically.

## Main definitions

* `absoluteInertiaDegree` — the inertia degree of `𝓂[K]` over `ℤ`.

## Main statements

* `card_residueField_eq_pow` — the residue field has `p_K ^ f_K` elements.

## Implementation notes

Encoded as Mathlib's `Ideal.inertiaDeg 𝓂[K] ℤ`, the rank of the residue field of `𝓂[K]` over
that of its pullback to `ℤ`—the prime `(p_K)`, whose residue field is `𝔽_{p_K}`. As with the
ramification index, this is inertia over `ℚ_{p_K}` without a `ℚ_[p]`-algebra structure, and
outside the local-field situation the encoding takes Mathlib's junk values.

As with the ramification index, the encoding and the name are connected by a theorem rather
than left as two assertions: `card_residueField_eq_pow` proves `#𝓀[K] = p_K ^ f_K`, which is
what every counting argument downstream reads `f_K` as—the well-posedness obligation of this
item, the `f`-side sibling of
`Atlas.Knowledge.span_residueCharacteristic_eq_maximalIdeal_pow`.
The proof moves the two residue fields of the encoding onto `𝓀[K]` and `ZMod p_K` along the
canonical maps and counts a finite vector space over its prime field.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- The **absolute inertia degree** of a mixed-characteristic local field: the degree of its
residue field over the prime field `𝔽_{p_K}`, encoded as the inertia degree of `𝓂[K]` over `ℤ`
([Hyeon 2025, §3, p.9][Hyeon2025]). -/
noncomputable def absoluteInertiaDegree (K : Type*) [Field K] [ValuativeRel K] : ℕ :=
  Ideal.inertiaDeg 𝓂[K] ℤ

namespace AbsoluteInertiaDegree

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

set_option synthInstance.maxHeartbeats 80000 in
-- The residue-field rewrites go through `IsLocalRing ↥𝒪[K]`, which does not fit the default
-- instance budget.
/-- The prime of `ℤ` below the maximal ideal is the residue characteristic. -/
private theorem under_eq :
    (𝓂[K] : Ideal ↥𝒪[K]).under ℤ = Ideal.span {(residueCharacteristic K : ℤ)} := by
  haveI := ringChar.charP 𝓀[K]
  ext n
  have hres : IsLocalRing.residue ↥𝒪[K] ((algebraMap ℤ ↥𝒪[K]) n) = (n : 𝓀[K]) := by
    rw [show (algebraMap ℤ ↥𝒪[K]) n = (n : ↥𝒪[K]) by simp, map_intCast]
  rw [Ideal.mem_span_singleton, Ideal.mem_under, ← IsLocalRing.residue_eq_zero_iff, hres]
  exact CharP.intCast_eq_zero_iff 𝓀[K] (ringChar 𝓀[K]) n

set_option synthInstance.maxHeartbeats 80000 in
-- Same instance searches through `IsLocalRing ↥𝒪[K]`.
/-- The residue field counts what the inertia degree is named for: `#𝓀[K] = p_K ^ f_K`
([Serre 1979, Chap. II, §5, p.36][Serre1979], when the residue field of the unequal
characteristic case is finite with q = p^f elements;
[Hyeon 2025, §3, p.9][Hyeon2025]). -/
theorem card_residueField_eq_pow :
    Nat.card 𝓀[K] = residueCharacteristic K ^ absoluteInertiaDegree K := by
  have hp : (residueCharacteristic K).Prime := residueCharacteristic_prime K
  haveI : Fact (residueCharacteristic K).Prime := ⟨hp⟩
  haveI hmax : (𝓂[K] : Ideal ↥𝒪[K]).IsMaximal := IsLocalRing.maximalIdeal.isMaximal _
  have hunder := under_eq K
  haveI hqmax : ((𝓂[K] : Ideal ↥𝒪[K]).under ℤ).IsMaximal := by
    rw [Ideal.Quotient.maximal_ideal_iff_isField_quotient]
    exact ((Ideal.quotEquivOfEq hunder).trans
      (Int.quotientSpanNatEquivZMod (residueCharacteristic K))).toMulEquiv.isField
      (Field.toIsField _)
  have eZ : (ℤ ⧸ (𝓂[K] : Ideal ↥𝒪[K]).under ℤ) ≃+* ZMod (residueCharacteristic K) :=
    (Ideal.quotEquivOfEq hunder).trans
      (Int.quotientSpanNatEquivZMod (residueCharacteristic K))
  have hf : absoluteInertiaDegree K
      = Module.finrank (ℤ ⧸ (𝓂[K] : Ideal ↥𝒪[K]).under ℤ)
          (↥𝒪[K] ⧸ (𝓂[K] : Ideal ↥𝒪[K])) :=
    Ideal.inertiaDeg_eq_of_isMaximal _ _
  letI : Field (ℤ ⧸ (𝓂[K] : Ideal ↥𝒪[K]).under ℤ) := Ideal.Quotient.field _
  haveI : Finite 𝓀[K] := inferInstance
  haveI : Finite (↥𝒪[K] ⧸ (𝓂[K] : Ideal ↥𝒪[K])) := ‹Finite 𝓀[K]›
  haveI : Finite (ℤ ⧸ (𝓂[K] : Ideal ↥𝒪[K]).under ℤ) := Finite.of_equiv _ eZ.toEquiv.symm
  haveI := Fintype.ofFinite (↥𝒪[K] ⧸ (𝓂[K] : Ideal ↥𝒪[K]))
  haveI := Fintype.ofFinite (ℤ ⧸ (𝓂[K] : Ideal ↥𝒪[K]).under ℤ)
  calc Nat.card 𝓀[K]
      = Nat.card (↥𝒪[K] ⧸ (𝓂[K] : Ideal ↥𝒪[K])) := rfl
    _ = Fintype.card (↥𝒪[K] ⧸ (𝓂[K] : Ideal ↥𝒪[K])) := Nat.card_eq_fintype_card
    _ = Fintype.card (ℤ ⧸ (𝓂[K] : Ideal ↥𝒪[K]).under ℤ)
          ^ Module.finrank (ℤ ⧸ (𝓂[K] : Ideal ↥𝒪[K]).under ℤ)
            (↥𝒪[K] ⧸ (𝓂[K] : Ideal ↥𝒪[K])) := Module.card_eq_pow_finrank
    _ = residueCharacteristic K ^ absoluteInertiaDegree K := by
        rw [← hf]
        congr 1
        rw [← Nat.card_eq_fintype_card, Nat.card_congr eZ.toEquiv, Nat.card_zmod]

end AbsoluteInertiaDegree

end Atlas.Knowledge
