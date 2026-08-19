import Mathlib
import Atlas.Knowledge.GroupTateModule
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.IsTateSystem
import Atlas.Knowledge.MStepSolvableQuotient

/-!
# group-theoretic cyclotomic character

The **group-theoretic cyclotomic character** `χ^(ℓ)(G)` of a topological group carrying a
Tate-module system: the homomorphism into the automorphisms of the group-theoretic Tate module
`Atlas.Knowledge.groupTateModule` by which the group acts on the levels by conjugation. For the
maximal `2`-step solvable quotient of the absolute Galois group of a mixed-characteristic local
field the recorded claim identifies it with Mathlib's `cyclotomicCharacter`: the image of a
Galois element acts on the `ν`th level by raising to the character's value modulo `ℓ ^ ν`—the
source's statement that the cyclotomic character of the field factors through the
group-theoretic character, and the group-side counterpart of the invariance
`Atlas.Knowledge.CyclotomicCharacterInvariance`.

## Main definitions

* `groupCyclotomicCharacter` — the character `G →* MulAut T_ℓ(G)`.

## Main statements

* `groupCyclotomicCharacter_eq_pow_cyclotomicCharacter` — on the maximal `2`-step solvable
  quotient of an absolute Galois group, the character raises each level to the value of the
  `ℓ`-adic cyclotomic character modulo `ℓ ^ ν`. Claim recorded ahead of its proof.

## Implementation notes

The definition takes the normality of the levels and the equivariance of the family `V` as
hypotheses: normality is what lets the group act at all, and equivariance is what carries the
action from the ambient product onto the module, by the stability
`Atlas.Knowledge.GroupTateModule.map_eq`. Equivariance of an honest system is the recorded
claim `Atlas.Knowledge.IsTateSystem.equivariant`, and a definition may not stand on a recorded
claim, so it enters here as an argument—the consumer device of
`Atlas.Knowledge.IsLocalReciprocity` again. The source writes `χ^(ℓ)(G) : G → Aut(T_ℓ(G))` and
specializes to `χ(G) := χ^(p(G^ab))(G)`; with the system and its transfers as parameters the
specialization is the instance at `ℓ` the group-theoretic residue characteristic
`Atlas.Knowledge.GroupResidueCharacteristic` of the abelianization, so no separate definition
is made. In the identification the Galois element enters through `QuotientGroup.mk`, the
projection onto the maximal `2`-step solvable quotient—the factoring of the source—and the
exponent is spelled `PadicInt.toZModPow` applied to the character value, the modulo-`ℓ ^ ν`
reading by which Mathlib's `cyclotomicCharacter.spec` states the action on `ℓ ^ ν`-th roots of
unity.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The **group-theoretic cyclotomic character** `χ^(ℓ)(G)`: the action of the group on its
Tate module, each element acting on every level by conjugation—defined for any family of
normal levels and any equivariant family of maps, the source's case being a Tate-module system
([Hyeon 2025, §3, p.12][Hyeon2025], `χ^(ℓ)(G) : G → Aut(T_ℓ(G))` and `χ(G)`). -/
def groupCyclotomicCharacter (ℓ : ℕ) {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ℕ → Subgroup G) (hN : ∀ ν, (H ν).Normal)
    (V : ∀ ν, TopologicalAbelianization ↥(H ν) →* TopologicalAbelianization ↥(H (ν + 1)))
    (hV : GroupTateModule.Equivariant H hN V) :
    G →* MulAut ↥(groupTateModule ℓ H V) where
  toFun g := ((MulEquiv.piCongrRight fun ν => GroupTateModule.conjAut (H ν) (hN ν) g).subgroupMap
      (groupTateModule ℓ H V)).trans
    (MulEquiv.subgroupCongr (GroupTateModule.map_eq ℓ hN hV g))
  map_one' := by
    ext x ν
    change GroupTateModule.conjAut (H ν) (hN ν) 1
      ((x : ∀ ν, TopologicalAbelianization ↥(H ν)) ν)
      = (x : ∀ ν, TopologicalAbelianization ↥(H ν)) ν
    rw [map_one]
    rfl
  map_mul' g₁ g₂ := by
    ext x ν
    change GroupTateModule.conjAut (H ν) (hN ν) (g₁ * g₂)
      ((x : ∀ ν, TopologicalAbelianization ↥(H ν)) ν)
      = GroupTateModule.conjAut (H ν) (hN ν) g₁ (GroupTateModule.conjAut (H ν) (hN ν) g₂
          ((x : ∀ ν, TopologicalAbelianization ↥(H ν)) ν))
    rw [map_mul]
    rfl

/-- The character acts levelwise by the conjugation action: the coercion of the image of a
module element at a level is `GroupTateModule.conjAut` of its coercion there. -/
@[simp]
theorem groupCyclotomicCharacter_coe (ℓ : ℕ) {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ℕ → Subgroup G) (hN : ∀ ν, (H ν).Normal)
    (V : ∀ ν, TopologicalAbelianization ↥(H ν) →* TopologicalAbelianization ↥(H (ν + 1)))
    (hV : GroupTateModule.Equivariant H hN V) (g : G) (x : ↥(groupTateModule ℓ H V)) (ν : ℕ) :
    (↑(groupCyclotomicCharacter ℓ H hN V hV g x) : ∀ ν, TopologicalAbelianization ↥(H ν)) ν
      = GroupTateModule.conjAut (H ν) (hN ν) g
          ((x : ∀ ν, TopologicalAbelianization ↥(H ν)) ν) :=
  rfl

/-- On the maximal `2`-step solvable quotient of the absolute Galois group of a
mixed-characteristic local field, the group-theoretic cyclotomic character of a Tate-module
system is the `ℓ`-adic cyclotomic character: the image of a Galois element acts on the `ν`th
level of the Tate module by raising to the character's value modulo `ℓ ^ ν`—the cyclotomic
character of the field factors through the group-theoretic character. Claim recorded ahead of
its proof ([Hyeon 2025, Prop. 3.2, p.12][Hyeon2025]). -/
theorem groupCyclotomicCharacter_eq_pow_cyclotomicCharacter (ℓ : ℕ) [Fact ℓ.Prime] (K : Type*)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
    (H : ℕ → Subgroup (mStepSolvableQuotient (Field.absoluteGaloisGroup K) 2))
    (V : ∀ ν, TopologicalAbelianization ↥(H ν) →* TopologicalAbelianization ↥(H (ν + 1)))
    (hS : IsTateSystem ℓ (mStepSolvableQuotient (Field.absoluteGaloisGroup K) 2) H V)
    (hV : GroupTateModule.Equivariant H hS.normal V) (σ : Field.absoluteGaloisGroup K)
    (x : ↥(groupTateModule ℓ H V)) (ν : ℕ) :
    (↑(groupCyclotomicCharacter ℓ H hS.normal V hV (QuotientGroup.mk σ) x) :
        ∀ ν, TopologicalAbelianization ↥(H ν)) ν
      = ((x : ∀ ν, TopologicalAbelianization ↥(H ν)) ν)
          ^ (PadicInt.toZModPow ν (((cyclotomicCharacter (AlgebraicClosure K) ℓ)
              (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K).toRingEquiv : ℤ_[ℓ]ˣ) :
                ℤ_[ℓ])).val := by
  sorry

end Atlas.Knowledge
