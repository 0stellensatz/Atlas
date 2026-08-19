import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.IsTateSystem
import Atlas.Knowledge.MStepSolvableQuotient

/-!
# group-theoretic Tate module

The **group-theoretic Tate module** `T_ℓ(G)` of a topological group equipped with a Tate-module
system `Atlas.Knowledge.IsTateSystem`: the inverse limit of the `ℓ ^ ν`-torsion subgroups of
the abelianizations of the levels, realized as the subgroup of their product cut out by the
torsion condition and the compatibility `V ν (x ν) = x (ν + 1) ^ ℓ`. The group acts on each
level's abelianization by conjugation, the module is stable under the action, and for the
maximal `2`-step solvable quotient of the absolute Galois group of a mixed-characteristic local
field the module is a copy of `ℤ_ℓ`—the carrier half of the source's Proposition 3.2 (1), whose
action half is the identification recorded with
`Atlas.Knowledge.groupCyclotomicCharacter`.

## Main definitions

* `groupTateModule` — the compatible sequences of torsion classes, a subgroup of the product of
  the abelianizations.
* `GroupTateModule.conjAut` — the conjugation action of the group on the topological
  abelianization of a normal subgroup.
* `GroupTateModule.Equivariant` — the compatibility of the maps `V ν` with the conjugation
  actions of the two levels.

## Main statements

* `GroupTateModule.map_eq` — an equivariant family of maps makes the module stable under the
  levelwise conjugation action: the `G`-module structure of the limit. Proved.
* `IsTateSystem.equivariant` — over a Tate-module system the transfers are equivariant. Claim
  recorded ahead of its proof.
* `groupTateModule_equiv_padicInt` — over the maximal `2`-step solvable quotient of the
  absolute Galois group of a mixed-characteristic local field, the module is topologically
  isomorphic to `ℤ_ℓ`. Claim recorded ahead of its proof.

## Implementation notes

The source forms the limit along the maps `Ver⁻¹ ∘ (−)^ℓ`, available because `Ver` is injective
on the torsion with image containing the needed classes; inverting `Ver` inside a definition
would stand on those facts, which enter this layer only as claims, and a definition may not
carry a `sorry`. The subgroup of compatible sequences is the same limit read off the
identification of the source: an element of `T_ℓ(G)` is a choice of `x ν` in the
`ℓ ^ ν`-torsion of each level with `x ν` corresponding to `x (ν + 1) ^ ℓ` under the
identification by `Ver`, which is the equation `V ν (x ν) = x (ν + 1) ^ ℓ`, and that equation
needs no inverse. The definition is total in the family `V`: an arbitrary family cuts out some
subgroup, and away from a Tate-module system nothing is claimed about it. The conjugation
action `conjAut` is `MulAut.conjNormal` pushed through the abelianization functor
`Atlas.Knowledge.mStepSolvableQuotient.map` at `m = 1`, with the automorphism inverted by
functoriality rather than topology, so no compactness is hypothesized. Equivariance of an
honest transfer under the simultaneous conjugation of the pair is what makes the source's
inverse system one of `G`-modules; it is a property of the transfer, not of a general family
`V`, so it is recorded as the claim `IsTateSystem.equivariant` and consumed as a hypothesis
by `Atlas.Knowledge.groupCyclotomicCharacter`—the device of
`Atlas.Knowledge.IsLocalReciprocity` one level up. The isomorphism claim takes the module to
`Multiplicative ℤ_[ℓ]`, the additive group of the `ℓ`-adic integers read multiplicatively, and
topologically: the source's `T_ℓ(G) ≅ ℤ_ℓ` is an isomorphism of profinite modules, and the
subtype-of-product topology on the module is the limit topology.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The **group-theoretic Tate module** `T_ℓ(G)`: the subgroup of the product of the
abelianizations of the levels of a sequence consisting of the `x` with each `x ν` in the
`ℓ ^ ν`-torsion and `V ν (x ν) = x (ν + 1) ^ ℓ`—the inverse limit of the torsion subgroups
along the maps the transfers induce, read as compatible sequences
([Hyeon 2025, §3, p.12][Hyeon2025], `T_ℓ(G) := lim ← H_ν^ab[ℓ^ν]`). -/
def groupTateModule (ℓ : ℕ) {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : ℕ → Subgroup G)
    (V : ∀ ν, TopologicalAbelianization ↥(H ν) →* TopologicalAbelianization ↥(H (ν + 1))) :
    Subgroup (∀ ν, TopologicalAbelianization ↥(H ν)) where
  carrier := {x | ∀ ν, x ν ^ ℓ ^ ν = 1 ∧ V ν (x ν) = x (ν + 1) ^ ℓ}
  one_mem' := fun ν => ⟨one_pow _, by simp⟩
  mul_mem' := fun {a b} ha hb ν => by
    refine ⟨?_, ?_⟩
    · rw [Pi.mul_apply, mul_pow, (ha ν).1, (hb ν).1, mul_one]
    · rw [Pi.mul_apply, map_mul, (ha ν).2, (hb ν).2, Pi.mul_apply, mul_pow]
  inv_mem' := fun {a} ha ν => by
    refine ⟨?_, ?_⟩
    · rw [Pi.inv_apply, inv_pow, (ha ν).1, inv_one]
    · rw [Pi.inv_apply, map_inv, (ha ν).2, Pi.inv_apply, inv_pow]

namespace GroupTateModule

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Conjugation by a group element on a normal subgroup, as an endomorphism of the topological
abelianization: `MulAut.conjNormal` pushed through the abelianization functor. -/
def conjMap (N : Subgroup G) (hN : N.Normal) (g : G) :
    TopologicalAbelianization ↥N →* TopologicalAbelianization ↥N :=
  haveI := hN
  mStepSolvableQuotient.map 1 (MulAut.conjNormal g).toMonoidHom
    (Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _)

theorem conjMap_comp (N : Subgroup G) (hN : N.Normal) (g₁ g₂ : G)
    (x : TopologicalAbelianization ↥N) :
    conjMap N hN g₁ (conjMap N hN g₂ x) = conjMap N hN (g₁ * g₂) x := by
  haveI := hN
  refine QuotientGroup.induction_on x fun z => ?_
  change QuotientGroup.mk (MulAut.conjNormal g₁ (MulAut.conjNormal g₂ z))
    = QuotientGroup.mk (MulAut.conjNormal (g₁ * g₂) z)
  rw [map_mul]
  rfl

theorem conjMap_one (N : Subgroup G) (hN : N.Normal) (x : TopologicalAbelianization ↥N) :
    conjMap N hN 1 x = x := by
  haveI := hN
  refine QuotientGroup.induction_on x fun z => ?_
  change QuotientGroup.mk (MulAut.conjNormal (1 : G) z) = QuotientGroup.mk z
  rw [map_one]
  rfl

/-- The **conjugation action** of a group on the topological abelianization of a normal
subgroup: each element acts through `GroupTateModule.conjMap`, inverted by the action of the
inverse ([Hyeon 2025, §3, p.11][Hyeon2025], the note that `G` acts on `H_ν^ab[ℓ^ν]` by
conjugation). -/
def conjAut (N : Subgroup G) (hN : N.Normal) : G →* MulAut (TopologicalAbelianization ↥N) where
  toFun g := MonoidHom.toMulEquiv (conjMap N hN g) (conjMap N hN g⁻¹)
    (MonoidHom.ext fun x => by
      rw [MonoidHom.comp_apply, conjMap_comp, inv_mul_cancel]
      exact conjMap_one N hN x)
    (MonoidHom.ext fun x => by
      rw [MonoidHom.comp_apply, conjMap_comp, mul_inv_cancel]
      exact conjMap_one N hN x)
  map_one' := by
    ext x
    exact conjMap_one N hN x
  map_mul' g₁ g₂ := by
    ext x
    exact (conjMap_comp N hN g₁ g₂ x).symm

/-- A family of maps between the abelianizations of consecutive levels is **equivariant** when
it commutes with the conjugation actions of the group on the two levels
([Hyeon 2025, §3, p.12][Hyeon2025], the inverse system being one of `G`-modules). -/
def Equivariant (H : ℕ → Subgroup G) (hN : ∀ ν, (H ν).Normal)
    (V : ∀ ν, TopologicalAbelianization ↥(H ν) →* TopologicalAbelianization ↥(H (ν + 1))) :
    Prop :=
  ∀ (ν : ℕ) (g : G) (x : TopologicalAbelianization ↥(H ν)),
    V ν (conjAut (H ν) (hN ν) g x) = conjAut (H (ν + 1)) (hN (ν + 1)) g (V ν x)

theorem map_le (ℓ : ℕ) {H : ℕ → Subgroup G} (hN : ∀ ν, (H ν).Normal)
    {V : ∀ ν, TopologicalAbelianization ↥(H ν) →* TopologicalAbelianization ↥(H (ν + 1))}
    (hV : Equivariant H hN V) (g : G) :
    Subgroup.map (MulEquiv.piCongrRight fun ν => conjAut (H ν) (hN ν) g :
        (∀ ν, TopologicalAbelianization ↥(H ν)) ≃* ∀ ν, TopologicalAbelianization ↥(H ν))
      (groupTateModule ℓ H V) ≤ groupTateModule ℓ H V := by
  rintro - ⟨x, hx, rfl⟩
  intro ν
  refine ⟨?_, ?_⟩
  · change (conjAut (H ν) (hN ν) g (x ν)) ^ ℓ ^ ν = 1
    rw [← map_pow, (hx ν).1, map_one]
  · change V ν (conjAut (H ν) (hN ν) g (x ν))
      = (conjAut (H (ν + 1)) (hN (ν + 1)) g (x (ν + 1))) ^ ℓ
    rw [hV ν g (x ν), (hx ν).2, map_pow]

/-- An equivariant family of maps makes the Tate module stable under the levelwise conjugation
action—the `G`-module structure of the limit: torsion is preserved because the action is by
automorphisms, and the compatibility is preserved because the family commutes with the action
([Hyeon 2025, §3, p.12][Hyeon2025], the passage of the `G`-modules to the limit). -/
theorem map_eq (ℓ : ℕ) {H : ℕ → Subgroup G} (hN : ∀ ν, (H ν).Normal)
    {V : ∀ ν, TopologicalAbelianization ↥(H ν) →* TopologicalAbelianization ↥(H (ν + 1))}
    (hV : Equivariant H hN V) (g : G) :
    Subgroup.map (MulEquiv.piCongrRight fun ν => conjAut (H ν) (hN ν) g :
        (∀ ν, TopologicalAbelianization ↥(H ν)) ≃* ∀ ν, TopologicalAbelianization ↥(H ν))
      (groupTateModule ℓ H V) = groupTateModule ℓ H V := by
  refine le_antisymm (map_le ℓ hN hV g) ?_
  intro x hx
  refine ⟨(MulEquiv.piCongrRight fun ν => conjAut (H ν) (hN ν) g⁻¹) x, ?_, ?_⟩
  · exact map_le ℓ hN hV g⁻¹ ⟨x, hx, rfl⟩
  · funext ν
    change conjAut (H ν) (hN ν) g (conjAut (H ν) (hN ν) g⁻¹ (x ν)) = x ν
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

end GroupTateModule

/-- Over a Tate-module system the transfers are equivariant for the conjugation actions: the
inverse system of the source is one of `G`-modules. Claim recorded ahead of its proof
([Hyeon 2025, §3, p.12][Hyeon2025]). -/
theorem IsTateSystem.equivariant {ℓ : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {H : ℕ → Subgroup G}
    {V : ∀ ν, TopologicalAbelianization ↥(H ν) →* TopologicalAbelianization ↥(H (ν + 1))}
    (hS : IsTateSystem ℓ G H V) : GroupTateModule.Equivariant H hS.normal V := by
  sorry

/-- Over the maximal `2`-step solvable quotient of the absolute Galois group of a
mixed-characteristic local field, the group-theoretic Tate module of a system at a prime `ℓ` is
topologically isomorphic to the additive group of the `ℓ`-adic integers—the carrier of the
source's `ℤ_ℓ(1) ≅ T_ℓ(G_K²)`, whose action is the identification recorded with
`Atlas.Knowledge.groupCyclotomicCharacter`. Claim recorded ahead of its proof
([Hyeon 2025, Prop. 3.2 (1), p.12][Hyeon2025]). -/
theorem groupTateModule_equiv_padicInt (ℓ : ℕ) [Fact ℓ.Prime] (K : Type*) [Field K]
    [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
    (H : ℕ → Subgroup (mStepSolvableQuotient (Field.absoluteGaloisGroup K) 2))
    (V : ∀ ν, TopologicalAbelianization ↥(H ν) →* TopologicalAbelianization ↥(H (ν + 1)))
    (hS : IsTateSystem ℓ (mStepSolvableQuotient (Field.absoluteGaloisGroup K) 2) H V) :
    Nonempty (↥(groupTateModule ℓ H V) ≃ₜ* Multiplicative ℤ_[ℓ]) := by
  sorry

end Atlas.Knowledge
