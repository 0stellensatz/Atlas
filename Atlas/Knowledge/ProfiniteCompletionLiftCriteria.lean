import Mathlib

/-!
# profinite completion lift criteria

Mathlib's profinite completion of a group `G`,
`ProfiniteGrp.ProfiniteCompletion.completion G`, with the universal
lift of a homomorphism `f` into a profinite group `P`: the lift's
coordinate at an open normal subgroup of `P` is the induced map on the
coordinate at the preimage; the lift is surjective when `f` has dense
range, injective when the preimages of the open normal subgroups of `P`
are cofinal among the finite-index normal subgroups of `G`, and a
bijective lift packages as a continuous multiplicative equivalence. The
completion half of the second reciprocity claim,
`Atlas.Knowledge.IsLocalReciprocity.unitsCompletion_continuousMulEquiv`,
stated on Mathlib's completion rather than the source's own (#104).

## Main definitions

* `ProfiniteCompletion.liftContinuousMulEquiv` — a bijective lift as a
  continuous multiplicative equivalence, with its `rfl` evaluation
  rule.

## Main statements

* `ProfiniteCompletion.proj_lift_apply` — the lift's coordinate at an
  open normal subgroup is the induced map on the coordinate at its
  preimage; proved.
* `ProfiniteCompletion.lift_surjective_of_denseRange` — a dense-range
  homomorphism lifts onto; proved.
* `ProfiniteCompletion.lift_injective_of_cofinal` — when the preimages
  of open normal subgroups are cofinal, the lift is injective; proved.

## Implementation notes

The source builds its own completion against the *open* finite-index
normal subgroups
(`LocalClassFieldTheory/Infinite/ProfiniteCompletion.lean:144`,
`TopologicalProfiniteCompletion`) and proves the two criteria for it;
the layer states them on Mathlib's `ProfiniteGrp.ProfiniteCompletion`,
whose index category is every finite-index normal subgroup — the
identification of the two in mixed characteristic is what
`Atlas.Knowledge.unitsFiniteIndexOpen` supplies at the application. The
cofinality hypothesis is the source's `≤` form (its
`ProfiniteCompletionCriteria.lean:60`): a kernel element's coordinate
at a preimage vanishes, and the limit's own compatibility carries that
vanishing along the inclusion to every index above — the local
application supplies the stronger equational form and specializes. The
coordinate formula is proved by the dense-equalizer device of Mathlib's
own `lift_unique`: the lift's defining cone is an anonymous term inside
`lift`, and its unfolding is not type-correct under instance
transparency, so the limit's factorization cannot be rewritten with.
The finite-quotient map's triviality of kernel is stated elementwise,
`y = 1` from its image being `1`, because the map's coercion runs
through the induced category of finite groups and defeats `map_one`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

namespace ProfiniteCompletion

open CategoryTheory ProfiniteGrp ProfiniteGrp.ProfiniteCompletion

noncomputable section

universe u

variable {G : GrpCat.{u}} {P : ProfiniteGrp.{u}}

/-- The coordinate of the lift at an open normal subgroup of the target
is the induced map on the coordinate of the completion point at the
subgroup's preimage. -/
theorem proj_lift_apply (f : G ⟶ GrpCat.of P) (N : OpenNormalSubgroup P) (x : completion G) :
    (ProfiniteGrp.proj N).hom ((lift f).hom x) = (quotientMap f N).hom (x.1 (preimage f N)) := by
  have hc1 : Continuous fun y : completion G => (ProfiniteGrp.proj N).hom ((lift f).hom y) :=
    (ProfiniteGrp.proj N).hom.continuous.comp (lift f).hom.continuous
  have hc2 : Continuous fun y : completion G =>
      (ofFiniteGrpHom (quotientMap f N)).hom
        (((limitCone (diagram G)).π.app (preimage f N)).hom y) :=
    (ofFiniteGrpHom (quotientMap f N)).hom.continuous.comp
      ((limitCone (diagram G)).π.app (preimage f N)).hom.continuous
  have h := (denseRange (G := G)).equalizer hc1 hc2 (by
    funext g
    have he : (lift f).hom (etaFn G g) = f.hom g := ConcreteCategory.congr_hom (lift_eta f) g
    change (ProfiniteGrp.proj N).hom ((lift f).hom (etaFn G g)) = _
    rw [he]
    rfl)
  exact congrFun h x

/-- The induced map on finite quotients has trivial kernel: the
preimage is the full kernel (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/ProfiniteCompletionCriteria.lean:25`). -/
theorem quotientMap_eq_one (f : G ⟶ GrpCat.of P) (N : OpenNormalSubgroup P)
    (y : G ⧸ (preimage f N).toSubgroup) (hy : (quotientMap f N).hom y = 1) : y = 1 := by
  induction y using QuotientGroup.induction_on with
  | H g =>
    change (QuotientGroup.mk (f.hom g) : P ⧸ N.toSubgroup) = 1 at hy
    rw [QuotientGroup.eq_one_iff] at hy
    exact (QuotientGroup.eq_one_iff g).2 hy

/-- **Cofinality of the preimages makes the lift injective**: when
every finite-index normal subgroup of the group contains the preimage
of an open normal subgroup of the target (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/ProfiniteCompletionCriteria.lean:60`). -/
theorem lift_injective_of_cofinal (f : G ⟶ GrpCat.of P)
    (hcof : ∀ H : FiniteIndexNormalSubgroup G, ∃ N : OpenNormalSubgroup P, preimage f N ≤ H) :
    Function.Injective (lift f).hom := by
  rw [injective_iff_map_eq_one]
  intro x hx
  apply Subtype.ext
  funext H
  obtain ⟨N, hN⟩ := hcof H
  have h1 : x.1 (preimage f N) = 1 := by
    apply quotientMap_eq_one f N
    have h : (ProfiniteGrp.proj N).hom ((lift f).hom x) = 1 := by
      rw [hx, map_one]
    rw [← proj_lift_apply f N x]
    exact h
  rw [← x.2 hN.hom, h1]
  exact map_one ((diagram G).map hN.hom).hom

/-- **A dense-range homomorphism lifts onto the target**: the lift's
range is closed, the completion being compact and the target Hausdorff,
and contains the dense range (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/ProfiniteCompletionCriteria.lean:43`). -/
theorem lift_surjective_of_denseRange (f : G ⟶ GrpCat.of P)
    (hdense : DenseRange f.hom) : Function.Surjective (lift f).hom := by
  have hclosed : IsClosed (Set.range (lift f).hom) :=
    (isCompact_range (lift f).hom.continuous).isClosed
  have hsub : Set.range f.hom ⊆ Set.range (lift f).hom := by
    rintro _ ⟨g, rfl⟩
    refine ⟨etaFn G g, ?_⟩
    exact ConcreteCategory.congr_hom (lift_eta f) g
  have hdense' : Dense (Set.range (lift f).hom) := hdense.mono hsub
  rw [← Set.range_eq_univ, ← hclosed.closure_eq]
  exact hdense'.closure_eq

/-- A bijective lift as a continuous multiplicative equivalence: the
inverse is continuous because the completion is compact and the target
Hausdorff (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/ProfiniteLocalReciprocity.lean:115`). -/
def liftContinuousMulEquiv (f : G ⟶ GrpCat.of P) (hinj : Function.Injective (lift f).hom)
    (hsurj : Function.Surjective (lift f).hom) : completion G ≃ₜ* P :=
  { Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective (lift f).hom ⟨hinj, hsurj⟩)
      (lift f).hom.continuous with
    map_mul' := (lift f).hom.map_mul }

/-- The equivalence is the lift on points. -/
@[simp]
theorem liftContinuousMulEquiv_apply (f : G ⟶ GrpCat.of P)
    (hinj : Function.Injective (lift f).hom) (hsurj : Function.Surjective (lift f).hom)
    (x : completion G) : liftContinuousMulEquiv f hinj hsurj x = (lift f).hom x :=
  rfl

end

end ProfiniteCompletion

end Atlas.Knowledge
