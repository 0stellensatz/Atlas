import Mathlib
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusFixedField
import Atlas.Knowledge.FrobeniusSemigroup
import Atlas.Knowledge.NormalizedDegree

/-!
# Frobenius descent

Descent from the Frobenius semigroup: the image of `G_L` in the inertia
quotient is closed, a finite field fixed by the inertia and one lift
representative bounds the Frobenius fixed field, and restriction
together with normalized degree distinguishes Frobenius elements — the
group-theoretic facts consumed when two Frobenius lifts share their
restriction and degree (#104).

## Main definitions

* `DegreeData.extensionImageInInertiaQuotient` — the image of `G_L` in
  `G_K / I_L`.

## Main statements

* `DegreeData.frobeniusFixedField_le_of_inertia_le_of_lift_mem` — the
  closed-subgroup minimality bound; proved.
* `DegreeData.frobeniusFixedField_le_of_restriction_eq_one` — trivial
  restriction puts `L` under the fixed field; proved.
* `DegreeData.extensionRestriction_normalizedDegree_joint_injective` —
  joint injectivity; proved.
* `DegreeData.frobenius_eq_of_restriction_eq_of_degree_eq` — its
  Frobenius-element form; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
which frees the containment the minimality bound's statement bound for
its `extensionSubgroup` alone, and the ambient compactness and
Hausdorff binders the openness argument never touches — all go; the
source's `Type*` ambient group is kept (the file is
representation-free).

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData


/-- The image of `G_L` in `G_K / I_L` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean:23`]
[Yamaguchi2026]). -/
def extensionImageInInertiaQuotient (D : DegreeData G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    Subgroup (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) :=
  (L.toSubgroup.subgroupOf K.toSubgroup).map
    (QuotientGroup.mk' (D.extensionInertiaWithin K L hLK))

/-- The image of `G_L` in `G_K / I_L` is closed — the finite-index
subgroup is clopen, and quotient maps are open ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean:33`]
[Yamaguchi2026]). -/
theorem extensionImageInInertiaQuotient_isClosed
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    IsClosed (D.extensionImageInInertiaQuotient K.field L hLK : Set
      (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)) := by
  letI : IsClosed
      (D.extensionInertiaWithin K.field L hLK : Set K.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed K L hLK
  let E := L.toSubgroup.subgroupOf K.field.toSubgroup
  have hEclosed : IsClosed (E : Set K.field.toSubgroup) := by
    have hcarrier : (E : Set K.field.toSubgroup) =
        ((fun x : K.field.toSubgroup => (x : G)) ⁻¹' (L : Set G)) := by
      rfl
    rw [hcarrier]
    exact L.isClosed'.preimage continuous_subtype_val
  letI : E.FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient K.field.toSubgroup _ E hLfinite
  have hEopen : IsOpen (E : Set K.field.toSubgroup) :=
    E.isOpen_of_isClosed_of_finiteIndex hEclosed
  change IsClosed
    ((QuotientGroup.mk' (D.extensionInertiaWithin K.field L hLK)) ''
      (E : Set K.field.toSubgroup))
  exact (D.extensionImageInInertiaQuotient K.field L hLK).isClosed_of_isOpen
    (QuotientGroup.isOpenMap_coe
      (N := D.extensionInertiaWithin K.field L hLK)
      (E : Set K.field.toSubgroup) hEopen)

/-- **A finite field fixed by the relative inertia and one representative
of a Frobenius lift contains the lift's Frobenius fixed field** — the
closed-subgroup minimality argument ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean:67`]
[Yamaguchi2026]). -/
theorem frobeniusFixedField_le_of_inertia_le_of_lift_mem
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L M : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hMfinite : Finite
      (K.field.toSubgroup ⧸ M.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK)
    (hI : D.extensionInertiaWithin K.field L hLK ≤
      M.toSubgroup.subgroupOf K.field.toSubgroup)
    (s : K.field.toSubgroup)
    (hsM : s ∈ M.toSubgroup.subgroupOf K.field.toSubgroup)
    (hsσ : (QuotientGroup.mk s :
      K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) = σ.1) :
    (D.frobeniusFixedField K L hLK σ).toSubgroup ≤
      M.toSubgroup := by
  let H := D.extensionInertiaWithin K.field L hLK
  let E := M.toSubgroup.subgroupOf K.field.toSubgroup
  let Q := K.field.toSubgroup ⧸ H
  let J : Subgroup Q := E.map (QuotientGroup.mk' H)
  letI : IsClosed (H : Set K.field.toSubgroup) :=
    D.extensionInertiaWithin_isClosed K L hLK
  have hEclosed : IsClosed (E : Set K.field.toSubgroup) := by
    have hcarrier : (E : Set K.field.toSubgroup) =
        ((fun x : K.field.toSubgroup => (x : G)) ⁻¹' (M : Set G)) := by
      rfl
    rw [hcarrier]
    exact M.isClosed'.preimage continuous_subtype_val
  letI : E.FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient K.field.toSubgroup _ E hMfinite
  have hEopen : IsOpen (E : Set K.field.toSubgroup) :=
    E.isOpen_of_isClosed_of_finiteIndex hEclosed
  have hJclosed : IsClosed (J : Set Q) := by
    change IsClosed ((QuotientGroup.mk' H) '' (E : Set K.field.toSubgroup))
    exact J.isClosed_of_isOpen
      (QuotientGroup.isOpenMap_coe (N := H)
        (E : Set K.field.toSubgroup) hEopen)
  have hσJ : σ.1 ∈ J := ⟨s, hsM, hsσ⟩
  have hClosureJ :
      (D.frobeniusClosure K L hLK σ).toSubgroup ≤ J := by
    change (Subgroup.closure
      (Set.range (fun _ : Unit => σ.1))).topologicalClosure ≤ J
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      rintro q ⟨u, rfl⟩
      exact hσJ
    · exact hJclosed
  rintro g ⟨k, hkClosure, rfl⟩
  have hkJ : (QuotientGroup.mk k : Q) ∈ J := hClosureJ hkClosure
  rcases hkJ with ⟨e, heE, heq⟩
  have hdiff : e⁻¹ * k ∈ H := QuotientGroup.eq.mp heq
  have hdiffE : e⁻¹ * k ∈ E := hI hdiff
  have hkE : k ∈ E := by
    have hmul := E.mul_mem heE hdiffE
    simpa [mul_assoc] using hmul
  change (k : G) ∈ M
  exact hkE

/-- **A Frobenius lift restricting trivially to `L` has its fixed field
containing `L`** — equivalently `G_Σ ≤ G_L` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean:128`]
[Yamaguchi2026]). -/
theorem frobeniusFixedField_le_of_restriction_eq_one
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (σ : D.FrobeniusElements K L hLK)
    (hσ : D.frobeniusRestriction K L hLK σ = 1) :
    (D.frobeniusFixedField K L hLK σ).toSubgroup ≤
      L.toSubgroup := by
  let H := D.extensionInertiaWithin K.field L hLK
  let E := L.toSubgroup.subgroupOf K.field.toSubgroup
  let Q := K.field.toSubgroup ⧸ H
  let J : Subgroup Q := D.extensionImageInInertiaQuotient K.field L hLK
  have hσJ : σ.1 ∈ J := by
    let k : K.field.toSubgroup := Quotient.out σ.1
    have hkq : QuotientGroup.mk k = σ.1 := Quotient.out_eq' σ.1
    have hkE : k ∈ E := by
      have hq : (QuotientGroup.mk k :
          K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) = 1 := by
        change D.extensionRestriction K.field L hLK
          (QuotientGroup.mk k : K.field.toSubgroup ⧸ H) = 1
        rw [hkq]
        exact hσ
      simpa using QuotientGroup.eq.mp hq.symm
    exact ⟨k, hkE, hkq⟩
  have hClosureJ :
      (D.frobeniusClosure K L hLK σ).toSubgroup ≤ J := by
    change (Subgroup.closure (Set.range (fun _ : Unit => σ.1))).topologicalClosure ≤ J
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      rintro q ⟨u, rfl⟩
      exact hσJ
    · exact D.extensionImageInInertiaQuotient_isClosed K L hLK
  rintro g ⟨k, hkClosure, rfl⟩
  have hkJ : (QuotientGroup.mk k : Q) ∈ J := hClosureJ hkClosure
  rcases hkJ with ⟨e, heE, heq⟩
  have hdiff : e⁻¹ * k ∈ H := QuotientGroup.eq.mp heq
  have hdiffE : e⁻¹ * k ∈ E := hdiff.1
  have hkE : k ∈ E := by
    have := E.mul_mem heE hdiffE
    simpa [mul_assoc] using this
  change (k : G) ∈ L
  exact hkE

/-- **Restriction and normalized degree jointly distinguish elements of
`G(L̃/K)`** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean:176`]
[Yamaguchi2026]). -/
theorem extensionRestriction_normalizedDegree_joint_injective
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    Function.Injective (fun q :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK =>
      (D.extensionRestriction K.field L hLK q,
        D.extensionNormalizedDegree K L hLK q)) := by
  intro q r hqr
  refine Quotient.inductionOn₂' q r ?_ hqr
  intro a b hab
  apply QuotientGroup.eq.mpr
  have hRestriction : QuotientGroup.mk a =
      (QuotientGroup.mk b :
        K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) := by
    exact congrArg Prod.fst hab
  have hExtension : a⁻¹ * b ∈ L.toSubgroup.subgroupOf K.field.toSubgroup :=
    QuotientGroup.eq.mp hRestriction
  have hDegree : D.normalizedDegree K a =
      D.normalizedDegree K b :=
    congrArg Prod.snd hab
  refine ⟨hExtension, ?_⟩
  rw [← D.normalizedDegree_ker K]
  change D.normalizedDegree K (a⁻¹ * b) = 1
  rw [map_mul, map_inv, hDegree, inv_mul_cancel]

/-- The Frobenius restriction is multiplicative ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean:208`]
[Yamaguchi2026]). -/
@[simp]
theorem frobeniusRestriction_mul (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ τ : D.FrobeniusElements K L hLK) :
    D.frobeniusRestriction K L hLK (σ * τ) =
      D.frobeniusRestriction K L hLK σ *
        D.frobeniusRestriction K L hLK τ := by
  change D.extensionRestriction K.field L hLK (σ.1 * τ.1) =
    D.extensionRestriction K.field L hLK σ.1 *
      D.extensionRestriction K.field L hLK τ.1
  exact map_mul _ _ _

/-- **Frobenius elements with equal restriction and equal normalized
degree are equal** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusDescent.lean:223`]
[Yamaguchi2026]). -/
theorem frobenius_eq_of_restriction_eq_of_degree_eq
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    {σ τ : D.FrobeniusElements K L hLK}
    (hRestriction :
      D.frobeniusRestriction K L hLK σ =
        D.frobeniusRestriction K L hLK τ)
    (hDegree :
      D.extensionNormalizedDegree K L hLK σ.1 =
        D.extensionNormalizedDegree K L hLK τ.1) :
    σ = τ := by
  apply Subtype.ext
  apply D.extensionRestriction_normalizedDegree_joint_injective
    K L hLK
  exact Prod.ext hRestriction hDegree
end DegreeData

end

end Atlas.Knowledge
