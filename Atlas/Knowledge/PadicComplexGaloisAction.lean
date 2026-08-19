import Mathlib

/-!
# Galois action on the p-adic complex numbers

The absolute Galois group of `ℚ_[p]` acts on Mathlib's field `ℂ_[p]` of `p`-adic complex
numbers: each automorphism of the algebraic closure is an isometry for the spectral norm, so it
extends uniquely to the completion, and the extensions assemble into a homomorphism into the
`ℚ_[p]`-algebra automorphisms. This is the `G_K`-module structure the source puts on
`ℂ_{p_K}`—stated over the base `ℚ_[p]`, whose closure is the closure of every
mixed-characteristic local field of residue characteristic `p`—and it is the layer's entry
into `p`-adic Hodge theory: the fixed points of a closed subgroup are
`Atlas.Knowledge.axSenTate`, and the twisted tensor invariants built on it are
`Atlas.Knowledge.hodgeTateNumber`.

## Main definitions

* `padicComplexGaloisAction` — the homomorphism from the absolute Galois group of `ℚ_[p]` to
  the `ℚ_[p]`-algebra automorphisms of `ℂ_[p]`.
* `PadicComplexGaloisAction.toAlgEquiv`, `PadicComplexGaloisAction.toGalSubgroup` — the
  definitional unwrappings of a Galois element, and of a subgroup, to the automorphism group
  of `PadicAlgCl p`; the second is how `Atlas.Knowledge.axSenTate` and
  `Atlas.Knowledge.hodgeTateNumber` reach `IntermediateField.fixedField`.

## Main statements

* `padicComplexGaloisAction_continuous` — the two-variable action map is continuous.
* `PadicComplexGaloisAction.isometry_algEquiv` — each extended automorphism is an isometry of
  `ℂ_[p]`; `PadicComplexGaloisAction.setOf_apply_eq_mem_nhds` — the orbit map of an algebraic
  point is locally constant. These are the two halves of the continuity proof, kept public
  because `Atlas.Knowledge.axSenTate` and `Atlas.Knowledge.hodgeTateNumber` want them too.

## Implementation notes

Mathlib's `ℂ_[p]` is the uniform completion of `PadicAlgCl p`, an abbreviation for
`AlgebraicClosure ℚ_[p]`—so the absolute Galois group of `ℚ_[p]` literally acts on the field
being completed, and no transport between closures enters. Each automorphism is an isometry
because the spectral norm is invariant under `ℚ_[p]`-algebra automorphisms and the norm of
`PadicAlgCl p` is the spectral norm definitionally; `UniformSpace.Completion.mapRingHom` then
extends it to `ℂ_[p]`, and the inverse automorphism extends to the inverse, which is what the
supporting `PadicComplexGaloisAction.algEquiv` assembles. The extension is the identity on the
image of `PadicAlgCl p`, elementwise the content of `padicComplexGaloisAction_coe`, and the
whole construction is forced by density: any continuous extension agrees with this one. What is
not free is the continuity of the action jointly in the automorphism and the point, for the
Krull topology on the group: on the dense subfield the orbit maps are locally constant, and the
extensions are equicontinuous because they are isometries.

Those two facts are exactly what the proof splits into, and neither needs the ultrametric
inequality—a plain three-term triangle estimate suffices, which is why the argument does not
touch `IsUltrametricDist`. Equicontinuity is `isometry_algEquiv`: the extension is
`UniformSpace.Completion.map` of an isometry, definitionally, so `Isometry.completion_map`
applies. Local constancy is `setOf_apply_eq_mem_nhds`: for an algebraic `y` the field
`ℚ_[p]⟮y⟯` is finite over `ℚ_[p]`, so `IntermediateField.fixingSubgroup_isOpen` makes its
fixing subgroup open, and the coset of `σ₀` is a neighbourhood on which `σ y` does not move.
Splitting `dist (σ x) (σ₀ x₀)` across an algebraic approximation `y` of `x₀` then costs three
thirds of `ε`, one for moving the point, two for the approximation, and none for moving the
automorphism.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
* [BrinonConrad2009] O. Brinon, B. Conrad, *CMI Summer School notes on p-adic Hodge theory
  (preliminary version)*, available at math.stanford.edu/~conrad/papers/notes.pdf, 2009.
-/

namespace Atlas.Knowledge

namespace PadicComplexGaloisAction

variable {p : ℕ} [Fact p.Prime]

/-- An element of the absolute Galois group of `ℚ_[p]`, as the automorphism of `PadicAlgCl p`
it is: `Field.absoluteGaloisGroup` is a bare `def` of the automorphism group, so the
definitional identity holds, but instance resolution does not unfold it—this wrapper is where
the function coercion becomes available. -/
def toAlgEquiv (σ : Field.absoluteGaloisGroup ℚ_[p]) : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p := σ

/-- A subgroup of the absolute Galois group of `ℚ_[p]`, as a subgroup of the automorphism
group of `PadicAlgCl p` it is: the subgroup-level companion of `toAlgEquiv`, so that the
Galois-correspondence machinery on `IntermediateField.fixedField` elaborates with the
automorphism group's own instances throughout. -/
def toGalSubgroup (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p])) :
    Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) := H

/-- Every element of the absolute Galois group of `ℚ_[p]` is an isometry of the algebraic
closure: the norm of `PadicAlgCl p` is the spectral norm, which is invariant under
`ℚ_[p]`-algebra automorphisms. -/
theorem isometry (σ : Field.absoluteGaloisGroup ℚ_[p]) : Isometry (toAlgEquiv σ) :=
  Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, ← PadicAlgCl.spectralNorm_eq,
      ← spectralNorm_eq_of_equiv, PadicAlgCl.spectralNorm_eq]

/-- The ring endomorphism of `ℂ_[p]` extending an automorphism of the algebraic closure by
uniform continuity. -/
noncomputable def ringHom (σ : Field.absoluteGaloisGroup ℚ_[p]) : ℂ_[p] →+* ℂ_[p] :=
  UniformSpace.Completion.mapRingHom ((toAlgEquiv σ).toAlgHom : PadicAlgCl p →+* PadicAlgCl p)
    (isometry σ).continuous

/-- The extension agrees with the automorphism on the image of the algebraic closure. -/
theorem ringHom_coe (σ : Field.absoluteGaloisGroup ℚ_[p]) (x : PadicAlgCl p) :
    ringHom σ (x : ℂ_[p]) = (toAlgEquiv σ x : ℂ_[p]) :=
  UniformSpace.Completion.map_coe (isometry σ).uniformContinuous x

/-- Extension is compatible with composition: the extensions form a monoid action. -/
theorem ringHom_comp (σ τ : Field.absoluteGaloisGroup ℚ_[p]) :
    (ringHom σ).comp (ringHom τ) = ringHom (σ * τ) :=
  RingHom.ext fun x =>
    congrFun
      (UniformSpace.Completion.map_comp (isometry σ).uniformContinuous
        (isometry τ).uniformContinuous)
      x

/-- The identity extends to the identity. -/
theorem ringHom_one : ringHom (1 : Field.absoluteGaloisGroup ℚ_[p]) = RingHom.id ℂ_[p] :=
  RingHom.ext fun x => congrFun UniformSpace.Completion.map_id x

/-- The `ℚ_[p]`-algebra automorphism of `ℂ_[p]` extending an automorphism of the algebraic
closure: the extension of the inverse is the inverse of the extension, and the extension fixes
`ℚ_[p]` because the automorphism does. -/
noncomputable def algEquiv (σ : Field.absoluteGaloisGroup ℚ_[p]) : ℂ_[p] ≃ₐ[ℚ_[p]] ℂ_[p] :=
  AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofRingHom (ringHom σ) (ringHom σ⁻¹)
      (by rw [ringHom_comp, mul_inv_cancel, ringHom_one])
      (by rw [ringHom_comp, inv_mul_cancel, ringHom_one]))
    (fun x => by
      have h : algebraMap ℚ_[p] ℂ_[p] x
          = ((algebraMap ℚ_[p] (PadicAlgCl p) x : PadicAlgCl p) : ℂ_[p]) := rfl
      rw [h]
      exact (ringHom_coe σ _).trans (congrArg _ ((toAlgEquiv σ).commutes x)))

/-- The extension of an automorphism to `ℂ_[p]` is again an isometry: the completion of an
isometry is one, and the extension is that completion. -/
theorem isometry_algEquiv (σ : Field.absoluteGaloisGroup ℚ_[p]) : Isometry (algEquiv σ) := by
  have h : ⇑(algEquiv σ) = UniformSpace.Completion.map (toAlgEquiv σ) := rfl
  rw [h]
  exact (isometry σ).completion_map

/-- The orbit map of an algebraic point is locally constant: the automorphisms agreeing with
`σ₀` at `y` form a neighbourhood of `σ₀`, because `ℚ_[p]⟮y⟯` is finite over `ℚ_[p]` and so its
fixing subgroup is open in the Krull topology. -/
theorem setOf_apply_eq_mem_nhds (σ₀ : Field.absoluteGaloisGroup ℚ_[p]) (y : PadicAlgCl p) :
    {σ : Field.absoluteGaloisGroup ℚ_[p] | toAlgEquiv σ y = toAlgEquiv σ₀ y} ∈ nhds σ₀ := by
  set E : IntermediateField ℚ_[p] (PadicAlgCl p) := IntermediateField.adjoin ℚ_[p] {y} with hE
  haveI : FiniteDimensional ℚ_[p] E :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral y)
  have hyE : y ∈ E := IntermediateField.mem_adjoin_simple_self ℚ_[p] y
  refine Filter.mem_of_superset (IsOpen.mem_nhds (?_ : IsOpen
    {σ : Field.absoluteGaloisGroup ℚ_[p] | σ₀⁻¹ * σ ∈ E.fixingSubgroup}) ?_) ?_
  · exact E.fixingSubgroup_isOpen.preimage (continuous_const.mul continuous_id)
  · change σ₀⁻¹ * σ₀ ∈ E.fixingSubgroup
    rw [inv_mul_cancel]
    exact E.fixingSubgroup.one_mem
  · intro σ hσ
    have h : (toAlgEquiv σ₀).symm (toAlgEquiv σ y) = y :=
      (IntermediateField.mem_fixingSubgroup_iff E _).mp hσ y hyE
    calc toAlgEquiv σ y
        = toAlgEquiv σ₀ ((toAlgEquiv σ₀).symm (toAlgEquiv σ y)) :=
          (AlgEquiv.apply_symm_apply _ _).symm
      _ = toAlgEquiv σ₀ y := congrArg _ h

end PadicComplexGaloisAction

open PadicComplexGaloisAction in
/-- The **Galois action on the `p`-adic complex numbers**: the homomorphism from the absolute
Galois group of `ℚ_[p]` to the `ℚ_[p]`-algebra automorphisms of `ℂ_[p]`, extending each
automorphism of the algebraic closure to its completion by uniform continuity
([Hyeon 2025, §4, p.15][Hyeon2025], the `G_K`-module `ℂ_{p_K}`;
[Brinon–Conrad 2009, §2.1, p.12][BrinonConrad2009], the unique isometric extension). -/
noncomputable def padicComplexGaloisAction (p : ℕ) [Fact p.Prime] :
    Field.absoluteGaloisGroup ℚ_[p] →* ℂ_[p] ≃ₐ[ℚ_[p]] ℂ_[p] where
  toFun := algEquiv
  map_one' := AlgEquiv.ext fun x => RingHom.congr_fun ringHom_one x
  map_mul' σ τ := AlgEquiv.ext fun x => (RingHom.congr_fun (ringHom_comp σ τ) x).symm

/-- The action extends the natural one on the algebraic closure: on the image of
`PadicAlgCl p` in `ℂ_[p]`, the extended automorphism is the original one. -/
@[simp]
theorem padicComplexGaloisAction_coe {p : ℕ} [Fact p.Prime]
    (σ : Field.absoluteGaloisGroup ℚ_[p]) (x : PadicAlgCl p) :
    padicComplexGaloisAction p σ (x : ℂ_[p])
      = (PadicComplexGaloisAction.toAlgEquiv σ x : ℂ_[p]) :=
  PadicComplexGaloisAction.ringHom_coe σ x

open PadicComplexGaloisAction in
/-- The action of the absolute Galois group of `ℚ_[p]` on `ℂ_[p]` is continuous jointly in the
automorphism and the point ([Hyeon 2025, §4, p.15][Hyeon2025], the `G_K`-module `ℂ_{p_K}`;
[Brinon–Conrad 2009, §2.1 and Def. 2.2.1, p.12][BrinonConrad2009]). -/
theorem padicComplexGaloisAction_continuous (p : ℕ) [Fact p.Prime] :
    Continuous fun q : Field.absoluteGaloisGroup ℚ_[p] × ℂ_[p] =>
      padicComplexGaloisAction p q.1 q.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨σ₀, x₀⟩
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  -- Approximate the point by an algebraic one, within a third of the target.
  obtain ⟨y, hy⟩ : ∃ y : PadicAlgCl p, dist x₀ (y : ℂ_[p]) < ε / 3 := by
    obtain ⟨-, ⟨y, rfl⟩, hy⟩ :=
      Metric.mem_closure_iff.mp
        (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p) x₀) (ε / 3) (by positivity)
    exact ⟨y, hy⟩
  rw [nhds_prod_eq]
  filter_upwards [Filter.prod_mem_prod (setOf_apply_eq_mem_nhds σ₀ y)
    (Metric.ball_mem_nhds x₀ (by positivity : (0 : ℝ) < ε / 3))] with q hq
  obtain ⟨hq1, hq2⟩ := hq
  have e1 : dist (padicComplexGaloisAction p q.1 q.2) (padicComplexGaloisAction p q.1 x₀)
      = dist q.2 x₀ := (isometry_algEquiv q.1).dist_eq _ _
  have e2 : dist (padicComplexGaloisAction p q.1 x₀)
      (padicComplexGaloisAction p q.1 (y : ℂ_[p])) = dist x₀ (y : ℂ_[p]) :=
    (isometry_algEquiv q.1).dist_eq _ _
  have e3 : padicComplexGaloisAction p q.1 (y : ℂ_[p])
      = padicComplexGaloisAction p σ₀ (y : ℂ_[p]) := by
    rw [padicComplexGaloisAction_coe, padicComplexGaloisAction_coe, hq1]
  have e4 : dist (padicComplexGaloisAction p σ₀ (y : ℂ_[p]))
      (padicComplexGaloisAction p σ₀ x₀) = dist (y : ℂ_[p]) x₀ :=
    (isometry_algEquiv σ₀).dist_eq _ _
  calc dist (padicComplexGaloisAction p q.1 q.2) (padicComplexGaloisAction p σ₀ x₀)
      ≤ dist (padicComplexGaloisAction p q.1 q.2) (padicComplexGaloisAction p q.1 x₀)
        + dist (padicComplexGaloisAction p q.1 x₀) (padicComplexGaloisAction p σ₀ x₀) :=
        dist_triangle _ _ _
    _ ≤ dist (padicComplexGaloisAction p q.1 q.2) (padicComplexGaloisAction p q.1 x₀)
        + (dist (padicComplexGaloisAction p q.1 x₀) (padicComplexGaloisAction p q.1 (y : ℂ_[p]))
          + dist (padicComplexGaloisAction p σ₀ (y : ℂ_[p]))
            (padicComplexGaloisAction p σ₀ x₀)) := by
        gcongr
        exact e3 ▸ dist_triangle _ _ _
    _ = dist q.2 x₀ + (dist x₀ (y : ℂ_[p]) + dist (y : ℂ_[p]) x₀) := by rw [e1, e2, e4]
    _ < ε / 3 + (ε / 3 + ε / 3) := by
        gcongr
        · exact Metric.mem_ball.mp hq2
        · rwa [dist_comm]
    _ = ε := by ring

end Atlas.Knowledge
