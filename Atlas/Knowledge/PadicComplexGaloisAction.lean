import Mathlib

/-!
# Galois action on the p-adic complex numbers

The absolute Galois group of `ℚ_[p]` acts on Mathlib's field `ℂ_[p]` of `p`-adic complex
numbers: each automorphism of the algebraic closure is an isometry for the spectral norm, so it
extends uniquely to the completion, and the extensions assemble into a homomorphism into the
`ℚ_[p]`-algebra automorphisms. This is the `G_K`-module structure the source puts on
`ℂ_{p_K}`—stated over the base `ℚ_[p]`, whose closure is every mixed-characteristic local
field's closure—and it is the layer's entry into `p`-adic Hodge theory: the fixed points of a
closed subgroup are `Atlas.Knowledge.axSenTate`, and the twisted tensor invariants built on it
are `Atlas.Knowledge.hodgeTateNumber`.

## Main definitions

* `padicComplexGaloisAction` — the homomorphism from the absolute Galois group of `ℚ_[p]` to
  the `ℚ_[p]`-algebra automorphisms of `ℂ_[p]`.

## Main statements

* `padicComplexGaloisAction_continuous` — the two-variable action map is continuous. Claim
  recorded ahead of its proof.

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
not free is the continuity of the action jointly in the automorphism and the point—the recorded
claim—for the Krull topology on the group: on the dense subfield the orbit maps are locally
constant, and the extensions are equicontinuous because they are isometries.

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

theorem ringHom_coe (σ : Field.absoluteGaloisGroup ℚ_[p]) (x : PadicAlgCl p) :
    ringHom σ (x : ℂ_[p]) = (toAlgEquiv σ x : ℂ_[p]) :=
  UniformSpace.Completion.map_coe (isometry σ).uniformContinuous x

theorem ringHom_comp (σ τ : Field.absoluteGaloisGroup ℚ_[p]) :
    (ringHom σ).comp (ringHom τ) = ringHom (σ * τ) :=
  RingHom.ext fun x =>
    congrFun
      (UniformSpace.Completion.map_comp (isometry σ).uniformContinuous
        (isometry τ).uniformContinuous)
      x

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

/-- The action of the absolute Galois group of `ℚ_[p]` on `ℂ_[p]` is continuous jointly in the
automorphism and the point. Claim recorded ahead of its proof
([Hyeon 2025, §4, p.15][Hyeon2025], the `G_K`-module `ℂ_{p_K}`;
[Brinon–Conrad 2009, §2.1 and Def. 2.2.1, p.12][BrinonConrad2009]). -/
theorem padicComplexGaloisAction_continuous (p : ℕ) [Fact p.Prime] :
    Continuous fun q : Field.absoluteGaloisGroup ℚ_[p] × ℂ_[p] =>
      padicComplexGaloisAction p q.1 q.2 := by
  sorry

end Atlas.Knowledge
