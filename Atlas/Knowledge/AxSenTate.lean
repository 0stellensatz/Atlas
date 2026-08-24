import Mathlib
import Atlas.Knowledge.ConjugateDiameterBound
import Atlas.Knowledge.PadicComplexGaloisAction

/-!
# Ax–Sen–Tate theorem

The fixed points of a closed subgroup of the absolute Galois group of `ℚ_[p]` acting on
`ℂ_[p]` are the completion of the fixed field: `ℂ_p^H = 𝒞((ℚ_p^alg)^H)`, the closure in
`ℂ_[p]` of the image of `IntermediateField.fixedField H`. This is the theorem that computes
every fixed field of the source's Hodge–Tate machinery—it closes the source's Lemma 5.1, and
through it the invariants of `Atlas.Knowledge.hodgeTateNumber` are vector spaces over the
completed fixed field. There are no transcendental invariants: nothing is fixed beyond the
closure of what is already fixed algebraically.

## Main statements

* `axSenTate` — the fixed points of a closed subgroup are the closure of the image of its
  fixed field.
* `AxSenTate.fixedPoints_eq_image_of_isOpen` — for an open subgroup the closure collapses:
  the fixed points are exactly the image of the fixed field, which is finite over `ℚ_[p]`
  and hence closed. Its elementwise form `AxSenTate.exists_algebraMap_eq_of_isOpen` is what
  the finite-dimensional consumers read.

## Implementation notes

The proof composes three pieces. The soft inclusion is topology: the fixed-point set is an
intersection of equalizers of isometries, hence closed, and it contains the image of the fixed
field by the definition of the action on algebraic points. For the content direction, a fixed
point is approximated within `ε` by an algebraic `y`; almost-invariance transfers from the
point to `y` at the cost of doubling `ε`, and the Krull correspondence
(`InfiniteGalois.fixingSubgroup_fixedField`, where closedness of `H` enters and nowhere else)
turns the conjugates of `y` over the fixed field into `H`-orbit points, so the whole conjugate
cluster of `y` has diameter `2 ε`. The descent estimate
`Atlas.Knowledge.conjugateDiameterBound`—Ax's induction on the degree, run on the zeros of
Hasse derivatives—then produces an element of the fixed field within `2 ε` times a constant
depending only on `p`, and `ε` was arbitrary.

The action is `Atlas.Knowledge.PadicComplexGaloisAction`, and the fixed points are stated as a
set equality: the left side is fixed points of the extended action on the completion, the
right side the topological closure of the image of the fixed field of Mathlib's Galois
correspondence, which is how the completion `𝒞` of an algebraic extension of `ℚ_[p]` lives
inside `ℂ_[p]`. One inclusion is soft—the fixed points form a closed subfield containing the
fixed field—and the content is the other: an element fixed by `H` is approximated by
`H`-fixed algebraic elements. The statement is over the base `ℚ_[p]`, which subsumes each
mixed-characteristic local field `K`: a closed subgroup of `G_K` is a closed subgroup of
`G_{ℚ_p}` under any realization of `G_K` as a fixing subgroup, per the conjugation transport
of `Atlas.Knowledge.ArtinMapProfiniteTransferNaturality`. The source of the closed-subgroup
form at this generality is Ax's theorem, whose henselian "local field" covers every
`(ℚ_p^alg)^H` and whose perfect closure is the identity in characteristic `0`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
* [Ax1970] J. Ax, *Zeros of polynomials over local fields—The Galois action*, J. Algebra
  **15** (1970), 417–428.
* [BrinonConrad2009] O. Brinon, B. Conrad, *CMI Summer School notes on p-adic Hodge theory
  (preliminary version)*, available at math.stanford.edu/~conrad/papers/notes.pdf, 2009.
-/

open Atlas.Knowledge.PadicComplexGaloisAction

namespace Atlas.Knowledge

/-- The **Ax–Sen–Tate theorem**: the fixed points of a closed subgroup of the absolute Galois
group of `ℚ_[p]` acting on `ℂ_[p]` are the closure of the image of its fixed field
([Hyeon 2025, §5, p.19][Hyeon2025]; [Ax 1970, Theorem, p.417][Ax1970];
[Brinon–Conrad 2009, Prop. 2.1.2, p.12][BrinonConrad2009]). -/
theorem axSenTate (p : ℕ) [Fact p.Prime] (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsClosed (H : Set (Field.absoluteGaloisGroup ℚ_[p]))) :
    {x : ℂ_[p] | ∀ σ ∈ H, padicComplexGaloisAction p σ x = x}
      = closure
          (((↑) : PadicAlgCl p → ℂ_[p]) ''
            (IntermediateField.fixedField (PadicComplexGaloisAction.toGalSubgroup H) :
              Set (PadicAlgCl p))) := by
  set F := IntermediateField.fixedField (toGalSubgroup H) with hF
  set M : ℝ := (‖(p : PadicAlgCl p)‖⁻¹) ^ ((p : ℝ) / ((p : ℝ) - 1) ^ 2) with hM
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).two_le
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM]
    refine Real.one_le_rpow ?_ (by positivity)
    rw [ConjugateDiameterBound.norm_natCast_self, inv_inv]
    linarith
  apply Set.Subset.antisymm
  · -- the content: a fixed point is a limit of fixed-field elements
    intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    set δ : ℝ := ε / (2 * (1 + 2 * M)) with hδ
    have hδ0 : 0 < δ := by
      rw [hδ]
      have : (0 : ℝ) < 1 + 2 * M := by linarith
      positivity
    obtain ⟨y, hy⟩ : ∃ y : PadicAlgCl p, dist x (y : ℂ_[p]) < δ := by
      obtain ⟨-, ⟨y, rfl⟩, hy⟩ :=
        Metric.mem_closure_iff.mp
          (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p) x) δ hδ0
      exact ⟨y, hy⟩
    -- almost-invariance of the algebraic approximation
    have horbit : ∀ σ ∈ H, ‖toAlgEquiv σ y - y‖ ≤ 2 * δ := by
      intro σ hσ
      have hcoe : ‖toAlgEquiv σ y - y‖
          = dist (padicComplexGaloisAction p σ (y : ℂ_[p])) (y : ℂ_[p]) := by
        rw [padicComplexGaloisAction_coe, dist_eq_norm, ← PadicComplex.norm_extends]
        push_cast
        rfl
      rw [hcoe]
      calc dist (padicComplexGaloisAction p σ (y : ℂ_[p])) (y : ℂ_[p])
          ≤ dist (padicComplexGaloisAction p σ (y : ℂ_[p]))
              (padicComplexGaloisAction p σ x) + dist x (y : ℂ_[p]) := by
            rw [hx σ hσ]
            exact dist_triangle _ _ _
        _ = dist (y : ℂ_[p]) x + dist x (y : ℂ_[p]) :=
            congrArg (· + _) ((isometry_algEquiv σ).dist_eq _ _)
        _ ≤ 2 * δ := by
            rw [dist_comm (y : ℂ_[p]) x]
            linarith
    -- the whole conjugate cluster of `y` has diameter `2 δ`, through the Krull correspondence
    have hΔ : ∀ β : PadicAlgCl p, (Polynomial.aeval β) (minpoly ↥F y) = 0 → ‖β - y‖ ≤ 2 * δ := by
      intro β hβ
      obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
        (Algebra.IsAlgebraic.isAlgebraic (R := ↥F) y) hβ
      have hKrull : F.fixingSubgroup = toGalSubgroup H :=
        InfiniteGalois.fixingSubgroup_fixedField ⟨toGalSubgroup H, hH⟩
      set τ : ↥(F.fixingSubgroup) := (IntermediateField.fixingSubgroupEquiv F).symm σ
      have hτH : τ.1 ∈ H := (SetLike.ext_iff.mp hKrull _).mp τ.2
      have hτy : toAlgEquiv τ.1 y = β := by
        rw [← hσ]
        rfl
      rw [← hτy]
      exact horbit τ.1 hτH
    obtain ⟨a, haF, ha⟩ := conjugateDiameterBound F y (by positivity) hΔ
    refine ⟨(a : ℂ_[p]), ⟨a, haF, rfl⟩, ?_⟩
    have hya : dist (y : ℂ_[p]) (a : ℂ_[p]) = ‖y - a‖ := by
      rw [dist_eq_norm, ← PadicComplex.norm_extends]
      push_cast
      rfl
    calc dist x (a : ℂ_[p]) ≤ dist x (y : ℂ_[p]) + dist (y : ℂ_[p]) (a : ℂ_[p]) :=
          dist_triangle _ _ _
      _ ≤ δ + 2 * δ * M := by
          rw [hya]
          exact add_le_add hy.le (le_trans ha (by rw [← hM]))
      _ < ε := by
          have hM0 : (0 : ℝ) < M := lt_of_lt_of_le one_pos hM1
          rw [hδ]
          have h1 : (0 : ℝ) < 1 + 2 * M := by linarith
          have h1' : (1 + 2 * M) ≠ 0 := h1.ne'
          calc ε / (2 * (1 + 2 * M)) + 2 * (ε / (2 * (1 + 2 * M))) * M
              = ε / 2 := by field_simp
            _ < ε := by linarith
  · -- the soft inclusion: the fixed-point set is closed and contains the fixed field
    refine closure_minimal ?_ ?_
    · rintro _ ⟨y, hyF, rfl⟩ σ hσ
      rw [padicComplexGaloisAction_coe]
      exact congrArg _
        ((IntermediateField.mem_fixedField_iff (toGalSubgroup H) _).mp hyF (toAlgEquiv σ) hσ)
    · have h : {x : ℂ_[p] | ∀ σ ∈ H, padicComplexGaloisAction p σ x = x}
          = ⋂ σ ∈ H, {x | padicComplexGaloisAction p σ x = x} := by
        ext x
        simp
      rw [h]
      exact isClosed_biInter fun σ _ =>
        isClosed_eq (isometry_algEquiv σ).continuous continuous_id

namespace AxSenTate

/-- For an **open** subgroup the closure in the Ax–Sen–Tate theorem collapses: the fixed
points of `H` on `ℂ_[p]` are exactly the image of its fixed field. Openness makes the fixed
field finite-dimensional over `ℚ_[p]` through the Krull correspondence, and a
finite-dimensional subspace of `ℂ_[p]` is closed. -/
theorem fixedPoints_eq_image_of_isOpen (p : ℕ) [Fact p.Prime]
    (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p]))) :
    {x : ℂ_[p] | ∀ σ ∈ H, padicComplexGaloisAction p σ x = x}
      = (((↑) : PadicAlgCl p → ℂ_[p]) ''
          (IntermediateField.fixedField (toGalSubgroup H) : Set (PadicAlgCl p))) := by
  have hclosed : IsClosed (H : Set (Field.absoluteGaloisGroup ℚ_[p])) :=
    Subgroup.isClosed_of_isOpen H hH
  rw [axSenTate p H hclosed]
  set L := IntermediateField.fixedField (toGalSubgroup H) with hL
  have hKrull : L.fixingSubgroup = toGalSubgroup H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨toGalSubgroup H, hclosed⟩
  haveI hfd : FiniteDimensional ℚ_[p] ↥L := by
    refine (InfiniteGalois.isOpen_iff_finite L).mp ?_
    rw [hKrull]
    exact hH
  let f : PadicAlgCl p →ₗ[ℚ_[p]] ℂ_[p] :=
    (Algebra.linearMap (PadicAlgCl p) ℂ_[p]).restrictScalars ℚ_[p]
  have himg : (((↑) : PadicAlgCl p → ℂ_[p]) '' (L : Set (PadicAlgCl p)))
      = (Submodule.map f (Subalgebra.toSubmodule L.toSubalgebra) : Set ℂ_[p]) := rfl
  rw [himg]
  haveI : FiniteDimensional ℚ_[p]
      ↥(Submodule.map f (Subalgebra.toSubmodule L.toSubalgebra)) := by infer_instance
  exact (Submodule.map f
    (Subalgebra.toSubmodule L.toSubalgebra)).closed_of_finiteDimensional.closure_eq

/-- The elementwise form of the open case: a scalar of `ℂ_[p]` fixed by every element of an
open subgroup comes from the fixed field. -/
theorem exists_algebraMap_eq_of_isOpen (p : ℕ) [Fact p.Prime]
    (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p]))) {c : ℂ_[p]}
    (hc : ∀ σ ∈ H, padicComplexGaloisAction p σ c = c) :
    ∃ a : ↥(IntermediateField.fixedField (toGalSubgroup H)),
      algebraMap ↥(IntermediateField.fixedField (toGalSubgroup H)) ℂ_[p] a = c := by
  have hmem : c ∈ {x : ℂ_[p] | ∀ σ ∈ H, padicComplexGaloisAction p σ x = x} := hc
  rw [fixedPoints_eq_image_of_isOpen p H hH] at hmem
  obtain ⟨a, haL, ha⟩ := hmem
  exact ⟨⟨a, haL⟩, ha⟩

end AxSenTate

end Atlas.Knowledge
