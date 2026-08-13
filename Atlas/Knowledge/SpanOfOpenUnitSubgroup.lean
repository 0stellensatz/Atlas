import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# span of an open unit subgroup

An open subgroup of the unit group of a mixed-characteristic local field spans the field over
`ℚ_p`. This is the one complete, self-contained proof in either anabelian source—the same
lemma, stated twice: the second source cites the first verbatim. It is the step that turns
group data back into field data in both main theorems: an isomorphism of filtered Galois
groups eventually hands one an open subgroup of units inside a common overfield, and this
lemma is why the subfield it spans is the whole field.

The proof is the sources': the span contains a translate of the open image around each of its
points, so it is open, and a `ℚ_p`-submodule with nonempty interior is everything because the
units of `ℚ_p` accumulate at `0`—Mathlib's `Submodule.eq_top_of_nonempty_interior'`, which is
the "the `p`-adic topology on `ℚ_p` is not discrete" of the sources.

## Main statements

* `spanOfOpenUnitSubgroup` — for `I ≤ Kˣ` a subgroup of integral units whose image in `K` is
  open, `span ℚ_[p] I = ⊤`.

## Implementation notes

The carrier `Atlas.Knowledge.IsMixedCharLocalField` deliberately carries no `ℚ_[p]`-algebra
structure, so the statement takes one, together with its continuity, as hypotheses. Openness is
stated for the image of `I` in `K`: the sources say "open subgroup of `U_K`", and the two are
the same condition because `U_K` is open in `K`—the reduction the sources' proofs open with.
The containment of `I` in the integral units is the sources' hypothesis and is carried by the
statement, though the proof consumes only the openness.

## References

* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

set_option linter.unusedVariables false in
-- The containment in the integral units is the sources' hypothesis and stays in the statement;
-- the proof consumes only the openness.
/-- An open subgroup of the unit group of a mixed-characteristic local field spans the field
over `ℚ_p` ([Mochizuki 1997, Lem. 4.1, p.505][Mochizuki1997];
[Hyeon 2025, Lem. 6.1, p.21][Hyeon2025]). -/
theorem spanOfOpenUnitSubgroup {p : ℕ} [Fact p.Prime] (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] [Algebra ℚ_[p] K] [ContinuousSMul ℚ_[p] K]
    {I : Subgroup Kˣ} (hIU : ∀ u ∈ I, (u : K) ∈ 𝒪[K])
    (hI : IsOpen ((fun u : Kˣ => (u : K)) '' I)) :
    Submodule.span ℚ_[p] ((fun u : Kˣ => (u : K)) '' I) = ⊤ := by
  haveI : (nhdsWithin (0 : ℚ_[p]) {x : ℚ_[p] | IsUnit x}).NeBot := by
    have h0 : {x : ℚ_[p] | IsUnit x} = {(0 : ℚ_[p])}ᶜ := by
      ext x
      simp [isUnit_iff_ne_zero]
    rw [h0]
    infer_instance
  refine Submodule.eq_top_of_nonempty_interior' _
    ⟨1, interior_maximal Submodule.subset_span hI ⟨1, I.one_mem, Units.val_one⟩⟩

end Atlas.Knowledge
