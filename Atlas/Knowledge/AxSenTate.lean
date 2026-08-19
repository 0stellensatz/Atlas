import Mathlib
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
  fixed field. Claim recorded ahead of its proof.

## Implementation notes

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

namespace Atlas.Knowledge

/-- The **Ax–Sen–Tate theorem**: the fixed points of a closed subgroup of the absolute Galois
group of `ℚ_[p]` acting on `ℂ_[p]` are the closure of the image of its fixed field. Claim
recorded ahead of its proof ([Hyeon 2025, §5, p.19][Hyeon2025];
[Ax 1970, Theorem, p.417][Ax1970]; [Brinon–Conrad 2009, Prop. 2.1.2, p.12][BrinonConrad2009]). -/
theorem axSenTate (p : ℕ) [Fact p.Prime] (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsClosed (H : Set (Field.absoluteGaloisGroup ℚ_[p]))) :
    {x : ℂ_[p] | ∀ σ ∈ H, padicComplexGaloisAction p σ x = x}
      = closure
          (((↑) : PadicAlgCl p → ℂ_[p]) ''
            (IntermediateField.fixedField (PadicComplexGaloisAction.toGalSubgroup H) :
              Set (PadicAlgCl p))) := by
  sorry

end Atlas.Knowledge
