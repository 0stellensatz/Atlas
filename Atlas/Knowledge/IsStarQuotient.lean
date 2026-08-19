import Mathlib
import Atlas.Knowledge.FreeFiltered
import Atlas.Knowledge.IsAdmissibleJumpPair
import Atlas.Knowledge.IsFilteredHom
import Atlas.Knowledge.JumpSetVector
import Atlas.Knowledge.QuasiFreeFiltered

/-!
# star-quotient presentation

Presentation of a filtered module as the source's `M_ρ^{f - 1} ⊕ M_ρ^* ⧸ R v_{(I, β)}`: a
filtered morphism out of the star model `Atlas.Knowledge.freeFiltered` that is strict—each
filtration step maps *onto* the corresponding step—and whose kernel is spanned by the normal
form `Atlas.Knowledge.jumpSetVector` of an extended jump pair. This is the right-hand side of
the source's classification of quasi-free modules, stated without a quotient construction: a
strict surjection with the prescribed kernel *is* an isomorphism from the quotient carrying the
image filtration. The half of that classification recorded here is that the pair presenting a
quasi-free module is admissible in the sense of `Atlas.Knowledge.IsAdmissibleJumpPair`; that
each local field is presented by a unique pair is `Atlas.Knowledge.UnitFiltrationClassification`,
and that every admissible pair arises this way is `Atlas.Knowledge.jumpSetRealization`.

## Main definitions

* `IsStarQuotient` — a strict filtered surjection from the star model with kernel spanned by
  the normal form of the pair.

## Main statements

* `IsStarQuotient.isAdmissibleJumpPair` — the pair presenting a quasi-free module is
  admissible. Claim recorded ahead of its proof.

## Implementation notes

Strictness is stated as `Submodule.map φ` carrying each step of the model onto the step of the
target; at the first step it is surjectivity of `φ`, the chains starting at `⊤`. The uniformizer
generating the kernel's coordinates is a parameter, as in `Atlas.Knowledge.QuasiFreeFiltered`:
the span is not independent of the choice—the coordinates of the normal form scale by different
units—but the existential over `φ` absorbs it, a diagonal-unit automorphism of the model
carrying one normal form to the other.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- A **star-quotient presentation** of a filtered module by an extended jump pair: a strict
filtered surjection from the star model `M_ρ^{f - 1} ⊕ M_ρ^*` whose kernel is spanned by the
normal form of the pair—the source's `M_ρ^{f - 1} ⊕ M_ρ^* ⧸ R v_{(I, β)}`, read through the
map instead of the quotient ([Pagano 2022, Thm. 3.37, p.434][Pagano2022]). -/
def IsStarQuotient (ρ : Shift) (hρ : (Shift.T ρ).Finite) (f : ℕ+) (π : R)
    (P : Finset (ℕ+ × ℕ+)) (F : FilteredModule R M) : Prop :=
  ∃ φ : (↥(Shift.starIndex hρ f) → R) →ₗ[R] M,
    IsFilteredHom (freeFiltered ρ (Shift.starIndex hρ f)) F φ ∧
      (∀ i, Submodule.map φ ((freeFiltered (R := R) ρ (Shift.starIndex hρ f)).filt i) =
        F.filt i) ∧
      LinearMap.ker φ = Submodule.span R {jumpSetVector π (Shift.starIndex hρ f) P}

/-- The pair presenting a quasi-free module is admissible: the image half of the source's
classification, whose forward direction computes the invariant of the presented module and
finds it reaches `e_ρ^*`. Claim recorded ahead of its proof
([Pagano 2022, Thm. 3.37, p.434][Pagano2022]). -/
theorem IsStarQuotient.isAdmissibleJumpPair {ρ : Shift} {hρ : (Shift.T ρ).Finite} {f : ℕ+}
    {π : R} (hπ : Irreducible π) {P : Finset (ℕ+ × ℕ+)} {F : FilteredModule R M}
    (hqf : IsQuasiFree ρ hρ f hπ F) (hP : IsJumpPair ρ (Shift.T_star ρ hρ) P)
    (hQ : IsStarQuotient ρ hρ f π P F) : IsAdmissibleJumpPair ρ hρ P := by
  sorry

end Atlas.Knowledge
