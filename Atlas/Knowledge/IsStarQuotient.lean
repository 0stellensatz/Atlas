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
quasi-free module reaches the star index, which completes its admissibility in the sense of
`Atlas.Knowledge.IsAdmissibleJumpPair`; that each local field is presented by a unique pair is
`Atlas.Knowledge.UnitFiltrationClassification`, and that every admissible pair arises this way
is `Atlas.Knowledge.JumpSetRealization`.

## Main definitions

* `IsStarQuotient` — a strict filtered surjection from the star model with kernel spanned by
  the normal form of the pair.

## Main statements

* `IsStarQuotient.isAdmissibleJumpPair` — an extended jump pair presenting a quasi-free module
  is admissible. Claim recorded ahead of its proof.

## Implementation notes

Strictness is stated as `Submodule.map φ` carrying each step of the model onto the step of the
target; at the first step it is surjectivity of `φ`, the chains starting at `⊤`. The
uniformizer generating the kernel's coordinates is a parameter guarded by its irreducibility,
as in `Atlas.Knowledge.QuasiFreeFiltered` and as in the source, which fixes a uniformizer for
the whole of its §3.3; the guard is not consumed by the existential formula, which is why the
definition scopes the unused-variable linter off, but without it the notion degenerates—at
`π = 0` the normal form of *every* pair is the zero vector, since the multiplicities live in
`ℕ+`, and the star model would be a star quotient of itself by every pair whatever. The span is
not independent of the choice of uniformizer—the coordinates of the normal form scale by
different units—but the existential over `φ` absorbs it, a diagonal-unit automorphism of the
model carrying one normal form to the other.

Two gaps between the recorded claim and the letter of the cited theorem are deliberate. The
source's §3.3 fixes a *complete* discrete valuation ring, while the layer's §3 vocabulary—
`Atlas.Knowledge.FreeFiltered`, `Atlas.Knowledge.QuasiFreeFiltered`—is stated over a plain one,
completeness entering as the module-level field `IsQuasiFree.complete` that the source's
propositions consume; this claim inherits that widening, recorded here at the first claim that
depends on it. And the source concludes admissibility for quasi-free modules *that are not
free*, a hypothesis dropped here because it is implied: a nonempty pair has every nonzero
coordinate of its normal form of the form `π ^ β` with `β ≥ 1`, so the kernel generator is
`π • w` with `w` outside the kernel and the presented module has torsion, while the empty
pair's kernel is `⊥` and the presented module is the star model itself, whose graded dimension
at the star level already fails quasi-freeness.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {M : Type*} [AddCommGroup M] [Module R M]

set_option linter.unusedVariables false in
-- The guard `hπ` is not consumed by the formula—the value is the same at any scalar—but the
-- notion is the source's only at a uniformizer, and carrying the guard keeps junk uniformizers
-- unstatable.
/-- A **star-quotient presentation** of a filtered module by an extended jump pair: a strict
filtered surjection from the star model `M_ρ^{f - 1} ⊕ M_ρ^*` whose kernel is spanned by the
normal form of the pair at a uniformizer—the source's `M_ρ^{f - 1} ⊕ M_ρ^* ⧸ R v_{(I, β)}`,
read through the map instead of the quotient ([Pagano 2022, Thm. 3.37, p.434][Pagano2022]). -/
def IsStarQuotient (ρ : Shift) (hρ : (Shift.T ρ).Finite) (f : ℕ+) {π : R}
    (hπ : Irreducible π) (P : Finset (ℕ+ × ℕ+)) (F : FilteredModule R M) : Prop :=
  ∃ φ : (↥(Shift.starIndex hρ f) → R) →ₗ[R] M,
    IsFilteredHom (freeFiltered ρ (Shift.starIndex hρ f)) F φ ∧
      (∀ i, Submodule.map φ ((freeFiltered (R := R) ρ (Shift.starIndex hρ f)).filt i) =
        F.filt i) ∧
      LinearMap.ker φ = Submodule.span R {jumpSetVector π (Shift.starIndex hρ f) P}

/-- An extended jump pair presenting a quasi-free module reaches the star index: its minimal
level, iterated along `ρ` as many times as its multiplicity, lands on `e_ρ^*`—the image half of
the source's classification, whose forward direction computes the invariant of the presented
module. Being an extended jump pair is the hypothesis `hP`, which `IsStarQuotient` alone does
not impose, so what the claim adds to `Atlas.Knowledge.IsAdmissibleJumpPair` is the reaching
condition. Claim recorded ahead of its proof
([Pagano 2022, Thm. 3.37, p.434][Pagano2022]). -/
theorem IsStarQuotient.isAdmissibleJumpPair {ρ : Shift} {hρ : (Shift.T ρ).Finite} {f : ℕ+}
    {π : R} (hπ : Irreducible π) {P : Finset (ℕ+ × ℕ+)} {F : FilteredModule R M}
    (hqf : IsQuasiFree ρ hρ f hπ F) (hP : IsJumpPair ρ (Shift.T_star ρ hρ) P)
    (hQ : IsStarQuotient ρ hρ f hπ P F) : IsAdmissibleJumpPair ρ hρ P := by
  sorry

end Atlas.Knowledge
