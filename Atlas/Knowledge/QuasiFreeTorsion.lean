import Mathlib
import Atlas.Knowledge.IsStarQuotient
import Atlas.Knowledge.QuasiFreeFiltered

/-!
# torsion of a quasi-free module

The source's recovery of the torsion from the invariant: the `π`-power torsion of a quasi-free
filtered module presented by the pair `(I_{M_•}, β_{M_•})` is cyclic, a copy of
`R ⧸ π^{β (max I)} R`—the multiplicity at the largest level of the presenting pair. Through
the unit filtration this is the group-of-roots-of-unity computation: the torsion of the
principal units is `μ_{p^∞}`, and its order is read off the invariant, which is what the
source uses to steer the realizability constructions of
`Atlas.Knowledge.JumpSetRealization`.

## Main statements

* `torsion_equiv_of_isStarQuotient` — the torsion of a presented quasi-free module is
  `R ⧸ π^{β (max I)} R`. Claim recorded ahead of its proof.

## Implementation notes

Over a discrete valuation ring the `π`-power torsion is the whole torsion submodule, so the
left side is Mathlib's `Submodule.torsion`, and the right side is the quotient by the ideal
the power spans. The maximal level enters as a hypothesized member of the presenting pair
above all others—the relational reading, as with the minimal level of
`Atlas.Knowledge.IsAdmissibleJumpPair`—so no junk maximum is formed; the presenting pair of a
quasi-free non-free module is nonempty, its normal form spanning a nonzero kernel, so the
hypothesis is satisfiable exactly where the source speaks. The equivalence is linear and its
existence is the claim, the bundling pattern of the layer's other isomorphism claims.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- The torsion of a presented quasi-free module is cyclic of length the multiplicity at the
largest level: `M₁[π^∞] ≃ R ⧸ π^{β (max I)} R` for `(I, β)` the presenting pair. Claim
recorded ahead of its proof ([Pagano 2022, Prop. 3.41, p.435][Pagano2022]). -/
theorem torsion_equiv_of_isStarQuotient (ρ : Shift) (hρ : (Shift.T ρ).Finite) (f : ℕ+)
    {π : R} (hπ : Irreducible π) {P : Finset (ℕ+ × ℕ+)} {F : FilteredModule R M}
    (hqf : IsQuasiFree ρ hρ f hπ F) (hP : IsJumpPair ρ (Shift.T_star ρ hρ) P)
    (hQ : IsStarQuotient ρ hρ f hπ P F) {q : ℕ+ × ℕ+} (hq : q ∈ P)
    (hmax : ∀ r ∈ P, r.1 ≤ q.1) :
    Nonempty ((↥(Submodule.torsion R M)) ≃ₗ[R] (R ⧸ Ideal.span {π ^ (q.2 : ℕ)})) := by
  sorry

end Atlas.Knowledge
