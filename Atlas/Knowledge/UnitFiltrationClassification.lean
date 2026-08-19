import Mathlib
import Atlas.Knowledge.AbsoluteInertiaDegree
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.FreeFiltered
import Atlas.Knowledge.IsStarQuotient
import Atlas.Knowledge.IsUnitFiltration
import Atlas.Knowledge.ShiftRhoEP
import Atlas.Knowledge.TRhoEP

/-!
# classification of the unit filtration

The source's classification of the unit filtration of a mixed-characteristic local field, in
its two halves. Without a `p`-th root of unity the filtration is `(f_K, ρ_K)`-free—isomorphic
to the free model `M_{ρ_K}^{f_K}` of `Atlas.Knowledge.FreeFiltered`—and with one it is
presented, in the sense of `Atlas.Knowledge.IsStarQuotient`, by a unique extended jump pair:
the invariant `(I_K, β_K)` of the field. Uniqueness is what makes it an invariant, and the
identification `Atlas.Knowledge.filtOrd_jumpSetVector` is how it is read off a presentation:
the filtered order of the kernel's normal form is the jump set of the pair. Which pairs occur
is answered by `Atlas.Knowledge.JumpSetRealization`.

## Main statements

Both are claims recorded ahead of their proofs.

* `unitFiltration_isFree_iff` — the unit filtration is free exactly when the field has no
  `p`-th root of unity other than `1`.
* `existsUnique_isStarQuotient_unitFiltration` — with a `p`-th root of unity, a unique extended
  jump pair presents the unit filtration.

## Implementation notes

The condition `μ_p (K) ≠ {1}` is spelled as a unit of the field of order exactly `p`: a `ζ`
with `ζ ^ p = 1` and `ζ ≠ 1`. Uniqueness in the second claim runs over every extended jump
pair, not only the admissible ones—the source bounds the orbit of a normal form by one pair
with no admissibility hypothesis
([Pagano 2022, Cor. 3.35, p.433][Pagano2022])—and admissibility of the unique pair then follows
by combining `Atlas.Knowledge.UnitFiltrationQuasiFree` with
`Atlas.Knowledge.IsStarQuotient.isAdmissibleJumpPair`, so it is not restated here. The
uniformizer of the presentation is `p` itself, matching the defect reading of the quasi-free
claim.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- The unit filtration of a mixed-characteristic local field is `(f_K, ρ_K)`-free exactly when
the field has no `p`-th root of unity other than `1`. Claim recorded ahead of its proof
([Pagano 2022, Thm. 5.2, p.442][Pagano2022]). -/
theorem unitFiltration_isFree_iff (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (p e f : ℕ+) [Fact (p : ℕ).Prime] (hp1 : 1 < p)
    (hp : (p : ℕ) = residueCharacteristic K)
    (he : (e : ℕ) = absoluteRamificationIndex K)
    (hf : (f : ℕ) = absoluteInertiaDegree K)
    [Module ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup K 1))]
    (F : FilteredModule ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup K 1)))
    (hF : IsUnitFiltration K (p : ℕ) F) :
    IsFree (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1) f F ↔
      ¬∃ ζ : Kˣ, ζ ^ (p : ℕ) = 1 ∧ ζ ≠ 1 := by
  sorry

/-- With a `p`-th root of unity in the field, a unique extended jump pair presents the unit
filtration of a mixed-characteristic local field as a star quotient: the invariant
`(I_K, β_K)` of the field. Claim recorded ahead of its proof
([Pagano 2022, Thm. 5.3, p.442][Pagano2022]). -/
theorem existsUnique_isStarQuotient_unitFiltration (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] (p e f : ℕ+) [Fact (p : ℕ).Prime]
    (hp1 : 1 < p) (hp : (p : ℕ) = residueCharacteristic K)
    (he : (e : ℕ) = absoluteRamificationIndex K)
    (hf : (f : ℕ) = absoluteInertiaDegree K)
    (hμ : ∃ ζ : Kˣ, ζ ^ (p : ℕ) = 1 ∧ ζ ≠ 1)
    [Module ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup K 1))]
    (F : FilteredModule ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup K 1)))
    (hF : IsUnitFiltration K (p : ℕ) F) :
    ∃! P : Finset (ℕ+ × ℕ+),
      IsJumpPair (ρ_ep e p hp1) (Shift.T_star (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1)) P ∧
        IsStarQuotient (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1) f PadicInt.irreducible_p P F := by
  sorry

end Atlas.Knowledge
