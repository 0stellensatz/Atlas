import Mathlib
import Atlas.Knowledge.AbsoluteInertiaDegree
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.IsAdmissibleJumpPair
import Atlas.Knowledge.IsStarQuotient
import Atlas.Knowledge.IsUnitFiltration
import Atlas.Knowledge.ShiftRhoEP
import Atlas.Knowledge.TRhoEP

/-!
# realizability of admissible jump sets

Every admissible extended jump pair is the invariant of a local field: for `p` prime, `f` a
positive integer, and `e` a positive multiple of `p - 1`, each pair admissible for
`ρ_ep e p` in the sense of `Atlas.Knowledge.IsAdmissibleJumpPair` presents, as a star quotient
`Atlas.Knowledge.IsStarQuotient`, the unit filtration of some mixed-characteristic local field
with residue characteristic `p`, absolute inertia degree `f`, and absolute ramification index
`e`. Together with `Atlas.Knowledge.UnitFiltrationClassification` this closes the circle of the
source's §5: the invariants `(I_K, β_K)` that occur among fields of given `(p, f, e)` with a
`p`-th root of unity are exactly the admissible pairs.

## Main statements

* `jumpSetRealization` — every admissible extended jump pair is realized by a
  mixed-characteristic local field. Claim recorded ahead of its proof.

## Implementation notes

The source produces the field as a totally ramified extension of `ℚ_{p^f} (ζ_p)` cut out by an
Eisenstein factor of an explicit polynomial; the claim records the interface of that
construction—existence of a field with the prescribed residue characteristic, inertia degree,
ramification index, and invariant—as an existential over the field type and its instances,
after `Atlas.Knowledge.IsMLFType`. Containing `ℚ_{p^f} (ζ_p)` also hands the field a `p`-th
root of unity, recorded as its own conjunct so that the produced field feeds the hypothesis of
`Atlas.Knowledge.existsUnique_isStarQuotient_unitFiltration` directly. The divisibility
`(p - 1) ∣ e` is the source's standing `e ∈ (p - 1) ℤ_{≥1}` for its §5's realizability
discussion: a field containing a `p`-th root of unity has ramification index divisible by
`p - 1`, so without it nothing is realizable and the claim would be false. The conclusion
quantifies over every module structure and unit filtration of the produced field, the honest
reading of "`(I_K, β_K`) `= (I, β)`"; `Atlas.Knowledge.IsUnitFiltration` says why the
quantification costs nothing.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- Every admissible extended jump pair is the invariant of a mixed-characteristic local field
with the prescribed residue characteristic, absolute inertia degree, and absolute ramification
index, carrying a `p`-th root of unity—a totally ramified extension of `ℚ_{p^f} (ζ_p)` in the
source's construction. Claim recorded ahead of its proof
([Pagano 2022, Thm. 5.4, pp.442–443][Pagano2022]). -/
theorem jumpSetRealization (p e f : ℕ+) [Fact (p : ℕ).Prime] (hp1 : 1 < p)
    (hdvd : ((p : ℕ) - 1) ∣ (e : ℕ)) (P : Finset (ℕ+ × ℕ+))
    (hP : IsAdmissibleJumpPair (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1) P) :
    ∃ (K : Type) (_ : Field K) (_ : ValuativeRel K) (_ : TopologicalSpace K)
      (_ : IsMixedCharLocalField K),
      (p : ℕ) = residueCharacteristic K ∧ (f : ℕ) = absoluteInertiaDegree K ∧
        (e : ℕ) = absoluteRamificationIndex K ∧ (∃ ζ : Kˣ, ζ ^ (p : ℕ) = 1 ∧ ζ ≠ 1) ∧
        ∀ (m : Module ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup K 1)))
          (F : @FilteredModule ℤ_[(p : ℕ)] _ (Additive ↥(higherUnitGroup K 1)) _ m),
          @IsUnitFiltration K _ _ (p : ℕ) _ m F →
            @IsStarQuotient ℤ_[(p : ℕ)] _ _ _ _ _ m (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1) f
              ((p : ℕ) : ℤ_[(p : ℕ)]) PadicInt.irreducible_p P F := by
  sorry

end Atlas.Knowledge
