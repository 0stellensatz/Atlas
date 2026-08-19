import Mathlib
import Atlas.Knowledge.AbsoluteInertiaDegree
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.IsStarQuotient
import Atlas.Knowledge.IsStronglyEisenstein
import Atlas.Knowledge.IsUnitFiltration
import Atlas.Knowledge.ShiftRhoEP
import Atlas.Knowledge.TRhoEP

/-!
# extremal invariant of a strongly Eisenstein polynomial

The source's Theorem 10.3: away from `(p, j) = (2, 0)`, an Eisenstein polynomial over
`ℚ_{p^f} (ζ_{p^{j+1}})` is strongly Eisenstein in the sense of
`Atlas.Knowledge.IsStronglyEisenstein` exactly when the invariant of the field it cuts out is
the two-point extremal pair—level `e / (p^{v_p (e)} (p - 1))` with multiplicity `v_p (e) + 1`,
and level `e_j + 1` with multiplicity `j + 1`. This is the jump set the source shows occurs
with the highest probability, and the equivalence is how one reads "most likely" off the
polynomial: a uniformizer in the linear coefficient. The excluded case is genuine—the source
exhibits `x ^ 2 + 2 * x + 2` over `ℚ_2`, strongly Eisenstein with invariant `{1}`.

## Main statements

* `isStronglyEisenstein_iff_isStarQuotient` — strongly Eisenstein exactly when the cut-out
  field's invariant is the extremal pair. Claim recorded ahead of its proof.

## Implementation notes

The base is characterized relationally, as in `Atlas.Knowledge.EisensteinFieldInvariant` at
`j = 0`: residue characteristic `p`, absolute ramification index `p^j (p - 1)`, absolute
inertia degree `f`, and a primitive `p^{j+1}`-th root of unity—a root of unity whose `p^j`-th
power is not yet `1`—pin the field to `ℚ_{p^f} (ζ_{p^{j+1}})`; the star model's parameters
come from the base and the degree while the filtration presented is the cut-out field's,
which is right because an Eisenstein generator makes the extension totally ramified, the
inertia degree passing up unchanged and the ramification index multiplying by the degree. The
source's standing `e ∈ p^{j+1} (p - 1) ℤ_{≥1}` is the divisibility hypothesis, on top of the
equation tying `e` to the degree; together they force `p` to divide the degree, so the
source's `d ≥ 2` for the strongly Eisenstein notion is implied here by the hypotheses. The
extremal pair's levels are spelled with truncating division and `Nat.toPNat'`, both exact and
positive under the divisibility, and the two points are always distinct, their multiplicities
differing. The exclusion `(p, j) ≠ (2, 0)` is the disjunction of the two disequalities. The
equivalence quantifies its field side over every module structure and unit filtration of the
cut-out field; one direction of the informal statement therefore leans on the existence claim
`Atlas.Knowledge.exists_isUnitFiltration`, which is what makes the quantified form and the
source's form the same statement.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- Away from `(p, j) = (2, 0)`, an Eisenstein polynomial over `ℚ_{p^f} (ζ_{p^{j+1}})` is
strongly Eisenstein exactly when the invariant of the field it cuts out is the extremal pair
`{(e / (p^{v_p (e)} (p - 1)), v_p (e) + 1), (e_j + 1, j + 1)}`. Claim recorded ahead of its
proof ([Pagano 2022, Thm. 10.3, pp.470–471][Pagano2022]). -/
theorem isStronglyEisenstein_iff_isStarQuotient (p e f : ℕ+) (j : ℕ) [Fact (p : ℕ).Prime]
    (hp1 : 1 < p) (hpj : (p : ℕ) ≠ 2 ∨ j ≠ 0)
    (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsMixedCharLocalField E]
    (hpE : (p : ℕ) = residueCharacteristic E)
    (heE : (p : ℕ) ^ j * ((p : ℕ) - 1) = absoluteRamificationIndex E)
    (hfE : (f : ℕ) = absoluteInertiaDegree E)
    (hζ : ∃ ζ : Eˣ, ζ ^ ((p : ℕ) ^ (j + 1)) = 1 ∧ ζ ^ ((p : ℕ) ^ j) ≠ 1)
    (g : Polynomial ↥𝒪[E]) (hg : g.IsEisensteinAt (IsLocalRing.maximalIdeal ↥𝒪[E]))
    (hdvd : (p : ℕ) ^ (j + 1) * ((p : ℕ) - 1) ∣ (e : ℕ))
    (he : (e : ℕ) = g.natDegree * ((p : ℕ) ^ j * ((p : ℕ) - 1)))
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
    [Algebra E K] (π : K) (hroot : Polynomial.aeval π (g.map (algebraMap ↥𝒪[E] E)) = 0)
    (hgen : Algebra.adjoin E {π} = ⊤) :
    IsStronglyEisenstein g ↔
      ∀ (m : Module ℤ_[(p : ℕ)] (Additive ↥(higherUnitGroup K 1)))
        (F : @FilteredModule ℤ_[(p : ℕ)] _ (Additive ↥(higherUnitGroup K 1)) _ m),
        @IsUnitFiltration K _ _ (p : ℕ) _ m F →
          @IsStarQuotient ℤ_[(p : ℕ)] _ _ _ _ _ m (ρ_ep e p hp1) (T_ρ_ep_finite e p hp1) f
            ((p : ℕ) : ℤ_[(p : ℕ)]) PadicInt.irreducible_p
            ({(((e : ℕ) / ((p : ℕ) ^ padicValNat (p : ℕ) (e : ℕ) * ((p : ℕ) - 1))).toPNat',
                ⟨padicValNat (p : ℕ) (e : ℕ) + 1, Nat.succ_pos _⟩),
              (((e : ℕ) / ((p : ℕ) ^ j * ((p : ℕ) - 1)) + 1).toPNat',
                ⟨j + 1, Nat.succ_pos _⟩)} : Finset (ℕ+ × ℕ+)) F := by
  sorry

end Atlas.Knowledge
