import Mathlib

/-!
# coefficient graph of an Eisenstein polynomial

The graph `S_{g(x)}` the source attaches to an Eisenstein polynomial: one point per nonzero
coefficient whose index has `p`-adic valuation at most that of the degree, with level the
weight of the monomial—degree times the coefficient's valuation, plus the index—divided by the
`p`-part of the index, and multiplicity one more than that `p`-adic valuation. Its
`≤_ρ`-minimal points are the pair `(I_g, β_g)` of `Atlas.Knowledge.eisensteinJumpPair`, the
polynomial-side invariant whose identification with the field-side invariant of
`Atlas.Knowledge.UnitFiltrationClassification` is the business of the source's §10.

## Main definitions

* `eisensteinGraph` — the coefficient graph, one point per contributing index.

## Main statements

* `mem_eisensteinGraph` — membership unfolded to a witnessing index.
* `eisensteinGraph_nonempty` — the graph of an Eisenstein polynomial of positive degree
  carries at least its leading point, so nothing downstream is vacuous.

## Implementation notes

The source's constraint is `v_p (i) ≤ v_p (e)` for `e` the ramification index of the field the
polynomial cuts out, which is the degree times the ramification index `p - 1` of the source's
base field; the last factor is prime to `p`, so the constraint is spelled against the degree
and no field enters the definition. The same arithmetic makes the division exact: the `p`-part
of the index divides the index and, through the constraint, the degree, hence the whole
weight—at *every* index the filter admits and every `p`, with no primality and no Eisenstein
hypothesis—and the level is at least `1`, so the division never truncates and `Nat.toPNat'`
never junks. The definition is total, and the degenerate readings are elsewhere: at
`p ∈ {0, 1}` the `p`-adic valuations collapse to `0`, so the divisor is `1`, every
multiplicity is `1`, and the graph is the plain weight graph of the polynomial—well formed,
but not the source's object, which the consuming statements' primality excludes. The valuation
of a coefficient is read through `IsDiscreteValuationRing.addVal`, whose `⊤` at a zero
coefficient is avoided by the nonvanishing filter.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

open Classical in
/-- The **coefficient graph** `S_{g(x)}` of a polynomial over a discrete valuation ring: for
each index `1 ≤ i ≤ deg g` with nonzero coefficient and `v_p (i) ≤ v_p (deg g)`, the point
whose level is the monomial weight `deg g · v (a_i) + i` divided by the `p`-part of `i` and
whose multiplicity is `v_p (i) + 1` ([Pagano 2022, §1.2.1, p.408][Pagano2022]). -/
noncomputable def eisensteinGraph (p : ℕ) (g : Polynomial R) : Finset (ℕ+ × ℕ+) :=
  ((Finset.Icc 1 g.natDegree).filter fun i =>
      g.coeff i ≠ 0 ∧ padicValNat p i ≤ padicValNat p g.natDegree).image fun i =>
    (((g.natDegree * ((addVal R) (g.coeff i)).toNat + i) / p ^ padicValNat p i).toPNat',
      ⟨padicValNat p i + 1, Nat.succ_pos _⟩)

/-- Membership in the coefficient graph, unfolded to a witnessing index. -/
theorem mem_eisensteinGraph {p : ℕ} {g : Polynomial R} {q : ℕ+ × ℕ+} :
    q ∈ eisensteinGraph p g ↔ ∃ i, (1 ≤ i ∧ i ≤ g.natDegree) ∧ g.coeff i ≠ 0 ∧
      padicValNat p i ≤ padicValNat p g.natDegree ∧
      q = (((g.natDegree * ((addVal R) (g.coeff i)).toNat + i) / p ^ padicValNat p i).toPNat',
        ⟨padicValNat p i + 1, Nat.succ_pos _⟩) := by
  classical
  simp only [eisensteinGraph, Finset.mem_image, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨i, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩
    exact ⟨i, ⟨h1, h2⟩, h3, h4, rfl⟩
  · rintro ⟨i, ⟨h1, h2⟩, h3, h4, rfl⟩
    exact ⟨i, ⟨⟨h1, h2⟩, h3, h4⟩, rfl⟩

/-- The coefficient graph of an Eisenstein polynomial of positive degree is nonempty: the
leading coefficient is a unit, so the leading index always contributes its point. -/
theorem eisensteinGraph_nonempty {p : ℕ} {g : Polynomial R}
    (hg : g.IsEisensteinAt (IsLocalRing.maximalIdeal R)) (hd : 1 ≤ g.natDegree) :
    (eisensteinGraph p g).Nonempty := by
  have hunit : IsUnit (g.coeff g.natDegree) := by
    have h := hg.leading
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h
  exact ⟨_, mem_eisensteinGraph.mpr ⟨g.natDegree, ⟨hd, le_rfl⟩, hunit.ne_zero, le_rfl, rfl⟩⟩

end Atlas.Knowledge
