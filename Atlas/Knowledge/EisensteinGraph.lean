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

## Implementation notes

The source's constraint is `v_p (i) ≤ v_p (e)` for `e` the ramification index of the field the
polynomial cuts out, which is the degree times the ramification index `p - 1` of the source's
base field; the last factor is prime to `p`, so the constraint is spelled against the degree
and no field enters the definition. The same arithmetic makes the division exact: the `p`-part
of the index divides the index and, through the constraint, the degree, hence the whole
weight. The definition is total—any polynomial over a discrete valuation ring is accepted, and
the division truncates and `Nat.toPNat'` junks to `1` where the reading is not the source's;
the statements about the graph hypothesize Eisenstein, where no junk arises. The valuation of
a coefficient is read through `IsDiscreteValuationRing.addVal`, whose `⊤` at a zero
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

end Atlas.Knowledge
