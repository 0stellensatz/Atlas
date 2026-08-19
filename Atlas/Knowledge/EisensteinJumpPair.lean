import Mathlib
import Atlas.Knowledge.EisensteinGraph
import Atlas.Knowledge.JumpSetExtremal
import Atlas.Knowledge.ShiftRhoP
import Atlas.Knowledge.ShiftT

/-!
# jump pair of an Eisenstein polynomial

The pair `(I_g, β_g)` the source attaches to an Eisenstein polynomial: the `≤_ρ`-minimal points
of the coefficient graph `Atlas.Knowledge.eisensteinGraph`, along the shift
`Atlas.Knowledge.ShiftRhoP` at a prime `p`—in the source's application, the residue
characteristic of the base field. As with `Atlas.Knowledge.filtOrd`, the recipe is taken as
the *definition*, which makes it total; the source's assertion that it lands on a jump pair is
here a proved theorem, in two stages. The
antichain structure is generic—minimal points of any finite graph form a jump pair over
unconstrained levels. That the levels then land in `T_ρ` is the Eisenstein arithmetic: a
minimal point below the top multiplicity has level prime to `p` because the `p`-part of its
index is exact in its weight, and at the top multiplicity every point other than the leading
one is dominated by it—the leading monomial has the smallest weight in that stratum, its
coefficient being a unit while Eisenstein coefficients are not. The identification of this
pair with the field-side invariant of `Atlas.Knowledge.UnitFiltrationClassification` is the
content of the source's Theorem 1.11, the claim of `Atlas.Knowledge.EisensteinFieldInvariant`.

## Main definitions

* `eisensteinJumpPair` — the minimal points of the coefficient graph.

## Main statements

* `isJumpPair_univ_eisensteinJumpPair` — the generic half: minimal points form a jump pair
  over unconstrained levels. Proved.
* `isJumpPair_eisensteinJumpPair` — on an Eisenstein polynomial the pair is a jump pair over
  `T_ρ`, the source's `(I_g, β_g) ∈ Jump_{ρ_{∞, p}}`. Proved.

## Implementation notes

The source states the landing as the existence of a unique pair whose graph is the minimal-point
set; with the recipe as definition the graph *is* the minimal-point set, and what remains—the
minimal points satisfy the jump-pair conditions over `T_ρ`—is the theorem. Primality of `p`
enters only there, through the exactness of `p`-parts; the definition itself is stated at any
`1 < p`, and nothing ties `p` to `R`—in the source's application `p` is the residue
characteristic of the base, but the arithmetic holds at any prime over any discrete valuation
ring. The source's `Eis_d (K)` is monic by definition; the landing theorem does not hypothesize
monicity, because the one thing the top-multiplicity domination consumes—the leading
coefficient being a unit—is already the `leading` field of `Polynomial.IsEisensteinAt`.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The **jump pair of an Eisenstein polynomial**: the `≤_ρ`-minimal points of its coefficient
graph along the shift `ρ_p`—the source's `(I_{g(x)}, β_{g(x)})`, carried as its graph, with the
recipe taken as the definition ([Pagano 2022, §1.2.1, p.408][Pagano2022]). -/
noncomputable def eisensteinJumpPair (p : ℕ+) (hp : 1 < p) (g : Polynomial R) :
    Finset (ℕ+ × ℕ+) :=
  jumpMin (ρ_p p hp) (eisensteinGraph (p : ℕ) g)

/-- The generic half of the landing: the minimal points of the coefficient graph form a jump
pair over unconstrained levels, by the antichain structure alone
([Pagano 2022, §1.2.1, p.408][Pagano2022]). -/
theorem isJumpPair_univ_eisensteinJumpPair (p : ℕ+) (hp : 1 < p) (g : Polynomial R) :
    IsJumpPair (ρ_p p hp) Set.univ (eisensteinJumpPair p hp g) :=
  isJumpPair_jumpMin _ fun _ _ => Set.mem_univ _

private theorem one_le_addVal_toNat {x : R} (hx : x ∈ IsLocalRing.maximalIdeal R)
    (hx0 : x ≠ 0) : 1 ≤ ((addVal R) x).toNat := by
  have hunit : ¬IsUnit x := mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx)
  have h0 : (addVal R) x ≠ 0 := fun h => hunit (addVal_eq_zero_iff.mp h)
  have htop : (addVal R) x ≠ ⊤ := fun h => hx0 (addVal_eq_top_iff.mp h)
  lift (addVal R) x to ℕ using htop with m hm
  simpa using Nat.one_le_iff_ne_zero.mpr (fun h => h0 (by simp [h]))

private theorem not_dvd_level {p n i v : ℕ} (hpp : p.Prime) (hi : i ≠ 0)
    (hlt : padicValNat p i < padicValNat p n) :
    ¬ p ∣ (n * v + i) / p ^ padicValNat p i := by
  set k := padicValNat p i with hk
  have hdi : p ^ k ∣ i := pow_padicValNat_dvd
  have hdn : p ^ (k + 1) ∣ n := dvd_trans (pow_dvd_pow p hlt) pow_padicValNat_dvd
  rw [Nat.add_div_of_dvd_left hdi]
  intro hdvd
  have h2 : ¬ p ∣ i / p ^ k := by
    have := Nat.not_dvd_ordCompl hpp hi
    rwa [Nat.factorization_def i hpp] at this
  have h1 : p ∣ n * v / p ^ k := by
    obtain ⟨t, ht⟩ := hdn
    refine ⟨t * v, ?_⟩
    rw [ht, pow_succ, mul_assoc, mul_assoc, Nat.mul_div_cancel_left _ (pow_pos hpp.pos k),
      ← mul_assoc, mul_comm p t, mul_assoc]
  exact h2 ((Nat.dvd_add_right h1).mp hdvd)

/-- On an Eisenstein polynomial the recipe lands: the pair is a jump pair over `T_ρ`—the
source's `(I_{g(x)}, β_{g(x)}) ∈ Jump_{ρ_{∞, p}}`. Below the top multiplicity a minimal
point's level is prime to `p` since the `p`-part of its index divides its weight exactly one
level deep; at the top multiplicity the leading point dominates every other, its weight being
least in the stratum ([Pagano 2022, §1.2.1, p.408][Pagano2022]). -/
theorem isJumpPair_eisensteinJumpPair (p : ℕ+) (hp : 1 < p) (hpp : (p : ℕ).Prime)
    {g : Polynomial R} (hg : g.IsEisensteinAt (IsLocalRing.maximalIdeal R)) :
    IsJumpPair (ρ_p p hp) (Shift.T (ρ_p p hp)) (eisensteinJumpPair p hp g) := by
  have hunit : IsUnit (g.coeff g.natDegree) := by
    have h := hg.leading
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at h
  have huniv := isJumpPair_univ_eisensteinJumpPair p hp g
  refine ⟨huniv.1, ?_, huniv.2.2.1, huniv.2.2.2⟩
  intro q hq
  have hqG : q ∈ eisensteinGraph (p : ℕ) g := (Finset.mem_filter.mp hq).1
  have hqmin := (Finset.mem_filter.mp hq).2
  obtain ⟨i, ⟨hi1, hin⟩, hci, hki, hq_eq⟩ := mem_eisensteinGraph.mp hqG
  have hi0 : i ≠ 0 := Nat.one_le_iff_ne_zero.mp hi1
  have hn0 : g.natDegree ≠ 0 := Nat.one_le_iff_ne_zero.mp (hi1.trans hin)
  have hq1pos : 0 < (g.natDegree * ((addVal R) (g.coeff i)).toNat + i) /
      (p : ℕ) ^ padicValNat (p : ℕ) i :=
    (Nat.one_le_div_iff (pow_pos hpp.pos _)).mpr
      ((Nat.le_of_dvd hi1 pow_padicValNat_dvd).trans (Nat.le_add_left i _))
  have hq1coe : (q.1 : ℕ) = (g.natDegree * ((addVal R) (g.coeff i)).toNat + i) /
      (p : ℕ) ^ padicValNat (p : ℕ) i := by
    rw [hq_eq, Nat.toPNat'_coe, if_pos hq1pos]
  have hT : ¬ (p : ℕ) ∣ (q.1 : ℕ) → q.1 ∈ Shift.T (ρ_p p hp) := by
    intro hnd
    refine ⟨Set.mem_univ _, ?_⟩
    rintro ⟨j, -, hj⟩
    exact hnd ⟨(j : ℕ), by rw [← hj]; exact PNat.mul_coe p j⟩
  rcases lt_or_eq_of_le hki with hlt | heq
  · exact hT (hq1coe ▸ not_dvd_level hpp hi0 hlt)
  · by_cases hii : i = g.natDegree
    · refine hT ?_
      have hv0 : ((addVal R) (g.coeff i)).toNat = 0 := by
        rw [hii, addVal_eq_zero_iff.mpr hunit]
        rfl
      rw [hq1coe, hv0, mul_zero, zero_add]
      have := Nat.not_dvd_ordCompl hpp hi0
      rwa [Nat.factorization_def i hpp] at this
    · exfalso
      have hilt : i < g.natDegree := lt_of_le_of_ne hin hii
      have hv1 : 1 ≤ ((addVal R) (g.coeff i)).toNat := one_le_addVal_toNat (hg.mem hilt) hci
      have hcn : g.coeff g.natDegree ≠ 0 := hunit.ne_zero
      have hvn0 : ((addVal R) (g.coeff g.natDegree)).toNat = 0 := by
        rw [addVal_eq_zero_iff.mpr hunit]
        rfl
      set ptn : ℕ+ × ℕ+ :=
        (((g.natDegree * ((addVal R) (g.coeff g.natDegree)).toNat + g.natDegree) /
            (p : ℕ) ^ padicValNat (p : ℕ) g.natDegree).toPNat',
          ⟨padicValNat (p : ℕ) g.natDegree + 1, Nat.succ_pos _⟩) with hptn
      have hnG : ptn ∈ eisensteinGraph (p : ℕ) g :=
        mem_eisensteinGraph.mpr
          ⟨g.natDegree, ⟨Nat.one_le_iff_ne_zero.mpr hn0, le_rfl⟩, hcn, le_rfl, rfl⟩
      have hptn_pos : 0 < (g.natDegree * ((addVal R) (g.coeff g.natDegree)).toNat +
          g.natDegree) / (p : ℕ) ^ padicValNat (p : ℕ) g.natDegree :=
        (Nat.one_le_div_iff (pow_pos hpp.pos _)).mpr
          ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) pow_padicValNat_dvd).trans
            (Nat.le_add_left _ _))
      have hptn_coe : (ptn.1 : ℕ) =
          g.natDegree / (p : ℕ) ^ padicValNat (p : ℕ) g.natDegree := by
        rw [hptn, Nat.toPNat'_coe, if_pos hptn_pos, hvn0, mul_zero, zero_add]
      have hdvd_w : (p : ℕ) ^ padicValNat (p : ℕ) g.natDegree ∣
          g.natDegree * ((addVal R) (g.coeff i)).toNat + i := by
        refine dvd_add (dvd_mul_of_dvd_left pow_padicValNat_dvd _) ?_
        rw [← heq]
        exact pow_padicValNat_dvd
      have hlev_lt : g.natDegree / (p : ℕ) ^ padicValNat (p : ℕ) g.natDegree <
          (g.natDegree * ((addVal R) (g.coeff i)).toNat + i) /
            (p : ℕ) ^ padicValNat (p : ℕ) g.natDegree :=
        Nat.div_lt_div_of_lt_of_dvd hdvd_w
          (lt_of_le_of_lt (Nat.le_mul_of_pos_right _ hv1) (Nat.lt_add_of_pos_right hi1))
      have hmult : ptn.2 = q.2 := by
        rw [hptn, hq_eq]
        exact Subtype.ext (by simp [heq])
      have hord : JumpOrder (ρ_p p hp) ptn q := by
        refine ⟨le_of_eq hmult, ?_⟩
        rw [hmult, ρ_p_iterate, ρ_p_iterate]
        rw [← PNat.coe_le_coe, PNat.mul_coe, PNat.mul_coe]
        refine Nat.mul_le_mul_left _ ?_
        rw [hptn_coe, hq1coe, heq]
        exact le_of_lt hlev_lt
      have hcontra := hqmin ptn hnG hord
      have hcoe : (ptn.1 : ℕ) = (q.1 : ℕ) := by rw [hcontra]
      rw [hptn_coe, hq1coe, heq] at hcoe
      exact absurd hcoe (Nat.ne_of_lt hlev_lt)

end Atlas.Knowledge
