import Mathlib
import Atlas.Knowledge.IntegerHigherUnitCount
import Atlas.Knowledge.StandardLubinTateDisplacement
import Atlas.Knowledge.StandardLubinTateSplitting

/-!
# standard Lubin–Tate conjugate ceiling

Every root of the mapped primitive polynomial is a unit-scalar orbit point of a
primitive root, and any root other than the root itself sits at value at most
`qⁿ ν(x)` — the conjugate ceiling that the Krasner gap `qⁿ⁺¹ ν(x)` of
`Atlas.Knowledge.standardLubinTateRootProximity_lt` strictly beats. Surjectivity onto
the roots is the splitting count read backwards: the class-indexed injection of
`Atlas.Knowledge.standardLubinTateSplitting` lands in a finite set of the same
cardinality. The ceiling then reads each non-trivial orbit displacement off the
spectrum of `Atlas.Knowledge.integerValuation_standardLubinTateSMul_sub_self`, the
scalar's depth being at most `n` precisely because a deeper scalar acts trivially.

## Main statements

* `exists_unit_smul_of_mem_roots` — every root is an orbit point; proved.
* `integerValuation_sub_le_of_mem_roots` — the conjugate ceiling `qⁿ ν(x)`; proved.

## Implementation notes

The orbit statement quantifies over plain units and the ceiling over roots — no Galois
group appears: the source states the ceiling for automorphisms of the level field, and
the Krasner consumer here will convert an automorphism image into a root first
(`Atlas.Knowledge.eval₂_algEquiv`-style) and then into an orbit point, so the
root-level form is the one that composes. The depth extraction is the DVR normal form
`v − 1 = πʲ w` of the displacement item, with `j ≤ n` forced by the annihilator: a
scalar of deeper distance from one fixes the root by
`Atlas.Knowledge.standardLubinTateSMul_eq_iff`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section Ceiling

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [Algebra K E]
  [ValuativeExtension K E] [IsMixedCharLocalField E]
variable {π : ↥𝒪[K]} (hπ : Irreducible π) {n : ℕ} {x : ↥𝒪[E]}

include hπ in
/-- **Every root is an orbit point**: the roots of the mapped primitive polynomial are
exactly the unit-scalar orbit of a primitive root — the injection of the splitting
count, forced surjective by the equal cardinalities
([Milne 2020, Chap. I, §3, the proof of Thm. 3.6 (a),(b), pp.38–39][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/HigherUnitLevelEquiv.lean:55`][Yamaguchi2026]
— the source's root embedding, whose cardinality argument is the same squeeze). -/
theorem exists_unit_smul_of_mem_roots
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    {r : ↥𝒪[E]}
    (hr : r ∈ ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
      (algebraMap ↥𝒪[K] ↥𝒪[E])).roots) :
    ∃ v : (↥𝒪[K])ˣ, r = lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑v) x := by
  classical
  have hx : x ∈ 𝓂[E] := mem_maximalIdeal_of_aeval_primitive K E hπ hroot
  set p := (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
    (algebraMap ↥𝒪[K] ↥𝒪[E]) with hp
  have hmonic : p.Monic :=
    (standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n).map _
  have hcard := (standardLubinTateSplitting K E hπ hroot).1
  have hnodup := (standardLubinTateSplitting K E hπ hroot).2
  -- the orbit map into the root finset, as in the splitting item
  have horbit : ∀ u : (↥𝒪[K])ˣ,
      lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑u) x ∈ p.roots := by
    intro u
    rw [Polynomial.mem_roots hmonic.ne_zero, Polynomial.IsRoot, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    exact standardLubinTateSMul_isRoot K E hπ hx hroot u
  set f : (↥𝒪[K])ˣ ⧸ integerHigherUnitGroup K (n + 1) → {z // z ∈ p.roots.toFinset} :=
    fun c => ⟨lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑c.out) x,
      Multiset.mem_toFinset.mpr (horbit c.out)⟩ with hf
  have hinj : Function.Injective f := by
    intro c d h
    have heq : lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑c.out) x =
        lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑d.out) x :=
      Subtype.mk_eq_mk.mp h
    have hsub := (standardLubinTateSMul_eq_iff K E hπ hx hroot
      (↑c.out) (↑d.out)).mp heq
    have hdiv := (sub_mem_iff_div_mem_integerHigherUnitGroup K (n + 1)
      c.out d.out).mp hsub
    calc c = ⟦c.out⟧ := c.out_eq.symm
      _ = ⟦d.out⟧ := (QuotientGroup.eq).mpr hdiv
      _ = d := d.out_eq
  -- equal cardinalities force surjectivity
  haveI : Finite ((↥𝒪[K])ˣ ⧸ integerHigherUnitGroup K (n + 1)) :=
    finite_integerHigherUnitGroup_quotient K (n + 1)
  haveI : Fintype ((↥𝒪[K])ˣ ⧸ integerHigherUnitGroup K (n + 1)) := Fintype.ofFinite _
  have hcards : Fintype.card ((↥𝒪[K])ˣ ⧸ integerHigherUnitGroup K (n + 1)) =
      Fintype.card {z // z ∈ p.roots.toFinset} := by
    rw [Fintype.card_coe]
    have h1 : p.roots.toFinset.card = Multiset.card p.roots :=
      Multiset.toFinset_card_eq_card_iff_nodup.mpr hnodup
    rw [h1, hcard, ← Nat.card_eq_fintype_card]
    have h2 := integerHigherUnitCount K (n + 1) (Nat.succ_ne_zero n)
    simpa using h2
  have hsurj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcards⟩ |>.2
  obtain ⟨c, hc⟩ := hsurj ⟨r, Multiset.mem_toFinset.mpr hr⟩
  exact ⟨c.out, (congrArg Subtype.val hc).symm⟩

include hπ in
/-- **The conjugate ceiling**: any other root of the primitive polynomial sits at value
at most `qⁿ ν(x)` from a primitive root — the bound the Krasner gap strictly beats
([Milne 2020, Chap. I, §3, the proof of Thm. 3.6 (b), p.39][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/PrimitiveDisplacement.lean:905`][Yamaguchi2026]
— the source's Galois form; the orbit form here needs no automorphism). -/
theorem integerValuation_sub_le_of_mem_roots
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    {r : ↥𝒪[E]}
    (hr : r ∈ ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
      (algebraMap ↥𝒪[K] ↥𝒪[E])).roots)
    (hne : r ≠ x) :
    integerValuation E (x - r) ≤ (Nat.card 𝓀[K] : ℤ) ^ n * integerValuation E x := by
  have hx : x ∈ 𝓂[E] := mem_maximalIdeal_of_aeval_primitive K E hπ hroot
  obtain ⟨v, rfl⟩ := exists_unit_smul_of_mem_roots K E hπ hroot hr
  -- the scalar's distance from one is a positive depth `j`; `j ≤ n` since `r ≠ x`
  have hvne : (v : ↥𝒪[K]) - 1 ≠ 0 := by
    intro h0
    refine hne ?_
    have hv1 : (v : ↥𝒪[K]) = 1 := by linear_combination h0
    rw [hv1, lubinTateSMul_one]
  obtain ⟨j, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hvne hπ
  have hju : (v : ↥𝒪[K]) - 1 = π ^ j * (w : ↥𝒪[K]) := by
    rw [hw]
    ring
  have hjn : j ≤ n := by
    by_contra hgt
    refine hne ?_
    have hmem : (v : ↥𝒪[K]) - 1 ∈ (𝓂[K] ^ (n + 1) : Ideal ↥𝒪[K]) := by
      rw [hju, (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact Dvd.dvd.mul_right (pow_dvd_pow π (by omega)) _
    have heq := (standardLubinTateSMul_eq_iff K E hπ hx hroot (↑v) 1).mpr
      (by simpa using hmem)
    rw [heq, lubinTateSMul_one]
  -- the displacement spectrum
  have hspec := integerValuation_standardLubinTateSMul_sub_self K E hπ hx hroot
    hjn w.isUnit hju
  have hneg : integerValuation E
      (x - lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑v) x) =
      integerValuation E
        (lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑v) x - x) := by
    rw [show x - lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑v) x =
      -(lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑v) x - x) by ring,
      integerValuation_neg]
  rw [hneg, hspec]
  have hq : (2 : ℤ) ≤ (Nat.card 𝓀[K] : ℤ) := by
    exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[K])
  have hxnn := integerValuation_nonneg E x
  have hpow : (Nat.card 𝓀[K] : ℤ) ^ j ≤ (Nat.card 𝓀[K] : ℤ) ^ n :=
    pow_le_pow_right₀ (by omega) hjn
  exact mul_le_mul_of_nonneg_right hpow hxnn

end Ceiling

end Atlas.Knowledge
