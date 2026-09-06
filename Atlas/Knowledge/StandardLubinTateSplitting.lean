import Mathlib
import Atlas.Knowledge.IntegerHigherUnitCount
import Atlas.Knowledge.StandardLubinTateTorsion

/-!
# standard Lubin–Tate splitting

The primitive polynomial splits over the integers of the carrier extension: at a
primitive root, the unit-parameter orbit provides as many distinct integral roots as the
degree — the roots multiset is full and has no repetition. Distinctness is the scalar
congruence of `Atlas.Knowledge.StandardLubinTateTorsion` read through the
multiplicative–additive bridge of `Atlas.Knowledge.IntegerHigherUnitGroup`, and the
count is `Atlas.Knowledge.integerHigherUnitCount` against the degree. This is the first
step of the analytic direction of the norm computation: the changed-uniformizer argument
ahead finds its roots inside this splitting.

## Main statements

* `standardLubinTateSplitting` — the roots multiset over `𝒪[E]` has full cardinality
  and no duplicate; proved.
* `standardLubinTatePrimitivePolynomial_map_splits` — the same fact in Mathlib's
  `Polynomial.Splits` form; proved.
* `exists_unit_lubinTateSMul_of_mem_roots` — every root is an orbit point: the
  injection read backwards; proved.

## Implementation notes

The counting form is the engine — the cardinality is what the index computation of the
norm subgroup consumes — and `Polynomial.Splits`, a one-argument predicate over any
semiring whose `Polynomial.splits_iff_card_roots` characterization holds over the
integer domain, is one `iff` away; the corollary records that reading, which is also the
counterpart source's spelling. Distinctness rides along as `Multiset.Nodup` because the
injection pins the deduplicated count as well, and a `Finset` phrasing would demand a
`DecidableEq` the statement should not carry. The injection is indexed by the
unit-parameter quotient through `Quotient.out`, so no system of representatives is
chosen by hand, and all bounds meet at the degree by `omega`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

section Splitting

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [Algebra K E]
  [ValuativeExtension K E] [IsMixedCharLocalField E]

/-- **The primitive polynomial splits over the integers of the carrier**: at a primitive
root, the unit-parameter orbit provides as many distinct integral roots as the degree —
the roots multiset is full and duplicate-free
([Milne 2020, Chap. I, §3, the proof of Thm. 3.6 (a), (b), p.39][MilneCFT];
Yamaguchi 2026, `LubinTate/FiniteLevel/HigherUnitLevelEquiv.lean:55`). -/
theorem standardLubinTateSplitting {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ}
    {x : ↥𝒪[E]}
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0) :
    ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
        (algebraMap ↥𝒪[K] ↥𝒪[E])).roots.card =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n ∧
    ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
        (algebraMap ↥𝒪[K] ↥𝒪[E])).roots.Nodup := by
  classical
  have hx : x ∈ 𝓂[E] := mem_maximalIdeal_of_aeval_primitive K E hπ hroot
  have hmonic : ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
      (algebraMap ↥𝒪[K] ↥𝒪[E])).Monic :=
    (standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n).map _
  have hdeg : ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
      (algebraMap ↥𝒪[K] ↥𝒪[E])).natDegree =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
    rw [(standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n).natDegree_map,
      standardLubinTatePrimitivePolynomial_natDegree]
  -- every orbit point is a root
  have horbit : ∀ u : 𝒪[K]ˣ,
      lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑u) x ∈
        ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
          (algebraMap ↥𝒪[K] ↥𝒪[E])).roots := by
    intro u
    rw [Polynomial.mem_roots hmonic.ne_zero, Polynomial.IsRoot, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    exact standardLubinTateSMul_isRoot K E hπ hx hroot u
  -- the class-indexed injection into the roots
  have hinj : Function.Injective
      (fun c : 𝒪[K]ˣ ⧸ integerHigherUnitGroup K (n + 1) =>
        (⟨lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑c.out) x,
          Multiset.mem_toFinset.mpr (horbit c.out)⟩ :
          ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
            (algebraMap ↥𝒪[K] ↥𝒪[E])).roots.toFinset)) := by
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
  have hcardQ : Nat.card (𝒪[K]ˣ ⧸ integerHigherUnitGroup K (n + 1)) =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
    have := integerHigherUnitCount K (n + 1) (Nat.succ_ne_zero n)
    simpa using this
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [hcardQ, Nat.card_eq_finsetCard] at hle
  have htf := Multiset.toFinset_card_le
    ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
      (algebraMap ↥𝒪[K] ↥𝒪[E])).roots
  have hub := Polynomial.card_roots'
    ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
      (algebraMap ↥𝒪[K] ↥𝒪[E]))
  refine ⟨by omega, ?_⟩
  set r := ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
    (algebraMap ↥𝒪[K] ↥𝒪[E])).roots with hr
  have hdd : r.toFinset.card = Multiset.card r.dedup := rfl
  exact Multiset.dedup_eq_self.mp
    (Multiset.eq_of_le_of_card_le (Multiset.dedup_le r) (by omega))

/-- **The splitting in Mathlib's predicate form**: over the integers of the carrier the
mapped primitive polynomial satisfies `Polynomial.Splits` — the counterpart source's
spelling, read off the cardinality (Yamaguchi 2026,
`LubinTate/FiniteLevel/HigherUnitLevelEquiv.lean:55`). -/
theorem standardLubinTatePrimitivePolynomial_map_splits {π : 𝒪[K]} (hπ : Irreducible π)
    {n : ℕ} {x : ↥𝒪[E]}
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0) :
    ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
        (algebraMap ↥𝒪[K] ↥𝒪[E])).Splits :=
  Polynomial.splits_iff_card_roots.mpr <| by
    rw [(standardLubinTateSplitting K E hπ hroot).1,
      (standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n).natDegree_map,
      standardLubinTatePrimitivePolynomial_natDegree]

/-- **Every root is an orbit point**: the roots of the mapped primitive polynomial are
exactly the unit-scalar orbit of a primitive root — the class-indexed injection of the
splitting count, forced surjective by the equal cardinalities
([Milne 2020, Chap. I, §3, Prop. 3.4, p.38][MilneCFT] — the module structure of the
root set; Yamaguchi 2026, `LubinTate/FiniteLevel/HigherUnitLevelEquiv.lean:55`). -/
theorem exists_unit_lubinTateSMul_of_mem_roots {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ}
    {x : ↥𝒪[E]}
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    {r : ↥𝒪[E]}
    (hr : r ∈ ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
      (algebraMap ↥𝒪[K] ↥𝒪[E])).roots) :
    ∃ v : (↥𝒪[K])ˣ, r = lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑v) x := by
  classical
  have hx : x ∈ 𝓂[E] := mem_maximalIdeal_of_aeval_primitive K E hπ hroot
  set p := (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
    (algebraMap ↥𝒪[K] ↥𝒪[E])
  have hmonic : p.Monic :=
    (standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n).map _
  have hcard := (standardLubinTateSplitting K E hπ hroot).1
  have hnodup := (standardLubinTateSplitting K E hπ hroot).2
  have horbit : ∀ u : (↥𝒪[K])ˣ,
      lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑u) x ∈ p.roots := by
    intro u
    rw [Polynomial.mem_roots hmonic.ne_zero, Polynomial.IsRoot, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    exact standardLubinTateSMul_isRoot K E hπ hx hroot u
  set f : (↥𝒪[K])ˣ ⧸ integerHigherUnitGroup K (n + 1) → {z // z ∈ p.roots.toFinset} :=
    fun c => ⟨lubinTateSMul K E hπ (standardLubinTateSeries hπ) (↑c.out) x,
      Multiset.mem_toFinset.mpr (horbit c.out)⟩
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

end Splitting

end Atlas.Knowledge
