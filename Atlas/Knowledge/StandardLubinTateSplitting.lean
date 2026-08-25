import Mathlib
import Atlas.Knowledge.IntegerHigherUnitCount
import Atlas.Knowledge.StandardLubinTateTorsion

/-!
# standard Lubin–Tate splitting

The primitive polynomial splits over the integers of the carrier extension: at a
primitive root, the unit-parameter orbit provides as many distinct integral roots as the
degree — the roots multiset is full. Distinctness is the scalar congruence of
`Atlas.Knowledge.StandardLubinTateTorsion` read through the multiplicative–additive
bridge of `Atlas.Knowledge.IntegerHigherUnitGroup`, and the count is
`Atlas.Knowledge.integerHigherUnitCount` against the degree. This is the first step of
the analytic direction of the norm computation: the changed-uniformizer argument ahead
finds its roots inside this splitting.

## Main statements

* `standardLubinTateSplitting` — the roots multiset over `𝒪[E]` has full cardinality;
  proved.

## Implementation notes

The statement counts the roots multiset over the integer ring — a domain, so the
multiset is well-behaved — rather than asserting `Polynomial.Splits`, which lives over a
field; the level consumer can read either form off the cardinality. The injection is
indexed by the unit-parameter quotient through `Quotient.out`, so no system of
representatives is chosen by hand, and both bounds meet at the degree by `omega`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

section Splitting

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [Algebra K E]
  [ValuativeExtension K E] [FiniteDimensional K E] [IsMixedCharLocalField E]

omit [FiniteDimensional K E] in
/-- **The primitive polynomial splits over the integers of the carrier**: at a primitive
root, the unit-parameter orbit provides as many distinct integral roots as the degree
([Milne 2020, Chap. I, §3, the proof of Thm. 3.6, p.39][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/HigherUnitLevelEquiv.lean:55`][Yamaguchi2026]). -/
theorem standardLubinTateSplitting {π : 𝒪[K]} (hπ : Irreducible π) {n : ℕ}
    {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E])
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0) :
    ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map
        (algebraMap ↥𝒪[K] ↥𝒪[E])).roots.card =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
  classical
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
  omega

end Splitting

end Atlas.Knowledge
