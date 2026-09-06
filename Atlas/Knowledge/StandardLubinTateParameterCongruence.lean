import Mathlib
import Atlas.Knowledge.IntegerHigherUnitGroup
import Atlas.Knowledge.IntegerIsIntegralClosure
import Atlas.Knowledge.StandardLubinTatePolynomial

/-!
# standard Lubin–Tate parameter congruence

The standard polynomial depends polynomially on its parameter, so the difference of two
parameters divides the difference of the two primitive evaluations — at any point of any
carrier. Specialized to a deep unit change: at a `π`-primitive root, a unit `u` of depth
`n + 1` puts the changed evaluation into divisibility by `π^{n + 2}`, the evaluation
depth the root-product comparison ahead consumes. The congruence is proved by passing to
the quotient by the principal ideal the parameter difference spans, where the two
parameters agree and the whole construction — polynomial, iterates, primitive quotient —
collapses to one.

## Main statements

* `sub_dvd_aeval_standardLubinTatePrimitivePolynomial_sub` — `(π′ − π) ∣ Φ_{π′}(x) −
  Φ_π(x)`; proved.
* `pow_dvd_aeval_changed_standardLubinTatePrimitivePolynomial` — at a `π`-primitive
  root, `u ∈ U^{(n+1)}` gives `π^{n+2} ∣ Φ_{πu}(x)`; proved.

## Implementation notes

The exports are divisibility statements, not valuation bounds: `ν(Φ_{πu}(x)) ≥
(n + 2) ν(π)` is false at the junk value when the changed evaluation happens to vanish,
and the consumer that knows nonvanishing recovers the bound from the divisibility
through `Atlas.Knowledge.integerValuation_mul` and nonnegativity. The source's
`ℕ∞`-valued order junks to `⊤`, where the bound survives vacuously; the `ℤ` carrier
does not, which is what forces the design. The source states the depth in its
completed valuation vocabulary and keeps the congruence over an arbitrary
ideal; here the ideal is the principal one the DVR provides, so the depth is a
divisibility by `π^{n+2}` and no ideal-membership plumbing survives to the statement.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section Congruence

variable {A : Type*} [CommRing A] [IsLocalRing A]
variable {R : Type*} [CommRing R] (g : A →+* R)

/-- Equal parameters give equal mapped standard polynomials. -/
private theorem map_standardLubinTatePolynomial_eq {π π' : A} (h : g π = g π') :
    (standardLubinTatePolynomial A π).map g = (standardLubinTatePolynomial A π').map g := by
  simp only [standardLubinTatePolynomial, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, h]

/-- Equal parameters give equal mapped iterates. -/
private theorem map_standardLubinTatePolynomialIterate_eq {π π' : A} (h : g π = g π')
    (m : ℕ) :
    (standardLubinTatePolynomialIterate A π m).map g =
      (standardLubinTatePolynomialIterate A π' m).map g := by
  induction m with
  | zero => simp [standardLubinTatePolynomialIterate_zero]
  | succ m ih =>
    rw [standardLubinTatePolynomialIterate_succ, standardLubinTatePolynomialIterate_succ,
      Polynomial.map_comp, Polynomial.map_comp, ih,
      map_standardLubinTatePolynomial_eq g h]

/-- Equal parameters give equal mapped primitive polynomials. -/
private theorem map_standardLubinTatePrimitivePolynomial_eq {π π' : A} (h : g π = g π')
    (m : ℕ) :
    (standardLubinTatePrimitivePolynomial A π m).map g =
      (standardLubinTatePrimitivePolynomial A π' m).map g := by
  simp only [standardLubinTatePrimitivePolynomial, Polynomial.map_add,
    Polynomial.map_pow, Polynomial.map_C, h,
    map_standardLubinTatePolynomialIterate_eq g h m]

end Congruence

section Evaluation

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [Algebra K E]
  [ValuativeExtension K E] [IsMixedCharLocalField E]

omit [TopologicalSpace E] [IsMixedCharLocalField E] in
/-- **The parameter congruence**: the difference of the two parameters divides the
difference of the two primitive evaluations (Yamaguchi 2026,
`LubinTate/FiniteLevel/ParameterCongruence.lean:97` — the source states membership
in an arbitrary ideal; the principal case is this statement). -/
theorem sub_dvd_aeval_standardLubinTatePrimitivePolynomial_sub
    (π π' : ↥𝒪[K]) (n : ℕ) (x : ↥𝒪[E]) :
    algebraMap ↥𝒪[K] ↥𝒪[E] (π' - π) ∣
      (Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π' n) -
        Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n)) := by
  set I : Ideal ↥𝒪[E] := Ideal.span {algebraMap ↥𝒪[K] ↥𝒪[E] (π' - π)}
  rw [← Ideal.mem_span_singleton]
  set g : ↥𝒪[K] →+* ↥𝒪[E] ⧸ I :=
    (Ideal.Quotient.mk I).comp (algebraMap ↥𝒪[K] ↥𝒪[E]) with hg
  have hparam : g π' = g π := by
    simp only [hg, RingHom.comp_apply]
    rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
    exact Ideal.subset_span rfl
  have heval : Ideal.Quotient.mk I
      (Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π' n)) =
      Ideal.Quotient.mk I
        (Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n)) := by
    have h1 : ∀ ϖ : ↥𝒪[K], Ideal.Quotient.mk I
        (Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] ϖ n)) =
        Polynomial.eval₂ g (Ideal.Quotient.mk I x)
          (standardLubinTatePrimitivePolynomial ↥𝒪[K] ϖ n) := by
      intro ϖ
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
    rw [h1, h1]
    rw [Polynomial.eval₂_eq_eval_map, Polynomial.eval₂_eq_eval_map,
      map_standardLubinTatePrimitivePolynomial_eq g hparam n]
  rwa [Ideal.Quotient.mk_eq_mk_iff_sub_mem] at heval

omit [TopologicalSpace E] [IsMixedCharLocalField E] in
/-- **The changed-uniformizer evaluation depth**: at a `π`-primitive root, a unit
change of depth `n + 1` evaluates the changed primitive polynomial into
`π^{n + 2} 𝒪[E]` ([Milne 2020, Chap. I, §3, the proof of Thm. 3.6 (a), p.38][MilneCFT]
— the tower recursion `f(π_n) = π_{n−1}` that a changed uniformizer perturbs; Milne's own
independence-of-`π` argument is Thm. 3.9 and Prop. 3.10, pp.40–41, and runs through a
formal-group isomorphism over `K^un`'s completion rather than through this congruence;
Yamaguchi 2026, `LubinTate/FiniteLevel/ChangedPrimitiveEvaluation.lean:46` and `:114`). -/
theorem pow_dvd_aeval_changed_standardLubinTatePrimitivePolynomial
    {π : ↥𝒪[K]} (hπ : Irreducible π) {n : ℕ} {x : ↥𝒪[E]}
    (hroot : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0)
    {u : (↥𝒪[K])ˣ} (hu : u ∈ integerHigherUnitGroup K (n + 1)) :
    algebraMap ↥𝒪[K] ↥𝒪[E] (π ^ (n + 2)) ∣
      Polynomial.aeval x
        (standardLubinTatePrimitivePolynomial ↥𝒪[K] (π * (u : ↥𝒪[K])) n) := by
  -- the parameter difference is divisible by `π^{n+2}`
  have hmem : (u : ↥𝒪[K]) - 1 ∈
      IsLocalRing.maximalIdeal ↥𝒪[K] ^ (n + 1) := hu
  have hspan : IsLocalRing.maximalIdeal ↥𝒪[K] ^ (n + 1) =
      Ideal.span {π ^ (n + 1)} := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ,
      Ideal.span_singleton_pow]
  rw [hspan, Ideal.mem_span_singleton] at hmem
  obtain ⟨c, hc⟩ := hmem
  have hdiff : π * (u : ↥𝒪[K]) - π = π ^ (n + 2) * c := by
    calc π * (u : ↥𝒪[K]) - π = π * ((u : ↥𝒪[K]) - 1) := by ring
      _ = π * (π ^ (n + 1) * c) := by rw [hc]
      _ = π ^ (n + 2) * c := by ring
  have hdvd := sub_dvd_aeval_standardLubinTatePrimitivePolynomial_sub K E
    π (π * (u : ↥𝒪[K])) n x
  rw [hroot, sub_zero, hdiff, map_mul] at hdvd
  exact dvd_trans ⟨algebraMap ↥𝒪[K] ↥𝒪[E] c, rfl⟩ hdvd

end Evaluation

end Atlas.Knowledge
