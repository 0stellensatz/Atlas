import Mathlib
import Atlas.Knowledge.IntegralClosureDVR
import Atlas.Knowledge.IsArithmeticFrobenius
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# arithmetic Frobenius on roots of unity

An arithmetic Frobenius of a finite extension of a
mixed-characteristic local field acts on the prime-to-`q` roots of
unity exactly by `ζ ↦ ζ ^ q`, `q = Nat.card 𝓀[K]`: the substitution
congruence `Atlas.Knowledge.IsArithmeticFrobenius` holds modulo the
maximal ideal of the integral closure, and reduction is injective on
`m`-th roots of unity for `m` prime to `q`. This is the field-level
reading of the Frobenius congruence that the normalization chain
evaluates on the cyclotomic floors (#104).

## Main statements

* `IsArithmeticFrobenius.apply_of_pow_eq_one` — the exact action on
  prime-to-`q` roots of unity; proved.
* `natCast_notMem_maximalIdeal_of_coprime` — integers prime to `q`
  avoid the maximal ideal of the integral closure; proved.
* `IsArithmeticFrobenius.isIntegral_of_pow_eq_one` — roots of unity are
  integral; proved.

## Implementation notes

The route is the identification the notes of
`Atlas.Knowledge.IsArithmeticFrobenius` record: the layer's
substitution congruence is Mathlib's `AlgHom.IsArithFrobAt` at
`Q := IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E)` —
`Atlas.Knowledge.integralClosure_jacobson_bot_eq_maximalIdeal` converts
the radical and `Atlas.Knowledge.natCard_quotient_under` (public since
this brick of #104, for exactly this consumer) converts the exponent —
and Mathlib's `AlgHom.IsArithFrobAt.apply_of_pow_eq_one` then does the
work. Its two side conditions are discharged the way the global
template `Atlas.Knowledge.cyclotomicArtinNormalization` does at a
number-field prime: the root of unity is integral as a root of the
monic `X ^ m - 1` (`IsArithmeticFrobenius.isIntegral_of_pow_eq_one`,
stated over any base ring), and `(m : _) ∉ Q` comes from the
coprimality by a Bézout argument in the base residue quotient under its
under-ideal name — `m` vanishes there by the membership, `q` by
`Nat.cast_card_eq_zero` through `natCard_quotient_under`, and a cast
Bézout combination `a * m + b * q = 1` then forces `1 = 0` — so no
decomposition of `q` into residue-characteristic powers enters. The
read repository's counterpart is
`padicCyclotomicUnramifiedArithmeticFrobenius_apply_primitiveRoot`,
which sends its *constructed* Frobenius's *chosen* primitive root to
the `q`-th power under Henselian-valuation and monogenic-presentation
hypotheses; the layer's form is predicate-based — any automorphism
satisfying the congruence, any root of any prime-to-`q` order, no
Hensel or monogenicity input — matching how the finite Artin map
delivers its Frobenii
(`Atlas.Knowledge.isArithmeticFrobenius_abelianLocalArtinMonoidHom`).

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- A root of unity is integral over any base ring: the monic
`X ^ m - 1` kills it. -/
theorem IsArithmeticFrobenius.isIntegral_of_pow_eq_one {A L : Type*} [CommRing A] [CommRing L]
    [Algebra A L] {x : L} {m : ℕ} (hm : m ≠ 0) (hx : x ^ m = 1) : IsIntegral A x :=
  ⟨Polynomial.X ^ m - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hm, by simp [hx]⟩

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  (E : Type*) [Field E] [Algebra K E] [Algebra.IsAlgebraic K E]

/-- An integer prime to the residue cardinality avoids the maximal
ideal of the integral closure: in the base residue quotient under its
under-ideal name both `m` and `q = Nat.card 𝓀[K]` would vanish,
against a Bézout combination `a * m + b * q = 1`. -/
theorem natCast_notMem_maximalIdeal_of_coprime [FiniteDimensional K E] {m : ℕ}
    (hm : Nat.Coprime m (Nat.card 𝓀[K])) :
    (m : integralClosure 𝒪[K] E) ∉ IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E) := by
  intro hmem
  set Q := IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E)
  have h1 : (m : 𝒪[K]) ∈ Q.under 𝒪[K] := by
    rw [Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hmem
  have h2 : (m : 𝒪[K] ⧸ Q.under 𝒪[K]) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (Q.under 𝒪[K])), Ideal.Quotient.eq_zero_iff_mem]
    exact h1
  have hcard := natCard_quotient_under K E
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  haveI : Finite (𝒪[K] ⧸ Q.under 𝒪[K]) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have h3 : (Nat.card 𝓀[K] : 𝒪[K] ⧸ Q.under 𝒪[K]) = 0 := by
    cases nonempty_fintype (𝒪[K] ⧸ Q.under 𝒪[K])
    rw [← hcard, Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero _
  have h4 : IsCoprime (m : 𝒪[K] ⧸ Q.under 𝒪[K]) (Nat.card 𝓀[K] : 𝒪[K] ⧸ Q.under 𝒪[K]) := by
    have h5 : IsCoprime (m : ℤ) (Nat.card 𝓀[K] : ℤ) := Nat.isCoprime_iff_coprime.mpr hm
    have h6 := h5.map (Int.castRingHom (𝒪[K] ⧸ Q.under 𝒪[K]))
    simpa using h6
  rw [h2, h3] at h4
  haveI : Nontrivial (𝒪[K] ⧸ Q.under 𝒪[K]) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard]; omega)
  obtain ⟨a, b, hab⟩ := h4
  simp at hab

variable {K E}

/-- **An arithmetic Frobenius acts on the prime-to-`q` roots of unity
by `ζ ↦ ζ ^ q` exactly**, `q = Nat.card 𝓀[K]`: the substitution
congruence pins the image modulo the maximal ideal of the integral
closure, and reduction is injective on `m`-th roots of unity for `m`
prime to `q` ([Milne 2020, Chap. I, §1, p.20][MilneCFT];
Yamaguchi 2026,
`LocalFieldTheory/Padic/Cyclotomic/Unramified/ArithmeticFrobenius.lean:1054`,
its constructed Frobenius at the chosen primitive root). -/
theorem IsArithmeticFrobenius.apply_of_pow_eq_one [FiniteDimensional K E] {σ : E ≃ₐ[K] E}
    (hσ : IsArithmeticFrobenius K E σ) {m : ℕ} (hm : Nat.Coprime m (Nat.card 𝓀[K]))
    {ζ : E} (hζ : ζ ^ m = 1) : σ ζ = ζ ^ Nat.card 𝓀[K] := by
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hm
    omega
  set z : integralClosure 𝒪[K] E := ⟨ζ, IsArithmeticFrobenius.isIntegral_of_pow_eq_one hm0 hζ⟩
  -- the layer's congruence is Mathlib's `IsArithFrobAt` at the maximal ideal
  have hfrob : ((galRestrict 𝒪[K] K E (integralClosure 𝒪[K] E) σ :
      integralClosure 𝒪[K] E ≃ₐ[𝒪[K]] integralClosure 𝒪[K] E) :
        integralClosure 𝒪[K] E →ₐ[𝒪[K]] integralClosure 𝒪[K] E).IsArithFrobAt
      (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] E)) := by
    intro x
    rw [natCard_quotient_under K E]
    have hx := hσ x
    rwa [integralClosure_jacobson_bot_eq_maximalIdeal K E] at hx
  have hz : z ^ m = 1 := by
    ext
    push_cast
    exact hζ
  have happ := hfrob.apply_of_pow_eq_one hz (natCast_notMem_maximalIdeal_of_coprime K E hm)
  rw [natCard_quotient_under K E] at happ
  have happ' : galRestrict 𝒪[K] K E (integralClosure 𝒪[K] E) σ z = z ^ Nat.card 𝓀[K] := happ
  have hcoe := congrArg (algebraMap (integralClosure 𝒪[K] E) E) happ'
  rw [map_pow, algebraMap_galRestrict_apply] at hcoe
  exact hcoe

end Atlas.Knowledge
