import Mathlib
import Atlas.Knowledge.IntegerIsIntegralClosure
import Atlas.Knowledge.IntegerValuation
import Atlas.Knowledge.MapMaximalIdealEqPowCardInertia
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.NormalizedValuationAlgEquiv

/-!
# normalized valuation of a norm

The valuation laws of a finite extension of mixed-characteristic local fields, pinned
by the exponent of the ideal identity `𝓂[K]·𝒪 = 𝓂[L]^e`: the embedding scales values
by `e` — on integers and on units — and, for a Galois extension, a norm's value
satisfies `e · v_K(N y) = [L : K] · v_L(y)`, the conjugate-product computation of the
unramified case freed of its `e = 1` hypothesis. These are the valuation half of the
reciprocity engine's ambient data (#104): the source's `norm_range` axiom is this law
read at `f = [L : K]/e`.

## Main statements

* `integerValuation_algebraMap_of_map_eq_pow` / `normalizedValuation_map_algebraMap_of_map_eq_pow`
  — the embedding scales the value by `e`; proved.
* `normalizedValuation_norm_of_map_eq_pow` — `e · v_K(N y) = [L : K] · v_L(y)` for
  Galois `L/K`; proved.

## Implementation notes

Everything is hypothesis-shaped over `map 𝓂[K] = 𝓂[L] ^ e`, the composable form of
`Atlas.Knowledge.MapMaximalIdealEqPowCardInertia.exists_map_maximalIdeal_eq_pow` and
the shape the level tower's `Atlas.Knowledge.map_maximalIdeal_levelField` supplies
directly. The integer law is a double reading of
`Atlas.Knowledge.span_singleton_eq_pow_maximalIdeal`; the unit law lifts it along an
`IsLocalization.surj` fraction; the norm law is the unramified sibling's
conjugate-product argument with the `e`-scaling replacing the value-preservation. The
`e`-form is deliberate: the inertia-degree form `v_K(N y) = f · v_L(y)` divides by `e`
and the non-normal extension of the law are deferred to the engine bricks that first
need them, rather than built speculatively.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer
  New York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section NormLaw

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] [IsMixedCharLocalField L]

/- Powers of the maximal ideal of a discrete valuation ring are injective in the
exponent: the coheight separates them. -/
private theorem maximalIdeal_pow_injective {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {a b : ℕ}
    (h : (IsLocalRing.maximalIdeal R) ^ a = (IsLocalRing.maximalIdeal R) ^ b) :
    a = b := by
  have hco := congrArg Order.coheight h
  rwa [IsDiscreteValuationRing.coheight_pow_maximalIdeal,
    IsDiscreteValuationRing.coheight_pow_maximalIdeal, Nat.cast_inj] at hco

omit [FiniteDimensional K L] in
/-- **The embedding scales the value by the ramification exponent**, on integers: with
`𝓂[K]·𝒪 = 𝓂[L]^e`, the value of an embedded integer is `e` times its value — the two
principal-ideal readings of `Atlas.Knowledge.span_singleton_eq_pow_maximalIdeal`
compared ([Serre 1979, Chap. I, §5, p.16][Serre1979] — `i(𝔭) = 𝔭B = ∏ 𝔓^e`, read at
one element). -/
theorem integerValuation_algebraMap_of_map_eq_pow {e : ℕ}
    (he : Ideal.map (algebraMap ↥𝒪[K] ↥𝒪[L]) 𝓂[K] = 𝓂[L] ^ e)
    {y : ↥𝒪[K]} (hy : y ≠ 0) :
    integerValuation L (algebraMap ↥𝒪[K] ↥𝒪[L] y) =
      (e : ℤ) * integerValuation K y := by
  have hy' : algebraMap ↥𝒪[K] ↥𝒪[L] y ≠ 0 := by
    intro h0
    apply hy
    have h1 := congrArg (algebraMap ↥𝒪[L] L) h0
    rw [map_zero, ← IsScalarTower.algebraMap_apply ↥𝒪[K] ↥𝒪[L] L,
      IsScalarTower.algebraMap_apply ↥𝒪[K] K L] at h1
    have h2 : algebraMap ↥𝒪[K] K y = 0 := by
      apply (algebraMap K L).injective
      rw [map_zero]
      exact h1
    exact Subtype.ext h2
  have hspanK := span_singleton_eq_pow_maximalIdeal K hy
  have hspanL := span_singleton_eq_pow_maximalIdeal L hy'
  have hmap : Ideal.map (algebraMap ↥𝒪[K] ↥𝒪[L]) (Ideal.span {y}) =
      Ideal.span {algebraMap ↥𝒪[K] ↥𝒪[L] y} := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [hspanK, Ideal.map_pow, he, ← pow_mul] at hmap
  rw [hspanL] at hmap
  have hexp := maximalIdeal_pow_injective hmap.symm
  have hL := Int.toNat_of_nonneg
    (integerValuation_nonneg L (algebraMap ↥𝒪[K] ↥𝒪[L] y))
  have hK := Int.toNat_of_nonneg (integerValuation_nonneg K y)
  rw [← hL, ← hK]
  exact_mod_cast hexp

omit [FiniteDimensional K L] in
/-- **The embedding scales the value by the ramification exponent**, on units: the
integer law lifted along a fraction representation
([Serre 1979, Chap. I, §5, p.16][Serre1979]). -/
theorem normalizedValuation_map_algebraMap_of_map_eq_pow {e : ℕ}
    (he : Ideal.map (algebraMap ↥𝒪[K] ↥𝒪[L]) 𝓂[K] = 𝓂[L] ^ e) (y : Kˣ) :
    normalizedValuation L (Units.map ((algebraMap K L) : K →* L) y) =
      (e : ℤ) * normalizedValuation K y := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors ↥𝒪[K]) ((y : Kˣ) : K)
  have hbne : (b : ↥𝒪[K]) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hane : a ≠ 0 := by
    intro rfl'
    subst rfl'
    rw [map_zero] at hab
    rcases mul_eq_zero.mp hab with h1 | h2
    · exact Units.ne_zero y h1
    · exact hbne (IsFractionRing.injective ↥𝒪[K] K (by rw [h2, map_zero]))
  have ha' : algebraMap ↥𝒪[K] K a ≠ 0 := fun h0 =>
    hane (IsFractionRing.injective ↥𝒪[K] K (by rw [h0, map_zero]))
  have hb' : algebraMap ↥𝒪[K] K (b : ↥𝒪[K]) ≠ 0 := fun h0 =>
    hbne (IsFractionRing.injective ↥𝒪[K] K (by rw [h0, map_zero]))
  set ua := Units.mk0 (algebraMap ↥𝒪[K] K a) ha'
  set ub := Units.mk0 (algebraMap ↥𝒪[K] K (b : ↥𝒪[K])) hb'
  have hyu : y * ub = ua := Units.ext hab
  have hval : ∀ (c : ↥𝒪[K]) (hc : c ≠ 0)
      (hc' : algebraMap ↥𝒪[K] K c ≠ 0),
      normalizedValuation L (Units.map ((algebraMap K L) : K →* L)
        (Units.mk0 (algebraMap ↥𝒪[K] K c) hc')) =
      (e : ℤ) * normalizedValuation K (Units.mk0 (algebraMap ↥𝒪[K] K c) hc') := by
    intro c hc hc'
    have hcL : algebraMap ↥𝒪[K] ↥𝒪[L] c ≠ 0 := by
      intro h0
      have h1 := congrArg (algebraMap ↥𝒪[L] L) h0
      rw [map_zero, ← IsScalarTower.algebraMap_apply ↥𝒪[K] ↥𝒪[L] L,
        IsScalarTower.algebraMap_apply ↥𝒪[K] K L] at h1
      exact hc' ((algebraMap K L).injective (by rw [h1, map_zero]))
    have hcL' : algebraMap ↥𝒪[L] L (algebraMap ↥𝒪[K] ↥𝒪[L] c) ≠ 0 := by
      rw [← IsScalarTower.algebraMap_apply ↥𝒪[K] ↥𝒪[L] L,
        IsScalarTower.algebraMap_apply ↥𝒪[K] K L]
      exact fun h0 => hc' ((algebraMap K L).injective (by rw [h0, map_zero]))
    have hint := integerValuation_algebraMap_of_map_eq_pow K L he hc
    rw [integerValuation_of_ne_zero L hcL', integerValuation_of_ne_zero K hc']
      at hint
    have hu : Units.map ((algebraMap K L) : K →* L)
        (Units.mk0 (algebraMap ↥𝒪[K] K c) hc') =
        Units.mk0 (algebraMap ↥𝒪[L] L (algebraMap ↥𝒪[K] ↥𝒪[L] c)) hcL' := by
      ext
      simp only [Units.coe_map, Units.val_mk0, MonoidHom.coe_coe]
      rw [← IsScalarTower.algebraMap_apply ↥𝒪[K] ↥𝒪[L] L,
        IsScalarTower.algebraMap_apply ↥𝒪[K] K L]
    rw [hu]
    exact hint
  have hmapyu := congrArg (fun z => normalizedValuationHom L
    (Units.map ((algebraMap K L) : K →* L) z)) hyu
  simp only [map_mul] at hmapyu
  have hKyu := congrArg (normalizedValuationHom K) hyu
  rw [map_mul] at hKyu
  have h1 := congrArg Multiplicative.toAdd hmapyu
  have h2 := congrArg Multiplicative.toAdd hKyu
  simp only [toAdd_mul] at h1 h2
  change normalizedValuation L _ + normalizedValuation L _ =
    normalizedValuation L _ at h1
  change normalizedValuation K _ + normalizedValuation K _ =
    normalizedValuation K _ at h2
  rw [hval (b : ↥𝒪[K]) hbne hb', hval a hane ha'] at h1
  linear_combination h1 - (e : ℤ) * h2

/-- **The norm law in exponent form**: for a finite Galois extension with
`𝓂[K]·𝒪 = 𝓂[L]^e`, `e · v_K(N y) = [L : K] · v_L(y)` — the norm is the full conjugate
product, each conjugate of the same value, and the embedding scales by `e`
([Serre 1979, Chap. I, §5, p.16][Serre1979] — `N(𝔓) = 𝔭^f`, the element form at
`f = [L : K]/e`; the source's counterpart is the `norm_range` field of
[Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Valuation.lean:153`,
`ValuationData`][Yamaguchi2026]). -/
theorem normalizedValuation_norm_of_map_eq_pow [IsGalois K L] {e : ℕ}
    (he : Ideal.map (algebraMap ↥𝒪[K] ↥𝒪[L]) 𝓂[K] = 𝓂[L] ^ e) (y : Lˣ) :
    (e : ℤ) * normalizedValuation K (Units.map ((Algebra.norm K) : L →* K) y) =
      (Module.finrank K L : ℤ) * normalizedValuation L y := by
  have hunit : Units.map ((algebraMap K L) : K →* L)
      (Units.map ((Algebra.norm K) : L →* K) y) =
      ∏ σ : L ≃ₐ[K] L, Units.map (σ : L →* L) y := by
    ext
    rw [show ((∏ σ : L ≃ₐ[K] L, Units.map (σ : L →* L) y : Lˣ) : L) =
      ∏ σ : L ≃ₐ[K] L, ((Units.map (σ : L →* L) y : Lˣ) : L) from
        map_prod (Units.coeHom L) _ _]
    change algebraMap K L (Algebra.norm K ((y : Lˣ) : L)) = _
    rw [Algebra.norm_eq_prod_automorphisms]
    rfl
  have hv := congrArg (normalizedValuationHom L) hunit
  rw [map_prod] at hv
  have hterm : ∀ σ : L ≃ₐ[K] L,
      normalizedValuationHom L (Units.map (σ : L →* L) y) =
      normalizedValuationHom L y := by
    intro σ
    exact normalizedValuation_algEquiv K L σ y
  rw [Finset.prod_congr rfl (fun σ _ => hterm σ)] at hv
  have hcard : (Finset.univ : Finset (L ≃ₐ[K] L)).card = Module.finrank K L := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact IsGalois.card_aut_eq_finrank K L
  rw [Finset.prod_const, hcard] at hv
  have hfinal := congrArg Multiplicative.toAdd hv
  rw [_root_.toAdd_pow] at hfinal
  have hLHS : Multiplicative.toAdd (normalizedValuationHom L
      (Units.map ((algebraMap K L) : K →* L)
        (Units.map ((Algebra.norm K) : L →* K) y))) =
      (e : ℤ) * normalizedValuation K (Units.map ((Algebra.norm K) : L →* K) y) :=
    normalizedValuation_map_algebraMap_of_map_eq_pow K L he _
  rw [hLHS] at hfinal
  rw [hfinal, nsmul_eq_mul]
  rfl

end NormLaw

end Atlas.Knowledge
