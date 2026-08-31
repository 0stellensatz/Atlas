import Mathlib
import Atlas.Knowledge.AddValMapIntegralClosure
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
reciprocity engine's ambient data (#104), one brick short of its `norm_range` axiom's
shape — the `f`-form for every finite separable extension.

## Main statements

* `integerValuation_algebraMap_of_map_eq_pow` — the embedding scales integer values by
  `e`; proved.
* `normalizedValuation_map_algebraMap_of_map_eq_pow` — the unit form of the scaling;
  proved.
* `normalizedValuation_norm_of_map_eq_pow` — `e · v_K(N y) = [L : K] · v_L(y)` for
  Galois `L/K`; proved.
* `ne_zero_of_map_maximalIdeal_integer_eq_pow` — the pinned exponent is nonzero;
  proved.

## Implementation notes

Everything is hypothesis-shaped over `map 𝓂[K] = 𝓂[L] ^ e`, the composable form of
`Atlas.Knowledge.MapMaximalIdealEqPowCardInertia.exists_map_maximalIdeal_eq_pow` and
the shape the level tower's `Atlas.Knowledge.map_maximalIdeal_levelField` supplies
directly. The integer law is a double reading of
`Atlas.Knowledge.span_singleton_eq_pow_maximalIdeal`; the unit law lifts it along an
`IsLocalization.surj` fraction; the norm law is the unramified sibling's
conjugate-product argument with the `e`-scaling replacing the value-preservation. The
`e`-form and the Galois scope are what the conjugate product gives; the reciprocity
engine's `norm_range` axiom is discharged from the stronger pointwise law
`v_K(N y) = f · v_L(y)` for every finite *separable* extension, normal or not, which
`Atlas.Knowledge.normalizedValuation_norm_of_isSeparable` reaches by uniformizer
decomposition rather than conjugates, not by a division from this one. The
unramified siblings `Atlas.Knowledge.normalizedValuation_algebraMap_of_unramified`
and `Atlas.Knowledge.normalizedValuation_norm_of_unramified` are the `e = 1`
instances and now read through these laws.

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

omit [FiniteDimensional K L] in
/-- **The embedding scales the value by the ramification exponent**, on integers: with
`𝓂[K]·𝒪 = 𝓂[L]^e`, the value of an embedded integer is `e` times its value — the two
principal-ideal readings of `Atlas.Knowledge.span_singleton_eq_pow_maximalIdeal`
compared ([Serre 1979, Chap. I, §4, p.15][Serre1979] — "Clearly `v_𝔓(x) = e_𝔓 v_𝔭(x)`
if `x ∈ K`"). -/
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
  have hexp := AddValMapIntegralClosure.maximalIdeal_pow_injective hmap.symm
  have hL := Int.toNat_of_nonneg
    (integerValuation_nonneg L (algebraMap ↥𝒪[K] ↥𝒪[L] y))
  have hK := Int.toNat_of_nonneg (integerValuation_nonneg K y)
  rw [← hL, ← hK]
  exact_mod_cast hexp

omit [FiniteDimensional K L] in
/-- **The pinned exponent is nonzero**: the base maximal ideal maps into the maximal
ideal upstairs, so its ideal identity cannot read `⊤` — the integer-carrier sibling of
`Atlas.Knowledge.ne_zero_of_map_maximalIdeal_eq_pow`. -/
theorem ne_zero_of_map_maximalIdeal_integer_eq_pow {e : ℕ}
    (he : Ideal.map (algebraMap ↥𝒪[K] ↥𝒪[L]) 𝓂[K] = 𝓂[L] ^ e) : e ≠ 0 := by
  intro h0
  rw [h0, pow_zero, Ideal.one_eq_top] at he
  have hle : Ideal.map (algebraMap ↥𝒪[K] ↥𝒪[L]) 𝓂[K] ≤ 𝓂[L] :=
    Ideal.map_le_iff_le_comap.mpr fun x hx => by
      have hnu : ¬ IsUnit (algebraMap ↥𝒪[K] ↥𝒪[L] x) := fun hu =>
        hx (isUnit_of_map_unit (algebraMap ↥𝒪[K] ↥𝒪[L]) x hu)
      simpa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hnu
  rw [he, top_le_iff] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top hle

omit [FiniteDimensional K L] in
/-- **The embedding scales the value by the ramification exponent**, on units: the
integer law lifted along a fraction representation
([Serre 1979, Chap. I, §4, p.15][Serre1979]). -/
theorem normalizedValuation_map_algebraMap_of_map_eq_pow {e : ℕ}
    (he : Ideal.map (algebraMap ↥𝒪[K] ↥𝒪[L]) 𝓂[K] = 𝓂[L] ^ e) (y : Kˣ) :
    normalizedValuation L (Units.map ((algebraMap K L) : K →* L) y) =
      (e : ℤ) * normalizedValuation K y := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors ↥𝒪[K]) ((y : Kˣ) : K)
  have hbne : (b : ↥𝒪[K]) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hane : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at hab
    rcases mul_eq_zero.mp hab with h1 | h2
    · exact Units.ne_zero y h1
    · exact hbne (IsFractionRing.injective ↥𝒪[K] K (by rw [h2, map_zero]))
  have ha' : algebraMap ↥𝒪[K] K a ≠ 0 := algebraMap_integer_ne_zero K hane
  have hb' : algebraMap ↥𝒪[K] K (b : ↥𝒪[K]) ≠ 0 := algebraMap_integer_ne_zero K hbne
  set ua := Units.mk0 (algebraMap ↥𝒪[K] K a) ha'
  set ub := Units.mk0 (algebraMap ↥𝒪[K] K (b : ↥𝒪[K])) hb'
  have hyu : y * ub = ua := Units.ext hab
  have hval : ∀ (c : ↥𝒪[K]) (hc' : algebraMap ↥𝒪[K] K c ≠ 0),
      normalizedValuation L (Units.map ((algebraMap K L) : K →* L)
        (Units.mk0 (algebraMap ↥𝒪[K] K c) hc')) =
      (e : ℤ) * normalizedValuation K (Units.mk0 (algebraMap ↥𝒪[K] K c) hc') := by
    intro c hc'
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
    have hc : c ≠ 0 := fun h0 => hc' (by rw [h0, map_zero])
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
  simp only [toAdd_mul, toAdd_normalizedValuationHom] at h1 h2
  rw [hval (b : ↥𝒪[K]) hb', hval a ha'] at h1
  linear_combination h1 - (e : ℤ) * h2

/-- **The norm law in exponent form**: for a finite Galois extension with
`𝓂[K]·𝒪 = 𝓂[L]^e`, `e · v_K(N y) = [L : K] · v_L(y)` — the norm is the full conjugate
product, each conjugate of the same value, and the embedding scales by `e`
([Serre 1979, Chap. I, §5, p.16][Serre1979] — `N(𝔓) = 𝔭^f`, the element form at
`f = [L : K]/e`; the source's pointwise law, already in `f`-form and for every finite
separable extension, is
[Yamaguchi 2026, `LocalClassFieldTheory/Finite/LocalReciprocity/SeparableNormValuation.lean:513`,
`v_normUnits_eq_residue_finrank_mul_of_isSeparable`][Yamaguchi2026]). -/
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
      (e : ℤ) * normalizedValuation K (Units.map ((Algebra.norm K) : L →* K) y) := by
    rw [toAdd_normalizedValuationHom]
    exact normalizedValuation_map_algebraMap_of_map_eq_pow K L he _
  rw [hLHS] at hfinal
  rw [hfinal, nsmul_eq_mul, toAdd_normalizedValuationHom]

end NormLaw

end Atlas.Knowledge
