import Mathlib
import Atlas.Knowledge.IntegralClosureDVR
import Atlas.Knowledge.LowerRamificationGroup

/-!
# commutator membership in the first ramification group

The tame quotient of a finite extension of a mixed-characteristic local field is abelian at
the bottom of the lower numbering: the commutator of two automorphisms in the zeroth
lower-numbering ramification group lands in the first. This is the finite-level fact behind
the abelianness of the tame quotient proved in `Atlas.Knowledge.WildInertiaSubgroup`, which
assembles it over the finite Galois subextensions of the algebraic closure; the source states
it as the cyclicity of the quotient of the zeroth group by the first, embedded into the roots
of unity of the residue field.

## Main statements

* `commutator_mem_lowerRamificationGroup` — for `s`, `t` in `lowerRamificationGroup K L 0`,
  the commutator `s * t * s⁻¹ * t⁻¹` lies in `lowerRamificationGroup K L 1`.

## Implementation notes

The source's route is the residue embedding of the tame quotient at a uniformizer generating
the ring of integers over the inertia field; the proof here reaches the commutator statement
without the reduction to total ramification and without monogenicity, in two residue-field
steps inside the discrete valuation ring of `Atlas.Knowledge.IntegralClosureDVR`. On the
maximal ideal, writing `x = ϖ * b` at a generator `ϖ` makes `g (h x)` and `h (g x)` both `ϖ`
times products whose factors agree modulo the maximal ideal, since an automorphism moving
every element within the maximal ideal fixes residues—so the two agree modulo its square by
commutativity, with no unit bookkeeping. A general element differs from its `q`-th power by
an element of the maximal ideal, `q` the cardinality of the finite residue field, and on
`q`-th powers the difference of the two automorphism values factors through the geometric sum
of `geom_sum₂_mul`, whose residue is `q` copies of one power of a residue and vanishes
because `q` does in the residue field. Nothing beyond the integral closure, its finite
residue field, and the principal maximal ideal enters.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

namespace CommutatorMemLowerRamificationGroup

/-- The generic core, in a discrete valuation ring with finite residue field: two ring
endomorphisms moving every element within the maximal ideal commute with each other modulo its
square. -/
private theorem apply_sub_apply_mem_sq {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    {F : Type*} [FunLike F R R] [RingHomClass F R R] (g h : F)
    (hg : ∀ x : R, g x - x ∈ IsLocalRing.maximalIdeal R)
    (hh : ∀ x : R, h x - x ∈ IsLocalRing.maximalIdeal R) (y : R) :
    g (h y) - h (g y) ∈ IsLocalRing.maximalIdeal R ^ 2 := by
  classical
  letI : Fintype (IsLocalRing.ResidueField R) := Fintype.ofFinite (IsLocalRing.ResidueField R)
  set q := Fintype.card (IsLocalRing.ResidueField R) with hq
  -- residues are fixed
  have hresg : ∀ z : R, IsLocalRing.residue R (g z) = IsLocalRing.residue R z := by
    intro z
    have hz := hg z
    rwa [← IsLocalRing.ker_residue, RingHom.mem_ker, map_sub, sub_eq_zero] at hz
  have hresh : ∀ z : R, IsLocalRing.residue R (h z) = IsLocalRing.residue R z := by
    intro z
    have hz := hh z
    rwa [← IsLocalRing.ker_residue, RingHom.mem_ker, map_sub, sub_eq_zero] at hz
  -- the Frobenius decomposition of an arbitrary element
  have hcard0 : ((q : ℕ) : IsLocalRing.ResidueField R) = 0 := by
    rw [hq]
    exact Nat.cast_card_eq_zero (IsLocalRing.ResidueField R)
  have hfrob : ∀ z : R, z - z ^ q ∈ IsLocalRing.maximalIdeal R := by
    intro z
    rw [← IsLocalRing.ker_residue, RingHom.mem_ker, map_sub, map_pow, sub_eq_zero]
    exact (FiniteField.pow_card (IsLocalRing.residue R z)).symm
  -- on the maximal ideal, commutation modulo the square at a generator
  have hcaseM : ∀ x ∈ IsLocalRing.maximalIdeal R,
      g (h x) - h (g x) ∈ IsLocalRing.maximalIdeal R ^ 2 := by
    intro x hx
    obtain ⟨ϖ, hϖ_irr⟩ := IsDiscreteValuationRing.exists_irreducible R
    have hspan := hϖ_irr.maximalIdeal_eq
    have hϖm : ϖ ∈ IsLocalRing.maximalIdeal R := by
      rw [hspan]
      exact Ideal.mem_span_singleton_self ϖ
    rw [hspan, Ideal.mem_span_singleton] at hx
    obtain ⟨b, rfl⟩ := hx
    have hgm : g ϖ ∈ IsLocalRing.maximalIdeal R := by
      have := add_mem (hg ϖ) hϖm
      simpa using this
    have hhm : h ϖ ∈ IsLocalRing.maximalIdeal R := by
      have := add_mem (hh ϖ) hϖm
      simpa using this
    rw [hspan, Ideal.mem_span_singleton] at hgm hhm
    obtain ⟨u, hu⟩ := hgm
    obtain ⟨w, hw⟩ := hhm
    have e1 : g (h (ϖ * b)) = ϖ * u * g w * g (h b) := by
      rw [map_mul, hw, map_mul, map_mul, hu]
    have e2 : h (g (ϖ * b)) = ϖ * w * h u * h (g b) := by
      rw [map_mul, hu, map_mul, map_mul, hw]
    have hF : u * g w * g (h b) - w * h u * h (g b) ∈ IsLocalRing.maximalIdeal R := by
      rw [← IsLocalRing.ker_residue, RingHom.mem_ker]
      simp only [map_sub, map_mul, hresg, hresh]
      ring
    have hfactor : g (h (ϖ * b)) - h (g (ϖ * b)) =
        ϖ * (u * g w * g (h b) - w * h u * h (g b)) := by
      rw [e1, e2]
      ring
    rw [hfactor, pow_two]
    exact Ideal.mul_mem_mul hϖm hF
  -- split `y` along the Frobenius decomposition
  have hsplit : g (h y) - h (g y) =
      (g (h (y - y ^ q)) - h (g (y - y ^ q))) + (g (h (y ^ q)) - h (g (y ^ q))) := by
    simp only [map_sub]
    ring
  rw [hsplit]
  refine add_mem (hcaseM _ (hfrob y)) ?_
  -- on `q`-th powers, factor through the geometric sum
  have hpow : g (h (y ^ q)) - h (g (y ^ q)) = g (h y) ^ q - h (g y) ^ q := by
    simp only [map_pow]
  rw [hpow, ← geom_sum₂_mul, pow_two]
  refine Ideal.mul_mem_mul ?_ ?_
  · rw [← IsLocalRing.ker_residue, RingHom.mem_ker, map_sum]
    have hterm : ∀ i ∈ Finset.range q,
        IsLocalRing.residue R (g (h y) ^ i * h (g y) ^ (q - 1 - i)) =
          IsLocalRing.residue R y ^ (q - 1) := by
      intro i hi
      have hi' := Finset.mem_range.mp hi
      rw [map_mul, map_pow, map_pow, hresg, hresh, hresh, hresg, ← pow_add]
      congr 1
      omega
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      hcard0, zero_mul]
  · rw [← IsLocalRing.ker_residue, RingHom.mem_ker, map_sub, hresg, hresh, hresh, hresg,
      sub_self]

end CommutatorMemLowerRamificationGroup

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- For `s` and `t` in the zeroth lower-numbering ramification group of a finite extension of
a mixed-characteristic local field, the commutator `s * t * s⁻¹ * t⁻¹` lies in the first—the
abelianness of the tame quotient, which the source derives from its residue embedding into
the roots of unity of the residue field
([Serre 1979, Chap. IV, §2, Prop. 7 and Cor. 1, p.67][Serre1979]). -/
theorem commutator_mem_lowerRamificationGroup [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] {s t : L ≃ₐ[K] L}
    (hs : s ∈ lowerRamificationGroup K L 0) (ht : t ∈ lowerRamificationGroup K L 0) :
    s * t * s⁻¹ * t⁻¹ ∈ lowerRamificationGroup K L 1 := by
  -- the finite residue field of the integral closure
  haveI : FaithfulSMul 𝒪[K] (integralClosure 𝒪[K] L) :=
    (faithfulSMul_iff_algebraMap_injective 𝒪[K] (integralClosure 𝒪[K] L)).mpr
      fun a b hab => by
        have h : algebraMap 𝒪[K] L a = algebraMap 𝒪[K] L b :=
          congrArg (algebraMap (integralClosure 𝒪[K] L) L) hab
        rw [IsScalarTower.algebraMap_apply 𝒪[K] K L,
          IsScalarTower.algebraMap_apply 𝒪[K] K L] at h
        exact Subtype.ext ((algebraMap K L).injective h)
  haveI : Module.Finite 𝒪[K] (integralClosure 𝒪[K] L) :=
    IsIntegralClosure.finite 𝒪[K] K L (integralClosure 𝒪[K] L)
  haveI : IsLocalHom (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) := by
    have hcomap : (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L)).comap
        (algebraMap 𝒪[K] (integralClosure 𝒪[K] L)) = IsLocalRing.maximalIdeal 𝒪[K] :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
    constructor
    intro a ha
    by_contra hnot
    have ham : a ∈ IsLocalRing.maximalIdeal 𝒪[K] := hnot
    rw [← hcomap] at ham
    exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp ham) ha
  haveI : Finite (IsLocalRing.ResidueField (integralClosure 𝒪[K] L)) :=
    IsLocalRing.ResidueField.finite_of_finite (R := 𝒪[K]) (inferInstance : Finite 𝓀[K])
  have hjac := integralClosure_jacobson_bot_eq_maximalIdeal K L
  rw [mem_lowerRamificationGroup_iff] at hs ht
  rw [mem_lowerRamificationGroup_iff]
  simp only [zero_add, Int.toNat_one, pow_one, hjac] at hs ht
  have hexp : ((1 : ℤ) + 1).toNat = 2 := rfl
  simp only [hexp, hjac]
  intro x
  set σ := galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) s with hσdef
  set τ := galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t with hτdef
  have hmap : galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) (s * t * s⁻¹ * t⁻¹) =
      σ * τ * σ⁻¹ * τ⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hσdef, hτdef]
  rw [hmap]
  have happ : (σ * τ * σ⁻¹ * τ⁻¹) x = σ (τ (σ.symm (τ.symm x))) := by
    simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv]
  rw [happ]
  set y := σ.symm (τ.symm x) with hy
  have hx : x = τ (σ y) := by
    rw [hy, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  rw [hx]
  exact CommutatorMemLowerRamificationGroup.apply_sub_apply_mem_sq σ τ hs ht y

end Atlas.Knowledge
