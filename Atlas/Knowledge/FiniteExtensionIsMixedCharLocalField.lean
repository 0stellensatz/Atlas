import Mathlib
import Atlas.Knowledge.ExistsValuativeExtension
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.IntegerIsIntegralClosure

/-!
# finite extension of a mixed-characteristic local field

A finite extension of a mixed-characteristic local field is again one. The statement splits
along what is data and what is property: given a valuative relation on `L` extending that of
`K` and inducing its topology, `L` satisfies `Atlas.Knowledge.IsMixedCharLocalField`—and such a
structure exists, the valuation of `K` prolonging to `L`. Local compactness descends through
finite dimensionality, nontriviality ascends through
`Atlas.Knowledge.IntegerIsIntegralClosure.isNontrivial`, and characteristic zero rides the
injective `algebraMap`. This is the field-side infrastructure that lets a statement about a
finite extension of a mixed-characteristic local field drop any explicit local-field hypothesis
on the extension, as `Atlas.Knowledge.CompletedUnitGroup` does.

## Main statements

* `FiniteExtensionIsMixedCharLocalField.locallyCompactSpace` — a finite extension carrying the
  valuative topology is locally compact.
* `finiteExtension_isMixedCharLocalField` — the conditional form: the extended structure is a
  mixed-characteristic local field structure.
* `exists_extension_isMixedCharLocalField` — the structure exists.

## Implementation notes

The conditional form hypothesizes `IsValuativeTopology L` rather than deriving it: the
hypothesis ties the topology of `L` to its valuative relation, and without it the statement
would quantify over junk topologies on `L` for which the local-field class is simply false.
Local compactness is Mathlib's `LocallyCompactSpace.of_finiteDimensional_of_complete`, which
asks for `K` as a complete `NontriviallyNormedField` and for `L` as a topological vector space
over it; the layer carries `K` only valuatively, so the norm is rebuilt inside the proof
exactly as in `Atlas.Knowledge.IntegerIsIntegralClosure`, and what remains—the one genuinely
valuative leg—is continuity of the `algebraMap`. A ball of `L` need not contain the image of a
ball of `K` for an abstract extension of valuative relations; here it does because below any
`γ < 1` of the value group of `L` sits the image of an element of `K`, namely the constant
coefficient of the minimal polynomial over `𝒪[K]` of a `b` of value `γ`: the relation
`Atlas.Knowledge.mem_integer_iff_isIntegral` makes `b` integral over `𝒪[K]`, and the constant
coefficient is `b` times a polynomial value that the valuation bounds by one coefficientwise.
The existence form quantifies the instances existentially, the pattern of
`Atlas.Knowledge.IsMLFType`, and conjoins the `Prop`-valued classes; it is what justifies
consumers that state claims about an abstract finite extension with no valuative data at all.
The data it installs are `Atlas.Knowledge.exists_valuativeExtension`'s prolongation and the
valuative topology `ValuativeRel.topologicalSpace`, Mathlib's canonical—deliberately
non-instance—topology of a valuative relation, whose `IsValuativeTopology` certificate then
holds by construction. Uniqueness of the prolongation is classical and deliberately not
recorded: no consumer compares two structures.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

namespace FiniteExtensionIsMixedCharLocalField

private theorem exists_algebraMap_le (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (L : Type*) [Field L] [ValuativeRel L] [Algebra K L]
    [ValuativeExtension K L] [FiniteDimensional K L] (γ : (ValueGroupWithZero L)ˣ) :
    ∃ c : K, c ≠ 0 ∧ valuation L (algebraMap K L c) ≤ γ := by
  rcases le_or_gt 1 (γ : ValueGroupWithZero L) with hγ | hγ
  · -- above `1` any nontrivially small element of `K` does
    obtain ⟨u, hu0, hu1⟩ := ValuativeRel.IsNontrivial.exists_lt_one (R := K)
    obtain ⟨a, rfl⟩ := valuation_surjective u
    refine ⟨a, (Valuation.ne_zero_iff _).mp hu0.ne', le_trans (le_of_lt ?_) hγ⟩
    rw [← ValuativeExtension.mapValueGroupWithZero_valuation]
    have h1 := ValuativeExtension.mapValueGroupWithZero_strictMono (A := K) (B := L) hu1
    rwa [map_one] at h1
  · -- below `1` take a `b` of value `γ`, integral over `𝒪[K]`; the constant coefficient of its
    -- minimal polynomial is `b` times an element the valuation bounds by one
    obtain ⟨b, hb⟩ := valuation_surjective (γ : ValueGroupWithZero L)
    have hb0 : b ≠ 0 := fun h => γ.ne_zero (by rw [← hb, h, map_zero])
    have hbmem : b ∈ 𝒪[L] := by rw [Valuation.mem_integer_iff, hb]; exact hγ.le
    have hbi : IsIntegral 𝒪[K] b := (mem_integer_iff_isIntegral K L).mp hbmem
    have hc0 : algebraMap 𝒪[K] K ((minpoly 𝒪[K] b).coeff 0) ≠ 0 := by
      have h1 := minpoly.coeff_zero_ne_zero (IsIntegral.of_finite K b) hb0
      rwa [minpoly.isIntegrallyClosed_eq_field_fractions' (K := K) hbi,
        Polynomial.coeff_map] at h1
    refine ⟨algebraMap 𝒪[K] K ((minpoly 𝒪[K] b).coeff 0), hc0, ?_⟩
    -- split off the constant coefficient through `Polynomial.X_mul_divX_add`
    have hsplit : b * Polynomial.aeval b (minpoly 𝒪[K] b).divX +
        algebraMap 𝒪[K] L ((minpoly 𝒪[K] b).coeff 0) = 0 := by
      have h1 : Polynomial.aeval b (Polynomial.X * (minpoly 𝒪[K] b).divX +
          Polynomial.C ((minpoly 𝒪[K] b).coeff 0)) = 0 := by
        rw [Polynomial.X_mul_divX_add]; exact minpoly.aeval 𝒪[K] b
      rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] at h1
      exact h1
    have hs1 : valuation L (Polynomial.aeval b (minpoly 𝒪[K] b).divX) ≤ 1 := by
      rw [Polynomial.aeval_eq_sum_range]
      refine (valuation L).map_sum_le fun i _ => ?_
      rw [Algebra.smul_def, map_mul, map_pow]
      refine mul_le_one' ?_ (pow_le_one' hbmem i)
      rw [IsScalarTower.algebraMap_apply 𝒪[K] K L,
        ← ValuativeExtension.mapValueGroupWithZero_valuation, ← map_one
          (ValuativeExtension.mapValueGroupWithZero K L)]
      exact ValuativeExtension.mapValueGroupWithZero_strictMono.monotone
        ((minpoly 𝒪[K] b).divX.coeff i).2
    rw [← IsScalarTower.algebraMap_apply 𝒪[K] K L,
      eq_neg_of_add_eq_zero_right hsplit, Valuation.map_neg, Valuation.map_mul, hb]
    exact mul_le_of_le_one_right' hs1

private theorem continuous_algebraMap_of_finiteDimensional (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
    [IsValuativeTopology L] : Continuous (algebraMap K L) := by
  refine continuous_of_continuousAt_zero (algebraMap K L) ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero L)]
  rintro γ -
  obtain ⟨c, hc0, hc⟩ := exists_algebraMap_le K L γ
  refine ⟨Units.mk0 (valuation K c) ((Valuation.ne_zero_iff _).mpr hc0), trivial, fun a ha => ?_⟩
  calc valuation L (algebraMap K L a)
      = ValuativeExtension.mapValueGroupWithZero K L (valuation K a) :=
        (ValuativeExtension.mapValueGroupWithZero_valuation a).symm
    _ < ValuativeExtension.mapValueGroupWithZero K L (valuation K c) :=
        ValuativeExtension.mapValueGroupWithZero_strictMono ha
    _ = valuation L (algebraMap K L c) := ValuativeExtension.mapValueGroupWithZero_valuation c
    _ ≤ γ := hc

/-- A finite extension of a mixed-characteristic local field, carrying a valuative relation
that extends the base and the topology it induces, is locally compact: the extension is a
finite-dimensional topological vector space over its complete locally compact base, and local
compactness passes to such a space
([Serre 1979, Chap. II, §1, Prop. 1, p.27, and §2, Prop. 3 and Cor. 1, pp.28–29][Serre1979]). -/
theorem locallyCompactSpace (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
    [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L] [IsValuativeTopology L] :
    LocallyCompactSpace L := by
  haveI : ContinuousSMul K L :=
    continuousSMul_of_algebraMap K L (continuous_algebraMap_of_finiteDimensional K L)
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : CompleteSpace K := inferInstance
  exact LocallyCompactSpace.of_finiteDimensional_of_complete K L

end FiniteExtensionIsMixedCharLocalField

/-- A finite extension of a mixed-characteristic local field is one: the valuative relation
extending the base, together with the topology it induces, satisfies the whole carrier
signature ([Serre 1979, Chap. II, §2, Prop. 3, pp.28–29][Serre1979]). -/
theorem finiteExtension_isMixedCharLocalField (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
    [IsValuativeTopology L] : IsMixedCharLocalField L := by
  haveI : CharZero L := charZero_of_injective_algebraMap (R := K) (algebraMap K L).injective
  haveI : ValuativeRel.IsNontrivial L := IntegerIsIntegralClosure.isNontrivial K L
  haveI := FiniteExtensionIsMixedCharLocalField.locallyCompactSpace K L
  exact {}

/-- The mixed-characteristic local field structure on a finite extension exists: the valuation
of the base prolongs to the extension, and the topology it induces completes the carrier
signature ([Serre 1979, Chap. II, §2, Prop. 3 and Cor. 2, pp.28–29][Serre1979]). -/
theorem exists_extension_isMixedCharLocalField (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] :
    ∃ (_ : ValuativeRel L) (_ : TopologicalSpace L),
      ValuativeExtension K L ∧ IsValuativeTopology L ∧ IsMixedCharLocalField L := by
  obtain ⟨vL, hVE⟩ := exists_valuativeExtension K L
  haveI := hVE
  letI : TopologicalSpace L := ValuativeRel.topologicalSpace L
  haveI : IsValuativeTopology L := inferInstance
  exact ⟨vL, ValuativeRel.topologicalSpace L, hVE, ‹_›,
    finiteExtension_isMixedCharLocalField K L⟩

end Atlas.Knowledge
