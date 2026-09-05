import Mathlib
import Atlas.Knowledge.AbstractFixedField
import Atlas.Knowledge.AdditiveNormSubgroup
import Atlas.Knowledge.FiniteAbelianSubextension
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteNormQuotientEquivNormQuotient
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IntegerHigherUnitGroup
import Atlas.Knowledge.IntermediateFieldNormResidueNaturality
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LocalResidueDatum
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.NormSubgroupOrderEmbedding
import Atlas.Knowledge.NormUnits
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.StandardLubinTateGaloisDescription
import Atlas.Knowledge.StandardLubinTateLevelField
import Atlas.Knowledge.StandardLubinTateNormSubgroup
import Atlas.Knowledge.StandardLubinTateUniformizerUnit
import Atlas.Knowledge.StandardOpenSubgroups
import Atlas.Knowledge.UnitLevelFiniteIndex
import Atlas.Knowledge.UnitsFiniteIndexOpen
import Atlas.Knowledge.UnramifiedExtensionOfDegree
import Atlas.Knowledge.UnramifiedNormContainment

/-!
# local norm subgroup existence

The existence input of the finite local existence theorem for a
mixed-characteristic local field `K` (#104): every finite-index
subgroup `H ≤ Kˣ`, open automatically in mixed characteristic, contains
the norm subgroup of a finite Galois extension inside the algebraic
closure. The route is Lubin–Tate's, the one the source takes in equal
characteristic: `H` contains a standard subgroup `⟨πᵈ⟩ ⊔ U^{(i)}`; the
Lubin–Tate level field of level `i − 1` has norm subgroup exactly
`⟨π⟩ ⊔ U^{(i)}`; the abstract unramified extension of degree `d` has
norm subgroup inside the valuations divisible by `d`; and the
compositum's norm subgroup lies in both, hence in `⟨πᵈ⟩ ⊔ U^{(i)}`. The
source reaches the same input in characteristic zero through Kummer
theory over the cyclotomic field; the layer, holding the Lubin–Tate
norm-subgroup identity already, takes the shorter road.

## Main statements

* `exists_finiteGalois_localNormSubgroup_le` — a finite-index subgroup
  contains a finite Galois norm subgroup; proved.
* `zpowers_sup_higherUnitGroup_inf_comap_le` — the standard-subgroup
  intersection; proved.
* `localNormSubgroup_le_of_le` — the norm subgroup is antitone in the
  intermediate field; proved.

## Implementation notes

The compositum is formed in `AlgebraicClosure K`, the level field
carried over from the layer's `SeparableClosure K` along the inclusion
as the field range of the composite embedding, with
`Atlas.Knowledge.localNormSubgroup_fieldRange_eq` keeping its norm
subgroup; it is Galois by Mathlib's `IntermediateField.normal_sup` and
the perfectness of `K`, and finite-dimensional by
`IntermediateField.finiteDimensional_sup`. The Lubin–Tate norm subgroup
is `Atlas.Knowledge.standardLubinTateNormSubgroup_eq` at level `i − 1`,
its integer unit level read in `Kˣ` by
`Atlas.Knowledge.map_integerHigherUnitGroup_eq_higherUnitGroup` and its
uniformizer unit identified with the chosen irreducible's by
`Units.ext rfl`; the standard subgroup comes from
`Atlas.Knowledge.StandardOpenSubgroups` for that irreducible; the
unramified factor is `Atlas.Knowledge.UnramifiedExtensionOfDegree`'s
abelian package at the algebraic closure, made a concrete finite Galois
field by `Atlas.Knowledge.NormSubgroupOrderEmbedding`'s finiteness,
normality, and Galoisness transports, its norm subgroup transported by
`Atlas.Knowledge.map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup`
and bounded by `Atlas.Knowledge.UnramifiedNormContainment`. The norm
tower for intermediate fields is `Atlas.Knowledge.normUnits_tower` with
the inclusion as the algebra, the source's `normSubgroup_le_of_tower`;
the intersection lemma is the source's
`unramifiedNormSubgroup_inf_uniformizerPrincipalSubgroup_le` in the
layer's spelling, with `Atlas.Knowledge.higherUnitGroup_le_ker` for the
levels' vanishing valuation. The local field is
`IsMixedCharLocalField`. The openness of the finite-index subgroup is
not hypothesized, `Atlas.Knowledge.unitsFiniteIndexOpen` supplying it,
so the existence theorem is stated for every finite-index subgroup
where `Atlas.Knowledge.StandardOpenSubgroups` takes openness as an
argument. `localNormSubgroup_le_of_le` carries no local-field structure
and would sit as naturally beside `Atlas.Knowledge.localNormSubgroup`
in `Atlas.Knowledge.NormQuotient`; it is filed here with its first
consumer. `Atlas.Knowledge.StandardLubinTateGaloisDescription` is
imported for the level field's Galois instance, which no spelled name
here carries. The file assembles the source's
`StandardSubgroupIntersection.lean` and `StandardLubinTate.lean` at the
algebraic closure, in the shape of its equal-characteristic existence
input
`LocalClassFieldTheory/Finite/Existence/EqualCharacteristic.lean:380`,
without their intrinsic abbreviations.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

open ValuativeRel

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

omit [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K] in
/-- Norms from a larger intermediate field are norms from a smaller
one: the norm subgroup is antitone in the field, by transitivity of the
norm along the inclusion ([Yamaguchi 2026,
`LocalFieldTheory/NonarchimedeanLocalField/NormSubgroupFunctoriality.lean:19`]
[Yamaguchi2026]). -/
theorem localNormSubgroup_le_of_le {Ω : Type u} [Field Ω] [Algebra K Ω]
    {E₁ E₂ : IntermediateField K Ω} (h : E₁ ≤ E₂) [FiniteDimensional K E₂] :
    localNormSubgroup K E₂ ≤ localNormSubgroup K E₁ := by
  letI : Algebra E₁ E₂ := (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower K E₁ E₂ := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Module.Free E₁ E₂ := Module.Free.of_divisionRing E₁ E₂
  rintro x ⟨y, rfl⟩
  exact ⟨normUnits E₁ E₂ y, normUnits_tower K E₁ E₂ y⟩

/-- **The standard-subgroup intersection**: for a uniformizer `ϖ` of
normalized valuation one, an element of `⟨ϖ⟩ ⊔ U^{(i)}` whose
normalized valuation is divisible by `d` lies in `⟨ϖᵈ⟩ ⊔ U^{(i)}`
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/StandardSubgroupIntersection.lean:29`]
[Yamaguchi2026]). -/
theorem zpowers_sup_higherUnitGroup_inf_comap_le (ϖ : Kˣ) (hϖ : normalizedValuation K ϖ = 1)
    (d : ℕ) (i : ℕ+) :
    (Subgroup.zpowers ϖ ⊔ higherUnitGroup K i) ⊓
        Subgroup.comap (normalizedValuationHom K)
          (Subgroup.zpowers (Multiplicative.ofAdd (d : ℤ))) ≤
      Subgroup.zpowers (ϖ ^ d) ⊔ higherUnitGroup K i := by
  intro x hx
  rcases Subgroup.mem_sup.mp hx.1 with ⟨y, hy, z, hz, hyz⟩
  rcases Subgroup.mem_zpowers_iff.mp hy with ⟨k, hky⟩
  have hvz : normalizedValuation K z = 0 := by
    have hker : z ∈ (normalizedValuationHom K).ker := higherUnitGroup_le_ker K i hz
    rw [MonoidHom.mem_ker] at hker
    have := congrArg Multiplicative.toAdd hker
    rwa [toAdd_normalizedValuationHom, toAdd_one] at this
  have hvx : normalizedValuation K x = k := by
    rw [← hyz, normalizedValuation_mul, ← hky, normalizedValuation_zpow, hϖ, hvz]
    ring
  rcases Subgroup.mem_zpowers_iff.mp (Subgroup.mem_comap.mp hx.2) with ⟨m, hm⟩
  have hkm : k = (d : ℤ) * m := by
    have := congrArg Multiplicative.toAdd hm
    rw [toAdd_zpow, toAdd_ofAdd, toAdd_normalizedValuationHom, hvx, smul_eq_mul] at this
    rw [← this, mul_comm]
  refine Subgroup.mem_sup.mpr ⟨y, ?_, z, hz, hyz⟩
  rw [← hky, hkm, zpow_mul, zpow_natCast]
  exact Subgroup.zpow_mem_zpowers (ϖ ^ d) m

/-- **The existence input of the finite local existence theorem**:
every finite-index subgroup of `Kˣ` — open automatically, `K` being of
mixed characteristic — contains the norm subgroup of a finite Galois
extension inside the algebraic closure — the compositum of a Lubin–Tate
level field with the abstract unramified extension of degree the index,
whose norm subgroup lies in the standard subgroup the given subgroup
contains. The source's equal-characteristic assembly, which its
characteristic-zero input reaches through Kummer theory instead
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/StandardLubinTate.lean:142`]
[Yamaguchi2026]; [Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Existence/CyclotomicKummerDescent.lean:27`]
[Yamaguchi2026]). -/
theorem exists_finiteGalois_localNormSubgroup_le (H : Subgroup Kˣ) [H.FiniteIndex] :
    ∃ E : IntermediateField K (AlgebraicClosure K),
      FiniteDimensional K E ∧ IsGalois K E ∧ localNormSubgroup K E ≤ H := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[K])
  have hπ0 : (π : K) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext h0)
  let πu : Kˣ := Units.mk0 (π : K) hπ0
  have hπv : normalizedValuation K πu = 1 := normalizedValuation_irreducible K π hπ πu rfl
  have hH : IsOpen (H : Set Kˣ) := unitsFiniteIndexOpen K H inferInstance
  obtain ⟨i, hstd⟩ := exists_zpowers_sup_higherUnitGroup_le_of_isOpen_finiteIndex K H hH π hπ
  -- the Lubin–Tate level `i - 1`, inside the separable closure
  let T := standardLubinTateLevelField K hπ ((i : ℕ) - 1)
  have hunit : standardLubinTateUniformizerUnit K hπ = πu := Units.ext rfl
  have hT : localNormSubgroup K T = Subgroup.zpowers πu ⊔ higherUnitGroup K i := by
    have h := standardLubinTateNormSubgroup_eq K hπ ((i : ℕ) - 1)
    rw [Nat.sub_add_cancel i.pos, hunit,
      map_integerHigherUnitGroup_eq_higherUnitGroup K (i : ℕ) i.ne_zero] at h
    exact h.symm
  -- transported into the algebraic closure
  let j : T →ₐ[K] AlgebraicClosure K :=
    (separableClosure K (AlgebraicClosure K)).val.comp T.val
  let Tc : IntermediateField K (AlgebraicClosure K) := AlgHom.fieldRange j
  letI : FiniteDimensional K Tc :=
    (AlgEquiv.ofInjectiveField j).toLinearEquiv.finiteDimensional
  letI : IsGalois K Tc := IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField j)
  have hTc : localNormSubgroup K Tc = localNormSubgroup K T :=
    localNormSubgroup_fieldRange_eq K (AlgebraicClosure K) T j
  -- the unramified factor of degree the index
  let D := localResidueDatum K
  let Kfinite := galoisAmbientFiniteAbstractBase K (AlgebraicClosure K)
  let Kres := Kfinite.toFiniteResidueAbstractField D
  letI : NeZero H.index := ⟨Subgroup.FiniteIndex.index_ne_zero⟩
  let L := D.finiteUnramifiedAbelianExtension Kres H.index
  let Uf : IntermediateField K (AlgebraicClosure K) :=
    abstractFixedField K (AlgebraicClosure K) L.field
  have hLfin := finiteAbelianSubextension_finite_over_absoluteBase K (AlgebraicClosure K) L
  letI : FiniteDimensional K Uf :=
    abstractFixedField_finiteDimensional K (AlgebraicClosure K) L.field hLfin
  letI : IsGalois K Uf :=
    abstractFixedField_isGalois_of_base_normal K (AlgebraicClosure K) L.field
      (finiteAbelianSubextension_normal_over_absoluteBase K (AlgebraicClosure K) L)
  have hUf : localNormSubgroup K Uf ≤
      Subgroup.comap (normalizedValuationHom K)
        (Subgroup.zpowers (Multiplicative.ofAdd (H.index : ℤ))) := by
    intro x hx
    have hxAdd : Additive.ofMul x ∈ additiveNormSubgroup K Uf := hx
    rw [← map_finiteAbelianNormSubgroup_eq_additiveNormSubgroup K (AlgebraicClosure K) L] at hxAdd
    have h := finiteUnramifiedNormSubgroup_map_le_comap_normalizedValuationHom K H.index
    exact h hxAdd
  -- the compositum
  let E : IntermediateField K (AlgebraicClosure K) := Tc ⊔ Uf
  haveI : FiniteDimensional K E := IntermediateField.finiteDimensional_sup Tc Uf
  haveI : IsGalois K E := ⟨⟩
  refine ⟨E, inferInstance, inferInstance, ?_⟩
  intro x hx
  have hxT : x ∈ Subgroup.zpowers πu ⊔ higherUnitGroup K i := by
    rw [← hT, ← hTc]
    exact localNormSubgroup_le_of_le K (le_sup_left : Tc ≤ E) hx
  have hxU : x ∈ Subgroup.comap (normalizedValuationHom K)
      (Subgroup.zpowers (Multiplicative.ofAdd (H.index : ℤ))) :=
    hUf (localNormSubgroup_le_of_le K (le_sup_right : Uf ≤ E) hx)
  exact hstd (zpowers_sup_higherUnitGroup_inf_comap_le K πu hπv H.index i ⟨hxT, hxU⟩)

end

end Atlas.Knowledge
