import Mathlib
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IntegerValuation
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.NormalizedValuation

/-!
# standard open subgroups

The standard subgroups of the unit group of a mixed-characteristic
local field `K` inside its open subgroups (#104): every open subgroup
of `Kˣ` contains a unit level `U^{(i)} = 1 + 𝔪ⁱ`, since the levels are
a neighbourhood basis of `1`, and an open subgroup of finite index `d`
contains the standard subgroup `⟨πᵈ⟩ · U^{(i)}` for any uniformizer
`π`, since `d`-th powers lie in a subgroup of index `d`. This is the
first step of the existence theorem's Lubin–Tate route: the standard
subgroup is the norm subgroup of an explicit compositum.

## Main statements

* `exists_higherUnitGroup_le_of_isOpen` — an open subgroup of `Kˣ`
  contains a unit level; proved.
* `exists_zpowers_sup_higherUnitGroup_le_of_isOpen_finiteIndex` — an
  open finite-index subgroup contains `⟨πᵈ⟩ · U^{(i)}` for a given
  uniformizer `π` and some level `i`; proved.

## Implementation notes

The unit levels are the layer's `Atlas.Knowledge.higherUnitGroup` where
the source spells `U^{(n)}` as its `fieldPrincipalUnits`, and the
standard subgroup `⟨πᵈ⟩ · U^{(i)}` is written out as
`Subgroup.zpowers (π ^ d) ⊔ higherUnitGroup K i` where the source names
it `uniformizerPrincipalSubgroup`, so nothing here is definitionally
new. The neighbourhood argument runs through Mathlib's
`IsValuativeTopology.hasBasis_nhds'` at `1`, the layer's
`Atlas.Knowledge.normalizedValuation_lt_iff` picking the level below a
given radius, where the source's runs through its
`exists_maximalIdeal_pow_subset_nhds_zero`; membership in a level is
unwound by `mem_higherUnitGroup_iff`, and the containment of the ideal
power in the closed ball is the source's inline argument. The second
theorem takes the irreducible `π` as an argument and returns only the
level, where the source returns a uniformizer of valuation one
existentially: its consumer, the Lubin–Tate level field, fixes `π`
first. The local field is `IsMixedCharLocalField` where the source's is
nonarchimedean, the layer's instantiation being mixed-characteristic
throughout. The file is the source's
`LocalFieldTheory/NonarchimedeanLocalField/StandardOpenSubgroups.lean`
in that vocabulary, its two definitions absorbed.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

open ValuativeRel

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- **Every open subgroup of the multiplicative group of a
mixed-characteristic local field contains a sufficiently deep unit
level** ([Yamaguchi 2026,
`LocalFieldTheory/NonarchimedeanLocalField/StandardOpenSubgroups.lean:37`]
[Yamaguchi2026]). -/
theorem exists_higherUnitGroup_le_of_isOpen (H : Subgroup Kˣ) (hH : IsOpen (H : Set Kˣ)) :
    ∃ i : ℕ+, higherUnitGroup K i ≤ H := by
  rcases Units.isEmbedding_val₀.isOpen_iff.mp hH with ⟨V, hVopen, hV⟩
  have hOneV : (1 : K) ∈ V := by
    have h1 : (1 : Kˣ) ∈ Units.val ⁻¹' V := hV.symm ▸ H.one_mem
    exact h1
  obtain ⟨γ, hγ, hball⟩ :=
    (IsValuativeTopology.hasBasis_nhds' (1 : K)).mem_iff.mp (hVopen.mem_nhds hOneV)
  obtain ⟨g, hg⟩ := ValuativeRel.valuation_surjective γ
  have hg0 : g ≠ 0 := by
    rintro rfl
    exact hγ (by rw [← hg, map_zero])
  let gu : Kˣ := Units.mk0 g hg0
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[K])
  have hϖ0 : (ϖ : K) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  let ϖu : Kˣ := Units.mk0 (ϖ : K) hϖ0
  have hϖv : normalizedValuation K ϖu = 1 := normalizedValuation_irreducible K ϖ hϖ ϖu rfl
  let i : ℕ+ := ⟨(normalizedValuation K gu).toNat + 1, Nat.succ_pos _⟩
  refine ⟨i, ?_⟩
  intro x hx
  obtain ⟨u, hu, rfl⟩ := (mem_higherUnitGroup_iff K i x).1 hx
  have hle : valuation K ((((u : (↥𝒪[K])ˣ) : ↥𝒪[K]) - 1 : ↥𝒪[K]) : K) ≤
      valuation K ((ϖ : K) ^ (i : ℕ)) := by
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hu
    obtain ⟨c, hc⟩ := hu
    calc valuation K ((((u : (↥𝒪[K])ˣ) : ↥𝒪[K]) - 1 : ↥𝒪[K]) : K)
        = valuation K ((ϖ ^ (i : ℕ) * c : ↥𝒪[K]) : K) := by rw [hc]
      _ = valuation K ((ϖ : K) ^ (i : ℕ)) * valuation K (c : K) := by push_cast; rw [map_mul]
      _ ≤ valuation K ((ϖ : K) ^ (i : ℕ)) :=
          mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).mp c.2)
  have hnv : normalizedValuation K gu < normalizedValuation K (ϖu ^ (i : ℕ)) := by
    rw [← zpow_natCast, normalizedValuation_zpow, hϖv, mul_one]
    have h1 : normalizedValuation K gu ≤ ((normalizedValuation K gu).toNat : ℤ) :=
      Int.self_le_toNat _
    have h2 : ((normalizedValuation K gu).toNat : ℤ) < ((i : ℕ) : ℤ) := by
      simp [i]
    exact lt_of_le_of_lt h1 h2
  have hlt : valuation K ((ϖ : K) ^ (i : ℕ)) < γ := by
    have h := (normalizedValuation_lt_iff K gu (ϖu ^ (i : ℕ))).1 hnv
    rw [Units.val_pow_eq_pow_val] at h
    exact hg ▸ h
  have hxV : ((Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u : Kˣ) : K) ∈ V := by
    apply hball
    change valuation K (((Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u : Kˣ) : K) - 1) < γ
    have hcoe : ((Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u : Kˣ) : K) - 1 =
        ((((u : (↥𝒪[K])ˣ) : ↥𝒪[K]) - 1 : ↥𝒪[K]) : K) := by
      simp
    rw [hcoe]
    exact lt_of_le_of_lt hle hlt
  have hpre : Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u ∈ Units.val ⁻¹' V := hxV
  change Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u ∈ (H : Set Kˣ)
  rw [← hV]
  exact hpre

/-- **An open finite-index subgroup contains a standard subgroup**
generated by the index-th power of a given uniformizer and a
sufficiently deep unit level ([Yamaguchi 2026,
`LocalFieldTheory/NonarchimedeanLocalField/StandardOpenSubgroups.lean:77`]
[Yamaguchi2026]). -/
theorem exists_zpowers_sup_higherUnitGroup_le_of_isOpen_finiteIndex
    (H : Subgroup Kˣ) [H.FiniteIndex] (hH : IsOpen (H : Set Kˣ))
    (π : ↥𝒪[K]) (hπ : Irreducible π) :
    ∃ i : ℕ+,
      Subgroup.zpowers ((Units.mk0 (π : K)
        (fun h0 => hπ.ne_zero (Subtype.ext h0))) ^ H.index) ⊔ higherUnitGroup K i ≤ H := by
  obtain ⟨i, hi⟩ := exists_higherUnitGroup_le_of_isOpen K H hH
  exact ⟨i, sup_le ((Subgroup.zpowers_le).2 (H.pow_index_mem _)) hi⟩

end

end Atlas.Knowledge
