import Mathlib
import Atlas.Knowledge.ArtinRestrictionSubfloor
import Atlas.Knowledge.CycloField
import Atlas.Knowledge.CycloFieldOfDegree
import Atlas.Knowledge.FiniteAbelianSubfieldCompositumNorm
import Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IntegerHigherUnitCount
import Atlas.Knowledge.IntegerHigherUnitGroup
import Atlas.Knowledge.IntegerUnitsNormalizedValuation
import Atlas.Knowledge.IntermediateFieldRestrictNormalHom
import Atlas.Knowledge.IntermediateFieldRestrictionKernel
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LocalNormSubgroupExistence
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.RamificationGroupAutCongr
import Atlas.Knowledge.RealHigherUnitGroup
import Atlas.Knowledge.StandardLubinTateLevelClosure
import Atlas.Knowledge.StandardLubinTateLevelField
import Atlas.Knowledge.StandardLubinTateLevelReciprocity
import Atlas.Knowledge.StandardLubinTateLowerRamification
import Atlas.Knowledge.StandardLubinTateUniformizerUnit
import Atlas.Knowledge.UnitLevelFiniteIndex
import Atlas.Knowledge.UpperRamificationGroup
import Atlas.Knowledge.UpperRamificationGroupSubfloor

/-!
# standard compositum

The compositum `F = Tₙ ⊔ K (μ_{q ^ d − 1})` of a Lubin–Tate level closure with the unramified
cyclotomic floor of degree `d`, and the ramification compatibility of the Artin map on it: at
every `t > 0` the Artin image of `U^t` is `G^t (F/K)`, and at `t = 0` the Artin image of the
full unit group is `G^0 (F/K)`, the inertia group. Every finite abelian extension lies in
such a compositum, so this is where the compatibility is proved before it descends. Both
sides of each statement lie in the kernel of restriction to the unramified factor — the Artin
side because units are norms from an unramified extension, the Galois side because that
factor's upper groups vanish — and restriction to the level is injective there, with the two
sides having the same image by the level case; at `t = 0` the equality is instead a count
against the level's Galois group.

## Main definitions

* `standardCompositum` — `Tₙ ⊔ K (μ_{q ^ d − 1})`.

## Main statements

* `standardCompositum_isAbelianGalois` — the compositum is abelian.
* `map_realHigherUnitGroup_standardCompositum` — `Art (U^t) = G^t (F/K)` for `t > 0`.
* `map_units_standardCompositum` — `Art (U^0) = G^0 (F/K)`.

## Implementation notes

The compositum is an `abbrev` so that the instances of a `⊔` are found by search; its
commutativity is `Atlas.Knowledge.isAbelianGalois_sup`, once the cyclotomic level is known
nonzero, which `d > 0` gives and instance search cannot see. At `t > 0` the argument is
`Atlas.Knowledge.subgroup_eq_of_map_eq_of_le` with the joint injectivity of
`Atlas.Knowledge.IntermediateFieldRestrictionKernel`. At `t = 0` the Artin image of the units
is the image of `U^0 ⊔ N (F) = N (K (μ))`, the compositum law
`Atlas.Knowledge.localNormSubgroup_sup` supplying `π ^ d ∈ N (F)`, hence the kernel of
restriction to the cyclotomic factor; the inertia group lies in that kernel, and its order is
at least the level's Galois group by restriction to the level while the kernel's is at most
the index `(q − 1) qⁿ` of the deep units, so the two agree. The lower ramification group of
the level at `0` is Phase 5's
`Atlas.Knowledge.standardLubinTateLowerRamification_zero_eq_top`, transported.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π) (n d : ℕ)

/-- **The standard compositum** `Tₙ ⊔ K (μ_{q ^ d − 1})` of a Lubin–Tate level closure and
the unramified cyclotomic floor of degree `d` (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/StandardCompositum.lean:30`). -/
noncomputable abbrev standardCompositum : IntermediateField K (AlgebraicClosure K) :=
  standardLubinTateLevelClosure K hπ n ⊔ cycloField K (Nat.card 𝓀[K] ^ d - 1)

instance standardCompositum_finiteDimensional :
    FiniteDimensional K (standardCompositum K hπ n d) :=
  IntermediateField.finiteDimensional_sup _ _

instance standardCompositum_isGalois : IsGalois K (standardCompositum K hπ n d) := ⟨⟩

/- The cyclotomic level is nonzero once `d` is positive. -/
private theorem neZero_level (hd : 0 < d) : NeZero (Nat.card 𝓀[K] ^ d - 1) :=
  ⟨by
    have := Nat.one_lt_pow hd.ne' (Finite.one_lt_card : 1 < Nat.card 𝓀[K])
    omega⟩

/-- The standard compositum is abelian over `K`, as a compositum of two abelian floors. -/
theorem standardCompositum_isAbelianGalois (hd : 0 < d) :
    IsAbelianGalois K (standardCompositum K hπ n d) := by
  haveI := neZero_level K d hd
  exact isAbelianGalois_sup

local notation "𝔽" => standardCompositum K hπ n d
local notation "𝕋n" => standardLubinTateLevelClosure K hπ n
set_option quotPrecheck false in
local notation "𝔼" => cycloField K (Nat.card 𝓀[K] ^ d - 1)
set_option quotPrecheck false in
local notation "𝕌" => MonoidHom.range (Units.map (𝒪[K].subtype : ↥𝒪[K] →* K))

/-- **Filtered reciprocity on the standard compositum**, `t > 0`: the Artin image of `U^t` is
`G^t (F/K)` — both lie in the kernel of restriction to the cyclotomic factor, on which
restriction to the level is injective, and both restrict to the level's `G^t`
([Serre 1979, Chap. XV, §2, Thm. 2, p.228][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/Compositum.lean:27`). -/
theorem map_realHigherUnitGroup_standardCompositum (hd : 0 < d) (ρ : Kˣ →* (𝔽 ≃ₐ[K] 𝔽))
    (hρ : IsArtinRestriction K 𝔽 ρ) {t : ℝ} (ht : 0 < t) :
    Subgroup.map ρ (realHigherUnitGroup K t) = upperRamificationGroup K 𝔽 t := by
  haveI := neZero_level K d hd
  haveI := standardCompositum_isAbelianGalois K hπ n d hd
  have hleT : 𝕋n ≤ 𝔽 := le_sup_left
  have hleE : 𝔼 ≤ 𝔽 := le_sup_right
  have hρT := hρ.intermediateFieldRestrict K hleT
  -- the two restrictions are jointly injective
  have hker : (intermediateFieldRestrictNormalHom 𝔼 𝔽 hleE).ker ⊓
      (intermediateFieldRestrictNormalHom 𝕋n 𝔽 hleT).ker = ⊥ := by
    rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    exact intermediateFieldRestrictNormalHom_sup_eq_one
      (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hσ).2)
      (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hσ).1)
  -- both sides lie in the kernel of restriction to the unramified factor
  have hA : Subgroup.map ρ (realHigherUnitGroup K t) ≤
      (intermediateFieldRestrictNormalHom 𝔼 𝔽 hleE).ker := by
    rw [← hρ.map_normRange_eq_ker K hleE]
    apply Subgroup.map_mono
    rw [cycloField_normRange K hd]
    intro x hx
    rw [Subgroup.mem_comap]
    have hv : x ∈ (normalizedValuationHom K).ker := higherUnitGroup_le_ker K _ hx
    rw [MonoidHom.mem_ker] at hv
    rw [hv]
    exact Subgroup.one_mem _
  have hB : upperRamificationGroup K 𝔽 t ≤ (intermediateFieldRestrictNormalHom 𝔼 𝔽 hleE).ker :=
    upperRamificationGroup_le_ker_intermediateFieldRestrictNormalHom K hleE
      (cycloField_upperRamificationGroup_eq_bot K hd ht.le)
  -- and have the same image at the level
  have himg : (Subgroup.map ρ (realHigherUnitGroup K t)).map
        (intermediateFieldRestrictNormalHom 𝕋n 𝔽 hleT) =
      (upperRamificationGroup K 𝔽 t).map (intermediateFieldRestrictNormalHom 𝕋n 𝔽 hleT) := by
    rw [Subgroup.map_map, map_upperRamificationGroup_intermediateFieldRestrictNormalHom K hleT t]
    exact map_realHigherUnitGroup_standardLubinTateLevelClosure K hπ n _ hρT ht
  exact subgroup_eq_of_map_eq_of_le hA hB hker himg

/-- **The inertia endpoint on the standard compositum**: the Artin image of the full unit
group `U^0` is `G^0 (F/K)` — both are the kernel of restriction to the cyclotomic factor, the
Artin side as the image of `U^0 ⊔ N (F) = N (K (μ))`, the Galois side by the count against
the level's Galois group ([Serre 1979, Chap. XIII, §4, Cor. to Prop. 13, p.198][Serre1979]). -/
theorem map_units_standardCompositum (hd : 0 < d) (ρ : Kˣ →* (𝔽 ≃ₐ[K] 𝔽))
    (hρ : IsArtinRestriction K 𝔽 ρ) :
    Subgroup.map ρ 𝕌 = upperRamificationGroup K 𝔽 0 := by
  haveI := neZero_level K d hd
  haveI := standardCompositum_isAbelianGalois K hπ n d hd
  have hleT : 𝕋n ≤ 𝔽 := le_sup_left
  have hleE : 𝔼 ≤ 𝔽 := le_sup_right
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  set πu := standardLubinTateUniformizerUnit K hπ with hπu
  have hπv : normalizedValuation K πu = 1 := normalizedValuation_irreducible K π hπ πu rfl
  have hNE : localNormSubgroup K 𝔼 = Subgroup.comap (normalizedValuationHom K)
      (Subgroup.zpowers (Multiplicative.ofAdd (d : ℤ))) := cycloField_localNormSubgroup K hd
  have hNT : localNormSubgroup K 𝕋n =
      Subgroup.zpowers πu ⊔ higherUnitGroup K ⟨n + 1, Nat.succ_pos n⟩ :=
    standardLubinTateLevelClosure_localNormSubgroup K hπ n
  have hNF : localNormSubgroup K 𝔽 = localNormSubgroup K 𝕋n ⊓ localNormSubgroup K 𝔼 :=
    localNormSubgroup_sup K 𝕋n 𝔼
  have hU : 𝕌 = (normalizedValuationHom K).ker := range_units_map_subtype_eq_ker K
  have hUE : 𝕌 ≤ localNormSubgroup K 𝔼 := by
    rw [hU, hNE]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap, hx]
    exact Subgroup.one_mem _
  -- `π ^ d` is a norm from the compositum
  have hπd : πu ^ (d : ℤ) ∈ localNormSubgroup K 𝔽 := by
    rw [hNF]
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [hNT]
      exact Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ _)
    · rw [hNE, Subgroup.mem_comap, Subgroup.mem_zpowers_iff]
      refine ⟨1, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [toAdd_zpow, toAdd_ofAdd, toAdd_normalizedValuationHom, normalizedValuation_zpow, hπv]
      simp
  -- the units together with the norms of the compositum are the norms of the unramified factor
  have hsup : 𝕌 ⊔ localNormSubgroup K 𝔽 = localNormSubgroup K 𝔼 := by
    apply le_antisymm (sup_le hUE (localNormSubgroup_le_of_le K hleE))
    intro x hx
    rw [hNE, Subgroup.mem_comap, Subgroup.mem_zpowers_iff] at hx
    obtain ⟨k, hk⟩ := hx
    have hvx : normalizedValuation K x = (d : ℤ) * k := by
      have := congrArg Multiplicative.toAdd hk
      rw [toAdd_zpow, toAdd_ofAdd, toAdd_normalizedValuationHom, smul_eq_mul] at this
      rw [← this, mul_comm]
    have hu : x * (πu ^ (d : ℤ)) ^ (-k) ∈ 𝕌 := by
      rw [hU, MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      rw [toAdd_normalizedValuationHom, toAdd_one, normalizedValuation_mul,
        normalizedValuation_zpow, normalizedValuation_zpow, hπv, hvx]
      ring
    have hx' : x = (x * (πu ^ (d : ℤ)) ^ (-k)) * (πu ^ (d : ℤ)) ^ k := by
      rw [mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]
    rw [hx']
    exact Subgroup.mul_mem_sup hu (Subgroup.zpow_mem _ hπd k)
  -- the Artin side is the kernel of restriction to the unramified factor
  have hArt : Subgroup.map ρ 𝕌 = (intermediateFieldRestrictNormalHom 𝔼 𝔽 hleE).ker := by
    rw [← hρ.map_normRange_eq_ker K hleE]
    change _ = Subgroup.map ρ (localNormSubgroup K 𝔼)
    have hbot : Subgroup.map ρ (localNormSubgroup K 𝔽) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hρ.ker]
      exact le_rfl
    rw [← hsup, Subgroup.map_sup, hbot, sup_bot_eq]
  -- the Galois side lies in that kernel
  have hGle := upperRamificationGroup_le_ker_intermediateFieldRestrictNormalHom K hleE
    (cycloField_upperRamificationGroup_eq_bot K hd le_rfl)
  -- and is at least as large as the level's Galois group
  have h1 : (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n ≤
      Nat.card (upperRamificationGroup K 𝔽 0) := by
    have hmap := map_upperRamificationGroup_intermediateFieldRestrictNormalHom K hleT 0
    have htop : upperRamificationGroup K 𝕋n 0 = ⊤ := by
      obtain ⟨vL, tL, hVE, _, hMCL⟩ :=
        exists_extension_isMixedCharLocalField K ↥(standardLubinTateLevelField K hπ n)
      letI := vL
      letI := tL
      haveI := hVE
      haveI := hMCL
      rw [upperRamificationGroup_zero,
        ← lowerRamificationGroup_map_autCongr K (standardLubinTateLevelClosureEquiv K hπ n) 0,
        standardLubinTateLowerRamification_zero_eq_top,
        Subgroup.map_top_of_surjective _ (AlgEquiv.autCongr _).surjective]
    have hcardT : Nat.card (upperRamificationGroup K 𝕋n 0) =
        (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
      rw [htop, Subgroup.card_top, IsGalois.card_aut_eq_finrank,
        standardLubinTateLevelClosure_finrank]
    have hle : Nat.card (Subgroup.map (intermediateFieldRestrictNormalHom 𝕋n 𝔽 hleT)
        (upperRamificationGroup K 𝔽 0)) ≤ Nat.card (upperRamificationGroup K 𝔽 0) :=
      Nat.card_le_card_of_surjective
        (fun h : upperRamificationGroup K 𝔽 0 =>
          (⟨_, ⟨h, h.2, rfl⟩⟩ : Subgroup.map (intermediateFieldRestrictNormalHom 𝕋n 𝔽 hleT)
            (upperRamificationGroup K 𝔽 0)))
        (by rintro ⟨_, h, hh, rfl⟩; exact ⟨⟨h, hh⟩, rfl⟩)
    rw [hmap, hcardT] at hle
    exact hle
  -- while the Artin side is at most the index of the deep units
  have h2 : Nat.card (Subgroup.map ρ 𝕌) ≤ (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
    have hrange : Subgroup.map ρ 𝕌 =
        (ρ.comp (Units.map (𝒪[K].subtype : ↥𝒪[K] →* K))).range := by
      rw [MonoidHom.range_comp]
    rw [hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv,
      ← Subgroup.index_eq_card]
    have hker : integerHigherUnitGroup K (n + 1) ≤
        (ρ.comp (Units.map (𝒪[K].subtype : ↥𝒪[K] →* K))).ker := by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hρ.ker]
      change _ ∈ localNormSubgroup K 𝔽
      rw [hNF]
      refine Subgroup.mem_inf.2 ⟨?_, hUE ⟨u, rfl⟩⟩
      rw [hNT]
      apply Subgroup.mem_sup_right
      rw [← map_integerHigherUnitGroup_eq_higherUnitGroup K (n + 1) (Nat.succ_ne_zero n)]
      exact ⟨u, hu, rfl⟩
    haveI : Finite (𝒪[K]ˣ ⧸ integerHigherUnitGroup K (n + 1)) :=
      Nat.finite_of_card_ne_zero (by
        rw [integerHigherUnitCount K (n + 1) (Nat.succ_ne_zero n)]
        exact Nat.mul_ne_zero (by omega) (Nat.pow_pos (by omega)).ne')
    haveI : (integerHigherUnitGroup K (n + 1)).FiniteIndex :=
      Subgroup.finiteIndex_of_finite_quotient
    calc (ρ.comp (Units.map (𝒪[K].subtype : ↥𝒪[K] →* K))).ker.index
        ≤ (integerHigherUnitGroup K (n + 1)).index := Subgroup.index_antitone hker
      _ = Nat.card (𝒪[K]ˣ ⧸ integerHigherUnitGroup K (n + 1)) := Subgroup.index_eq_card _
      _ = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
        rw [integerHigherUnitCount K (n + 1) (Nat.succ_ne_zero n)]
        simp
  rw [hArt] at h2 ⊢
  exact (Subgroup.eq_of_le_of_card_ge hGle (h2.trans h1)).symm

end Atlas.Knowledge
