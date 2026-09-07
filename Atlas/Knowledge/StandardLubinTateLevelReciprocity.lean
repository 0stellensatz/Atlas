import Mathlib
import Atlas.Knowledge.ArtinRestrictionNormQuotient
import Atlas.Knowledge.ArtinRestrictionSubfloor
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IntermediateFieldRestrictionKernel
import Atlas.Knowledge.IntermediateFieldRestrictNormalHom
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.RealHigherUnitGroup
import Atlas.Knowledge.StandardLubinTateLevelClosure
import Atlas.Knowledge.StandardLubinTateUniformizerUnit
import Atlas.Knowledge.UpperRamificationGroup
import Atlas.Knowledge.UpperRamificationGroupSubfloor

/-!
# filtered reciprocity on a Lubin–Tate level

The ramification compatibility of the Artin map on the standard Lubin–Tate level closure `Tₙ`
of `Atlas.Knowledge.StandardLubinTateLevelClosure`: the Artin image of the `k`th unit step is
the `k`th upper ramification group for `1 ≤ k ≤ n + 1`, and the real-indexed statement holds
at every `t > 0`. Both sides are the kernel of restriction to the level `T_{k−1}` below: the
Artin image of `U^k` is the image of the norm subgroup `⟨π⟩ ⊔ U^k` of `T_{k−1}`, since `π` is
itself a norm, hence that kernel by `Atlas.Knowledge.ArtinRestrictionSubfloor`; and
`G^k (Tₙ/K)` restricts trivially to `T_{k−1}`, whose `k`th upper group is trivial, and has
the kernel's order `q^{n+1−k}`. No identification of the Artin map with the level character
enters, which is what makes the level case reachable with Phase 5's cardinalities alone.

## Main statements

* `map_higherUnitGroup_standardLubinTateLevelClosure` — `Art (U^k) = G^k (Tₙ/K)`.
* `map_realHigherUnitGroup_standardLubinTateLevelClosure` — `Art (U^t) = G^t (Tₙ/K)` for
  `t > 0`.

## Notation

* `𝕋 k` — `standardLubinTateLevelClosure K hπ k`, the level-`k` closure; a `local notation`,
  scoped to this file.

## Implementation notes

Every step at the concrete level carriers is an instantiation of a lemma stated over abstract
subfields — `Atlas.Knowledge.ArtinRestrictionSubfloor`,
`Atlas.Knowledge.UpperRamificationGroupSubfloor`,
`Atlas.Knowledge.IntermediateFieldRestrictionKernel` — because installing the tower instances
by hand at these carriers and restricting directly overran the kernel's budget. Above the
visible range both sides vanish: `U^t ≤ U^{n+1}` is normic and `G^t ≤ G^{n+1}` is trivial.

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
  {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ)

local notation "𝕋" k => standardLubinTateLevelClosure K hπ k

/-- **Filtered reciprocity at an integer level**: the Artin image of `U^k` on `Tₙ` is
`G^k (Tₙ/K)`, `1 ≤ k ≤ n + 1` — both are the kernel of restriction to `T_{k−1}`
([Serre 1979, Chap. XV, §2, Thm. 2, p.228][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/LubinTateApplication/StandardFilteredArtinComparison.lean:64`, `:115`,
`:377`). -/
theorem map_higherUnitGroup_standardLubinTateLevelClosure
    (ρ : Kˣ →* ((𝕋 n) ≃ₐ[K] (𝕋 n))) (hρ : IsArtinRestriction K (𝕋 n) ρ)
    {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n + 1) :
    Subgroup.map ρ (higherUnitGroup K ⟨k, hk1⟩) =
      upperRamificationGroup K (𝕋 n) (k : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hmn : m ≤ n := by omega
  have hle : (𝕋 m) ≤ (𝕋 n) := standardLubinTateLevelClosure_le K hπ n hmn
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  -- the Artin side is the kernel of restriction
  have hArt' := hρ.map_normRange_eq_ker K hle
  have hNm : (Units.map (Algebra.norm K : (𝕋 m) →* K)).range =
      Subgroup.zpowers (standardLubinTateUniformizerUnit K hπ) ⊔
        higherUnitGroup K ⟨m + 1, Nat.succ_pos m⟩ :=
    standardLubinTateLevelClosure_localNormSubgroup K hπ m
  rw [hNm] at hArt'
  have h1 : Subgroup.map ρ (Subgroup.zpowers (standardLubinTateUniformizerUnit K hπ)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hρ.ker]
    have hNn : (Units.map (Algebra.norm K : (𝕋 n) →* K)).range =
        Subgroup.zpowers (standardLubinTateUniformizerUnit K hπ) ⊔
          higherUnitGroup K ⟨n + 1, Nat.succ_pos n⟩ :=
      standardLubinTateLevelClosure_localNormSubgroup K hπ n
    rw [hNn]
    exact le_sup_left
  have hArt : Subgroup.map ρ (higherUnitGroup K ⟨m + 1, hk1⟩) =
      (intermediateFieldRestrictNormalHom (𝕋 m) (𝕋 n) hle).ker := by
    rw [← hArt', Subgroup.map_sup, h1, bot_sup_eq]
  -- the Galois side lies in the kernel of restriction and has its order
  have hbot : upperRamificationGroup K (𝕋 m) ((m + 1 : ℕ) : ℝ) = ⊥ := by
    apply Subgroup.eq_bot_of_card_eq
    rw [card_upperRamificationGroup_standardLubinTateLevelClosure K hπ m hk1 le_rfl]
    simp
  have hGle := upperRamificationGroup_le_ker_intermediateFieldRestrictNormalHom K hle hbot
  have hcardG : Nat.card (upperRamificationGroup K (𝕋 n) ((m + 1 : ℕ) : ℝ)) =
      Nat.card 𝓀[K] ^ (n - m) := by
    rw [card_upperRamificationGroup_standardLubinTateLevelClosure K hπ n hk1 hkn]
    congr 1
    omega
  have hcardK : Nat.card (intermediateFieldRestrictNormalHom (𝕋 m) (𝕋 n) hle).ker =
      Nat.card 𝓀[K] ^ (n - m) := by
    have h := card_ker_intermediateFieldRestrictNormalHom hle
    rw [standardLubinTateLevelClosure_finrank, standardLubinTateLevelClosure_finrank] at h
    have hpos : 0 < (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ m :=
      Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
    have hsplit : (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n =
        Nat.card 𝓀[K] ^ (n - m) * ((Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ m) := by
      rw [mul_comm (Nat.card 𝓀[K] ^ (n - m)), mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]
    rw [hsplit] at h
    exact Nat.eq_of_mul_eq_mul_right hpos h
  rw [hArt]
  exact (Subgroup.eq_of_le_of_card_ge hGle (by rw [hcardG, hcardK])).symm

/-- **Filtered reciprocity at every positive real index on a level**:
`Art (U^t) = G^t (Tₙ/K)` for `t > 0` — the integer case at `⌈t⌉₊` on the visible range, both
sides trivial above it ([Serre 1979, Chap. XV, §2, Thm. 2, p.228][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/LubinTateApplication/StandardFixedFieldComparison.lean:47`). -/
theorem map_realHigherUnitGroup_standardLubinTateLevelClosure
    (ρ : Kˣ →* ((𝕋 n) ≃ₐ[K] (𝕋 n))) (hρ : IsArtinRestriction K (𝕋 n) ρ)
    {t : ℝ} (ht : 0 < t) :
    Subgroup.map ρ (realHigherUnitGroup K t) = upperRamificationGroup K (𝕋 n) t := by
  have hc1 : 1 ≤ ⌈t⌉₊ := Nat.ceil_pos.2 ht
  have hreal : realHigherUnitGroup K t = higherUnitGroup K ⟨⌈t⌉₊, hc1⟩ :=
    realHigherUnitGroup_eq K (n := ⟨⌈t⌉₊, hc1⟩)
      (by rw [PNat.mk_coe]; linarith [Nat.ceil_lt_add_one ht.le])
      (by rw [PNat.mk_coe]; exact_mod_cast Nat.le_ceil t)
  rw [hreal]
  by_cases hkn : ⌈t⌉₊ ≤ n + 1
  · rw [upperRamificationGroup_standardLubinTateLevelClosure_natCeil K hπ n t hc1 hkn]
    exact map_higherUnitGroup_standardLubinTateLevelClosure K hπ n ρ hρ hc1 hkn
  · push Not at hkn
    have hNn : (Units.map (Algebra.norm K : (𝕋 n) →* K)).range =
        Subgroup.zpowers (standardLubinTateUniformizerUnit K hπ) ⊔
          higherUnitGroup K ⟨n + 1, Nat.succ_pos n⟩ :=
      standardLubinTateLevelClosure_localNormSubgroup K hπ n
    have hU : higherUnitGroup K ⟨⌈t⌉₊, hc1⟩ ≤ higherUnitGroup K ⟨n + 1, Nat.succ_pos n⟩ :=
      higherUnitGroup_antitone K (Subtype.mk_le_mk.2 hkn.le)
    have hleft : Subgroup.map ρ (higherUnitGroup K ⟨⌈t⌉₊, hc1⟩) = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hρ.ker, hNn]
      exact hU.trans le_sup_right
    have hright : upperRamificationGroup K (𝕋 n) t = ⊥ := by
      apply le_bot_iff.mp
      have h1 : upperRamificationGroup K (𝕋 n) t ≤
          upperRamificationGroup K (𝕋 n) ((n + 1 : ℕ) : ℝ) := by
        apply upperRamificationGroup_antitone
        have h3 := Nat.ceil_lt_add_one ht.le
        have h2 : ((n + 1 : ℕ) : ℝ) + 1 ≤ (⌈t⌉₊ : ℝ) := by exact_mod_cast hkn
        linarith
      have h2 : upperRamificationGroup K (𝕋 n) ((n + 1 : ℕ) : ℝ) = ⊥ := by
        apply Subgroup.eq_bot_of_card_eq
        rw [card_upperRamificationGroup_standardLubinTateLevelClosure K hπ n (by omega) le_rfl]
        simp
      rw [h2] at h1
      exact h1
    rw [hleft, hright]

end Atlas.Knowledge
