import Mathlib
import Atlas.Knowledge.IntegerHigherUnitCount
import Atlas.Knowledge.IntegerIsIntegralClosure
import Atlas.Knowledge.IntegerValuation
import Atlas.Knowledge.NormalizedValuationAlgEquiv
import Atlas.Knowledge.RamificationNumber
import Atlas.Knowledge.RamificationNumberEqAddVal
import Atlas.Knowledge.StandardLubinTateDisplacement
import Atlas.Knowledge.StandardLubinTateGaloisDescription
import Atlas.Knowledge.StandardLubinTateLevelUniformizer
import Atlas.Knowledge.StandardLubinTateTorsion
import Atlas.Knowledge.TotallyRamifiedMonogenic

/-!
# standard Lubin–Tate lower ramification

The lower ramification filtration of a level field, computed: on the interval
`q^(k−1) ≤ r < q^k` the group `G_r` is the image under the level character of the
`k`-th higher unit group, the inertia end `G_0` is everything, and the order at the
break is `q^(n+1−k)`. The engine is the one-rewrite chain assembled by the plumbing
layer — the ramification number read as the value of the generator's displacement —
fed by the displacement spectrum of
`Atlas.Knowledge.integerValuation_standardLubinTateSMul_sub_self` at the level
generator, whose value is one: a character value of exact depth `j ≤ n` has
ramification number `q^j`, a deep one is the identity, and the interval pins the depth.

## Main statements

* `standardLubinTateLowerRamification_eq` — `G_r = σ(U^{(k)})` on the `k`-th power
  interval; proved.
* `standardLubinTateLowerRamification_zero_eq_top` — `G_0` is everything; proved.
* `standardLubinTateLowerRamification_natCard` — order `q^(n+1−k)` on the interval;
  proved.

## Implementation notes

The generator of the integral closure is the level generator pulled back along
`Atlas.Knowledge.integerEquivIntegralClosure`, irreducible by transport, generating by
`Atlas.Knowledge.totallyRamifiedMonogenic` at the level's total-ramification identity —
so the ramification number of any automorphism is the integer valuation of its
displacement of the level generator, through
`Atlas.Knowledge.ramificationNumber_eq_addVal` and the additive-valuation bridges. The
statements are phrased at the hypothesized local-field structure on the level field, as
in `Atlas.Knowledge.StandardLubinTateLevelUniformizer`, and never mention the integral
closure of the concrete carrier; the closure enters only inside proofs, instantiated
wholesale. The card is the relative index of the higher unit groups, carried through
the character's kernel by the first isomorphism theorem.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer
  New York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section LowerRamification

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable {π : ↥𝒪[K]} (hπ : Irreducible π) (n : ℕ)
variable [ValuativeRel ↥(standardLubinTateLevelField K hπ n)]
  [TopologicalSpace ↥(standardLubinTateLevelField K hπ n)]
  [ValuativeExtension K ↥(standardLubinTateLevelField K hπ n)]
  [IsMixedCharLocalField ↥(standardLubinTateLevelField K hπ n)]

/- The level generator, pulled back to the integral closure, generates it: it is
irreducible by transport, and the level's total-ramification identity feeds the
monogenic theorem. -/
private theorem adjoin_levelGenerator_eq_top :
    Algebra.adjoin ↥𝒪[K]
      {(integerEquivIntegralClosure K ↥(standardLubinTateLevelField K hπ n)).symm
        (levelGeneratorInteger K hπ n)} = ⊤ := by
  have hirr : Irreducible
      ((integerEquivIntegralClosure K ↥(standardLubinTateLevelField K hπ n)).symm
        (levelGeneratorInteger K hπ n)) :=
    (levelGeneratorInteger_irreducible K hπ n).map
      (integerEquivIntegralClosure K
        ↥(standardLubinTateLevelField K hπ n)).symm.toMulEquiv
  exact totallyRamifiedMonogenic K ↥(standardLubinTateLevelField K hπ n)
    (map_maximalIdeal_levelField K hπ n) hirr

set_option synthInstance.maxHeartbeats 400000 in
-- the additive-monoid-hom class of the ring isomorphism at the concrete level carrier
-- exceeds the default synthesis budget
/- The ramification number of any automorphism is the value of its displacement of the
level generator — the one-rewrite chain of the plumbing layer, instantiated. -/
private theorem ramificationNumber_eq_integerValuation
    (σ : ↥(standardLubinTateLevelField K hπ n) ≃ₐ[K]
      ↥(standardLubinTateLevelField K hπ n))
    (hne : algEquivIntegerRestrict K ↥(standardLubinTateLevelField K hπ n) σ
        (levelGeneratorInteger K hπ n) - levelGeneratorInteger K hπ n ≠ 0) :
    ramificationNumber K ↥(standardLubinTateLevelField K hπ n) σ =
      ((integerValuation ↥(standardLubinTateLevelField K hπ n)
        (algEquivIntegerRestrict K ↥(standardLubinTateLevelField K hπ n) σ
          (levelGeneratorInteger K hπ n) -
            levelGeneratorInteger K hπ n)).toNat : ℕ∞) := by
  set e := integerEquivIntegralClosure K ↥(standardLubinTateLevelField K hπ n) with he
  rw [ramificationNumber_eq_addVal K ↥(standardLubinTateLevelField K hπ n)
      (adjoin_levelGenerator_eq_top K hπ n) σ,
    ← RamificationNumberEqAddVal.addVal_ringEquiv e,
    map_sub, integerEquivIntegralClosure_galRestrict,
    RingEquiv.apply_symm_apply,
    addVal_eq_toNat_integerValuation ↥(standardLubinTateLevelField K hπ n) hne]

set_option synthInstance.maxHeartbeats 400000 in
-- the chain lemma's rewrite works at the same concrete carrier and inherits its budget
/- A character value of exact depth `j ≤ n` has ramification number `q^j`: the
displacement spectrum at the level generator, whose value is one. -/
private theorem ramificationNumber_levelCharacter {u : 𝒪[K]ˣ} {j : ℕ} (hjn : j ≤ n)
    {w : ↥𝒪[K]} (hw : IsUnit w) (hju : (u : ↥𝒪[K]) - 1 = π ^ j * w) :
    ramificationNumber K ↥(standardLubinTateLevelField K hπ n)
        (levelCharacter K hπ n u) =
      ((Nat.card 𝓀[K] : ℕ) ^ j : ℕ∞) := by
  have hgenmem := mem_maximalIdeal_of_aeval_primitive K
    ↥(standardLubinTateLevelField K hπ n) hπ (aeval_levelGeneratorInteger K hπ n)
  have hspec := integerValuation_standardLubinTateSMul_sub_self K
    ↥(standardLubinTateLevelField K hπ n) hπ hgenmem
    (aeval_levelGeneratorInteger K hπ n) hjn hw hju
  rw [integerValuation_levelGeneratorInteger K hπ n, mul_one] at hspec
  have hact := algEquivIntegerRestrict_levelCharacter K hπ n u
  have hq1 : (1 : ℤ) ≤ (Nat.card 𝓀[K] : ℤ) := by
    exact_mod_cast le_of_lt (Finite.one_lt_card : 1 < Nat.card 𝓀[K])
  have hne : algEquivIntegerRestrict K ↥(standardLubinTateLevelField K hπ n)
      (levelCharacter K hπ n u) (levelGeneratorInteger K hπ n) -
        levelGeneratorInteger K hπ n ≠ 0 := by
    rw [hact]
    intro h0
    rw [h0, integerValuation_zero] at hspec
    have hpos : (0 : ℤ) < (Nat.card 𝓀[K] : ℤ) ^ j := pow_pos (by omega) j
    omega
  rw [ramificationNumber_eq_integerValuation K hπ n _ hne, hact, hspec]
  norm_cast

/- A deep character value is the identity, of infinite ramification number. -/
private theorem ramificationNumber_levelCharacter_of_mem {u : 𝒪[K]ˣ}
    (hu : u ∈ integerHigherUnitGroup K (n + 1)) :
    ramificationNumber K ↥(standardLubinTateLevelField K hπ n)
      (levelCharacter K hπ n u) = ⊤ := by
  have h1 : levelCharacter K hπ n u = 1 := by
    rw [← MonoidHom.mem_ker, levelCharacter_ker]
    exact hu
  rw [h1]
  exact (ramificationNumber_eq_top_iff K
    ↥(standardLubinTateLevelField K hπ n)).mpr rfl

include hπ in
/- A unit-times-power lies in the `k`-th power of the maximal ideal exactly when the
exponent reaches `k`. -/
private theorem pow_mul_unit_mem_maximalIdeal_pow_iff {j k : ℕ} {w : ↥𝒪[K]}
    (hw : IsUnit w) :
    π ^ j * w ∈ (𝓂[K] ^ k : Ideal ↥𝒪[K]) ↔ k ≤ j := by
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  constructor
  · rintro ⟨c, hc⟩
    by_contra hlt
    have hjk : j < k := by omega
    have h1 : π ^ j * w = π ^ j * (π ^ (k - j) * c) := by
      rw [hc, ← mul_assoc, ← pow_add]
      congr 2
      omega
    have h2 : w = π ^ (k - j) * c := mul_left_cancel₀ (pow_ne_zero _ hπ.ne_zero) h1
    have hdvd : π ∣ w := by
      refine ⟨π ^ (k - j - 1) * c, ?_⟩
      rw [h2, ← mul_assoc, ← pow_succ']
      congr 2
      omega
    exact hπ.not_isUnit (isUnit_of_dvd_unit hdvd hw)
  · intro hkj
    exact ⟨π ^ (j - k) * w, by rw [← mul_assoc, ← pow_add]; congr 2; omega⟩

set_option synthInstance.maxHeartbeats 400000 in
-- the character-value rewrites work at the same concrete carrier as the chain
/- The interval membership: a character value lies in `G_r` on the `k`-th power
interval exactly when its parameter is a `k`-th higher unit. -/
private theorem levelCharacter_mem_lowerRamificationGroup_iff {u : 𝒪[K]ˣ} {k r : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n + 1)
    (hr1 : Nat.card 𝓀[K] ^ (k - 1) ≤ r) (hr2 : r < Nat.card 𝓀[K] ^ k) :
    levelCharacter K hπ n u ∈
        lowerRamificationGroup K ↥(standardLubinTateLevelField K hπ n) (r : ℤ) ↔
      u ∈ integerHigherUnitGroup K k := by
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hidx : levelCharacter K hπ n u ∈
      lowerRamificationGroup K ↥(standardLubinTateLevelField K hπ n) (r : ℤ) ↔
      ((r + 1 : ℕ) : ℕ∞) ≤ ramificationNumber K
        ↥(standardLubinTateLevelField K hπ n) (levelCharacter K hπ n u) := by
    rw [show (r : ℤ) = ((r + 1 : ℕ) : ℤ) - 1 by push_cast; ring,
      mem_lowerRamificationGroup_sub_one_iff]
  rw [hidx]
  rcases eq_or_ne ((u : ↥𝒪[K]) - 1) 0 with h0 | hne0
  · have hu1 : u ∈ integerHigherUnitGroup K (n + 1) := by
      change (u : ↥𝒪[K]) - 1 ∈ (𝓂[K] ^ (n + 1) : Ideal ↥𝒪[K])
      rw [h0]
      exact zero_mem _
    constructor
    · intro _
      change (u : ↥𝒪[K]) - 1 ∈ (𝓂[K] ^ k : Ideal ↥𝒪[K])
      rw [h0]
      exact zero_mem _
    · intro _
      rw [ramificationNumber_levelCharacter_of_mem K hπ n hu1]
      exact le_top
  · obtain ⟨j, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne0 hπ
    have hju : (u : ↥𝒪[K]) - 1 = π ^ j * (w : ↥𝒪[K]) := by rw [hw]; ring
    have hmemk : u ∈ integerHigherUnitGroup K k ↔ k ≤ j := by
      change (u : ↥𝒪[K]) - 1 ∈ (𝓂[K] ^ k : Ideal ↥𝒪[K]) ↔ k ≤ j
      rw [hju, pow_mul_unit_mem_maximalIdeal_pow_iff K hπ w.isUnit]
    rcases le_or_gt (n + 1) j with hdeep | hjn
    · have hu1 : u ∈ integerHigherUnitGroup K (n + 1) := by
        change (u : ↥𝒪[K]) - 1 ∈ (𝓂[K] ^ (n + 1) : Ideal ↥𝒪[K])
        rw [hju, pow_mul_unit_mem_maximalIdeal_pow_iff K hπ w.isUnit]
        exact hdeep
      rw [ramificationNumber_levelCharacter_of_mem K hπ n hu1, hmemk]
      simp only [le_top, true_iff]
      omega
    · have hjn' : j ≤ n := by omega
      rw [ramificationNumber_levelCharacter K hπ n hjn' w.isUnit hju, hmemk,
        ← Nat.cast_pow, Nat.cast_le]
      constructor
      · intro hle
        by_contra hlt
        have hjk : j ≤ k - 1 := by omega
        have hmono : Nat.card 𝓀[K] ^ j ≤ Nat.card 𝓀[K] ^ (k - 1) :=
          Nat.pow_le_pow_right (by omega) hjk
        omega
      · intro hkj
        have hmono : Nat.card 𝓀[K] ^ k ≤ Nat.card 𝓀[K] ^ j :=
          Nat.pow_le_pow_right (by omega) hkj
        omega

/-- **The lower filtration of a level field**: on the `k`-th power interval
`q^(k−1) ≤ r < q^k`, the ramification group `G_r` is the image under the level
character of the `k`-th higher unit group — Serre's cyclotomic computation, at the
standard Lubin–Tate tower
([Serre 1979, Chap. IV, §4, Prop. 18, pp.78–79][Serre1979] — the cyclotomic case is
the tower over `ℚ_p`;
[Yamaguchi 2026, `LubinTate/FiniteLevel/LowerRamificationFormula.lean:126`]
[Yamaguchi2026]). -/
theorem standardLubinTateLowerRamification_eq {k r : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n + 1)
    (hr1 : Nat.card 𝓀[K] ^ (k - 1) ≤ r) (hr2 : r < Nat.card 𝓀[K] ^ k) :
    lowerRamificationGroup K ↥(standardLubinTateLevelField K hπ n) (r : ℤ) =
      Subgroup.map (levelCharacter K hπ n) (integerHigherUnitGroup K k) := by
  ext σ
  constructor
  · intro hmem
    obtain ⟨u, rfl⟩ := levelCharacter_surjective K hπ n σ
    exact ⟨u, (levelCharacter_mem_lowerRamificationGroup_iff K hπ n
      hk1 hkn hr1 hr2).mp hmem, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact (levelCharacter_mem_lowerRamificationGroup_iff K hπ n
      hk1 hkn hr1 hr2).mpr hu

/-- **The inertia end is everything**: the level field is totally ramified, so `G_0` is
the whole Galois group
([Serre 1979, Chap. IV, §4, Prop. 18, pp.78–79][Serre1979] — the `G_0 = G` line). -/
theorem standardLubinTateLowerRamification_zero_eq_top :
    lowerRamificationGroup K ↥(standardLubinTateLevelField K hπ n) 0 = ⊤ := by
  rw [eq_top_iff]
  intro σ _
  obtain ⟨u, rfl⟩ := levelCharacter_surjective K hπ n σ
  have h1 : (0 : ℤ) = ((1 : ℕ) : ℤ) - 1 := by norm_num
  rw [h1, mem_lowerRamificationGroup_sub_one_iff]
  rcases eq_or_ne ((u : ↥𝒪[K]) - 1) 0 with h0 | hne0
  · have hu1 : u ∈ integerHigherUnitGroup K (n + 1) := by
      change (u : ↥𝒪[K]) - 1 ∈ (𝓂[K] ^ (n + 1) : Ideal ↥𝒪[K])
      rw [h0]
      exact zero_mem _
    rw [ramificationNumber_levelCharacter_of_mem K hπ n hu1]
    exact le_top
  · obtain ⟨j, w, hw⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hne0 hπ
    have hju : (u : ↥𝒪[K]) - 1 = π ^ j * (w : ↥𝒪[K]) := by rw [hw]; ring
    rcases le_or_gt (n + 1) j with hdeep | hjn
    · have hu1 : u ∈ integerHigherUnitGroup K (n + 1) := by
        change (u : ↥𝒪[K]) - 1 ∈ (𝓂[K] ^ (n + 1) : Ideal ↥𝒪[K])
        rw [hju, pow_mul_unit_mem_maximalIdeal_pow_iff K hπ w.isUnit]
        exact hdeep
      rw [ramificationNumber_levelCharacter_of_mem K hπ n hu1]
      exact le_top
    · have hjn' : j ≤ n := by omega
      rw [ramificationNumber_levelCharacter K hπ n hjn' w.isUnit hju]
      have hq1 : 1 ≤ Nat.card 𝓀[K] ^ j := Nat.one_le_pow _ _
        (by have := (Finite.one_lt_card : 1 < Nat.card 𝓀[K]); omega)
      exact_mod_cast hq1

/- The index of a higher unit group is the ambient quotient count, in index form. -/
private theorem integerHigherUnitGroup_index {m : ℕ} (hm : m ≠ 0) :
    (integerHigherUnitGroup K m).index =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (m - 1) :=
  integerHigherUnitCount K m hm

/- The relative index between higher unit levels is the power of the residue count. -/
private theorem integerHigherUnitGroup_relIndex {k : ℕ} (hk1 : 1 ≤ k)
    (hkn : k ≤ n + 1) :
    (integerHigherUnitGroup K (n + 1)).relIndex (integerHigherUnitGroup K k) =
      Nat.card 𝓀[K] ^ (n + 1 - k) := by
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hle : integerHigherUnitGroup K (n + 1) ≤ integerHigherUnitGroup K k := by
    intro v hv
    change (v : ↥𝒪[K]) - 1 ∈ (𝓂[K] ^ k : Ideal ↥𝒪[K])
    exact Ideal.pow_le_pow_right hkn hv
  have hmul := Subgroup.relIndex_mul_index hle
  rw [integerHigherUnitGroup_index K (by omega : (n + 1 : ℕ) ≠ 0),
    integerHigherUnitGroup_index K (by omega : k ≠ 0)] at hmul
  have hpos : 0 < (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (k - 1) :=
    Nat.mul_pos (by omega) (Nat.pow_pos (by omega))
  have hDD : (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (n + 1 - 1) =
      Nat.card 𝓀[K] ^ (n + 1 - k) *
        ((Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (k - 1)) := by
    rw [show Nat.card 𝓀[K] ^ (n + 1 - k) *
        ((Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (k - 1)) =
        (Nat.card 𝓀[K] - 1) *
          (Nat.card 𝓀[K] ^ (k - 1) * Nat.card 𝓀[K] ^ (n + 1 - k)) by ring,
      ← pow_add, show k - 1 + (n + 1 - k) = n + 1 - 1 by omega]
  rw [hDD] at hmul
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

/- The card of a mapped higher unit group: the character's kernel is the deepest level,
so the image is the relative-index quotient. -/
private theorem card_map_levelCharacter {k : ℕ} (hk1 : 1 ≤ k) (hkn : k ≤ n + 1) :
    Nat.card (Subgroup.map (levelCharacter K hπ n) (integerHigherUnitGroup K k)) =
      Nat.card 𝓀[K] ^ (n + 1 - k) := by
  set g := (levelCharacter K hπ n).comp (integerHigherUnitGroup K k).subtype with hg
  have hrange : g.range = Subgroup.map (levelCharacter K hπ n)
      (integerHigherUnitGroup K k) := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : g.ker = (integerHigherUnitGroup K (n + 1)).subgroupOf
      (integerHigherUnitGroup K k) := by
    rw [hg, ← MonoidHom.comap_ker, levelCharacter_ker]
    rfl
  rw [← hrange, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv,
    hker]
  have h1 : Nat.card ((integerHigherUnitGroup K k) ⧸
      (integerHigherUnitGroup K (n + 1)).subgroupOf (integerHigherUnitGroup K k)) =
      (integerHigherUnitGroup K (n + 1)).relIndex (integerHigherUnitGroup K k) :=
    rfl
  rw [h1, integerHigherUnitGroup_relIndex K n hk1 hkn]

/-- **The order at the break**: on the `k`-th power interval the ramification group has
order `q^(n+1−k)` — the relative index of the higher unit levels, carried through the
character's kernel
([Serre 1979, Chap. IV, §4, Prop. 18, pp.78–79][Serre1979] — the `Card = p^v` line of
its proof;
[Yamaguchi 2026, `LubinTate/FiniteLevel/LowerRamificationFormula.lean:145`]
[Yamaguchi2026]). -/
theorem standardLubinTateLowerRamification_natCard {k r : ℕ}
    (hk1 : 1 ≤ k) (hkn : k ≤ n + 1)
    (hr1 : Nat.card 𝓀[K] ^ (k - 1) ≤ r) (hr2 : r < Nat.card 𝓀[K] ^ k) :
    Nat.card (lowerRamificationGroup K
        ↥(standardLubinTateLevelField K hπ n) (r : ℤ)) =
      Nat.card 𝓀[K] ^ (n + 1 - k) := by
  rw [standardLubinTateLowerRamification_eq K hπ n hk1 hkn hr1 hr2]
  exact card_map_levelCharacter K hπ n hk1 hkn

end LowerRamification

end Atlas.Knowledge
