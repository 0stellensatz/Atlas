import Mathlib
import Atlas.Knowledge.FiniteAbelianSubfieldOrder
import Atlas.Knowledge.FiniteNormQuotientEquivNormQuotient
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IntegerHigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.RamificationGroupAutCongr
import Atlas.Knowledge.StandardLubinTateGaloisDescription
import Atlas.Knowledge.StandardLubinTateLevelField
import Atlas.Knowledge.StandardLubinTateNormSubgroup
import Atlas.Knowledge.StandardLubinTateUniformizerUnit
import Atlas.Knowledge.StandardLubinTateUpperRamification
import Atlas.Knowledge.UpperRamificationGroup

/-!
# standard Lubin–Tate level closure

The standard Lubin–Tate level field `Lₙ = K (π-torsion of level n + 1)` of
`Atlas.Knowledge.StandardLubinTateLevelField` lives in the separable closure; the reciprocity
predicate `Atlas.Knowledge.IsArtinRestriction` lives in the algebraic closure. This item
carries the level field across — its range under the inclusion of the separable closure — and
reads Phase 5's results there: the degree `(q − 1) qⁿ`, the norm subgroup `⟨π⟩ ⊔ U^{n+1}`,
the orders `q^{n+1−k}` of the upper ramification groups at the integers `1 ≤ k ≤ n + 1`, and
the natural-ceiling constancy of the upper filtration on the visible range. It adds the one
fact Phase 5 does not state: the levels form a tower, `Tₘ ≤ Tₙ` for `m ≤ n`, which follows
from the norm subgroups through the order reversal — no torsion argument, and no dependence
on which primitive root each level was built on.

## Main definitions

* `standardLubinTateLevelClosure` — the level field as a subfield of the algebraic closure.
* `standardLubinTateLevelClosureEquiv` — the identification with the level field.

## Main statements

* `standardLubinTateLevelClosure_finrank` — degree `(q − 1) qⁿ`.
* `standardLubinTateLevelClosure_localNormSubgroup` — norm subgroup `⟨π⟩ ⊔ U^{n+1}`.
* `card_upperRamificationGroup_standardLubinTateLevelClosure` — `#G^k = q^{n+1−k}`.
* `upperRamificationGroup_standardLubinTateLevelClosure_natCeil` — `G^t = G^{⌈t⌉₊}` on the
  visible range.
* `standardLubinTateLevelClosure_le` — the tower.

## Implementation notes

The ramification statements are Phase 5's, transported by
`Atlas.Knowledge.RamificationGroupAutCongr` along the identification; the norm subgroup is
`Atlas.Knowledge.localNormSubgroup_fieldRange_eq` on
`Atlas.Knowledge.standardLubinTateNormSubgroup_eq`, its integer unit level read in `Kˣ` by
`Atlas.Knowledge.map_integerHigherUnitGroup_eq_higherUnitGroup`. The tower is
`Atlas.Knowledge.finiteAbelian_le_iff_localNormSubgroup_le` on the containment
`⟨π⟩ ⊔ U^{n+1} ≤ ⟨π⟩ ⊔ U^{m+1}`. The base field is bound in one universe with the level
field, as the norm-subgroup dictionary requires.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ)

/-- **The standard Lubin–Tate level closure**: the level field `Lₙ` carried into the
algebraic closure as the range of the inclusion of the separable closure
([Milne 2020, Chap. I, §3, Thm. 3.6, p.38][MilneCFT]). -/
noncomputable def standardLubinTateLevelClosure : IntermediateField K (AlgebraicClosure K) :=
  AlgHom.fieldRange ((separableClosure K (AlgebraicClosure K)).val.comp
    (standardLubinTateLevelField K hπ n).val)

/-- The identification of the level field with its closure. -/
noncomputable def standardLubinTateLevelClosureEquiv :
    standardLubinTateLevelField K hπ n ≃ₐ[K] standardLubinTateLevelClosure K hπ n :=
  AlgEquiv.ofInjectiveField _

/-- The level closure is finite over `K`, through its identification with the level field. -/
instance standardLubinTateLevelClosure_finiteDimensional :
    FiniteDimensional K (standardLubinTateLevelClosure K hπ n) :=
  (standardLubinTateLevelClosureEquiv K hπ n).toLinearEquiv.finiteDimensional

/-- The level closure is abelian over `K`, transported from the level field along the
identification. -/
instance standardLubinTateLevelClosure_isAbelianGalois :
    IsAbelianGalois K (standardLubinTateLevelClosure K hπ n) := by
  haveI := standardLubinTateLevelField_isAbelianGalois K hπ n
  exact IsAbelianGalois.of_algHom (standardLubinTateLevelClosureEquiv K hπ n).symm.toAlgHom

/-- The level closure has degree `(q − 1) qⁿ`
([Milne 2020, Chap. I, §3, Thm. 3.6 (a), p.38][MilneCFT]). -/
theorem standardLubinTateLevelClosure_finrank :
    Module.finrank K (standardLubinTateLevelClosure K hπ n) =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
  rw [← (standardLubinTateLevelClosureEquiv K hπ n).toLinearEquiv.finrank_eq]
  exact standardLubinTateLevelField_finrank (A := ↥𝒪[K]) (K := K) hπ n

/-- **The norm subgroup of the level closure** is `⟨π⟩ ⊔ U^{n+1}`
([Milne 2020, Chap. I, §1, p.25][MilneCFT]). -/
theorem standardLubinTateLevelClosure_localNormSubgroup :
    localNormSubgroup K (standardLubinTateLevelClosure K hπ n) =
      Subgroup.zpowers (standardLubinTateUniformizerUnit K hπ) ⊔
        higherUnitGroup K ⟨n + 1, Nat.succ_pos n⟩ := by
  rw [standardLubinTateLevelClosure, localNormSubgroup_fieldRange_eq]
  have h := standardLubinTateNormSubgroup_eq K hπ n
  rw [map_integerHigherUnitGroup_eq_higherUnitGroup K (n + 1) (Nat.succ_ne_zero n)] at h
  exact h.symm

/-- **The order of the upper ramification group at an integer** `1 ≤ k ≤ n + 1` of the level
closure is `q^{n+1−k}` ([Serre 1979, Chap. XV, §2, Thm. 2 and Rem., p.228][Serre1979]). -/
theorem card_upperRamificationGroup_standardLubinTateLevelClosure {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n + 1) :
    Nat.card (upperRamificationGroup K (standardLubinTateLevelClosure K hπ n) (k : ℝ)) =
      Nat.card 𝓀[K] ^ (n + 1 - k) := by
  rw [card_upperRamificationGroup_autCongr K (standardLubinTateLevelClosureEquiv K hπ n)]
  exact standardLubinTateUpperRamification_natCard K hπ n k hk hkn

/-- On the visible range the upper filtration of the level closure is constant on the
natural-ceiling steps ([Serre 1979, Chap. XV, §2, Thm. 2 and Rem., p.228][Serre1979]). -/
theorem upperRamificationGroup_standardLubinTateLevelClosure_natCeil (t : ℝ) (h1 : 1 ≤ ⌈t⌉₊)
    (hn : ⌈t⌉₊ ≤ n + 1) :
    upperRamificationGroup K (standardLubinTateLevelClosure K hπ n) t =
      upperRamificationGroup K (standardLubinTateLevelClosure K hπ n) (⌈t⌉₊ : ℝ) := by
  rw [← upperRamificationGroup_map_autCongr K (standardLubinTateLevelClosureEquiv K hπ n) t,
    ← upperRamificationGroup_map_autCongr K (standardLubinTateLevelClosureEquiv K hπ n) _,
    standardLubinTateUpperRamification K hπ n t h1 hn]

/-- **The levels form a tower**: `Tₘ ≤ Tₙ` for `m ≤ n`, by the order reversal on the norm
subgroups `⟨π⟩ ⊔ U^{n+1} ≤ ⟨π⟩ ⊔ U^{m+1}`
([Milne 2020, Chap. I, §1, Cor. 1.2 (b), p.20][MilneCFT]). -/
theorem standardLubinTateLevelClosure_le {m : ℕ} (hmn : m ≤ n) :
    standardLubinTateLevelClosure K hπ m ≤ standardLubinTateLevelClosure K hπ n := by
  rw [finiteAbelian_le_iff_localNormSubgroup_le, standardLubinTateLevelClosure_localNormSubgroup,
    standardLubinTateLevelClosure_localNormSubgroup]
  exact sup_le_sup_left
    (higherUnitGroup_antitone K (Subtype.mk_le_mk.2 (Nat.succ_le_succ hmn))) _

end Atlas.Knowledge
