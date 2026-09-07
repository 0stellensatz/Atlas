import Mathlib
import Atlas.Knowledge.ArtinRestrictionAutCongr
import Atlas.Knowledge.ArtinRestrictionSubfloor
import Atlas.Knowledge.ArtinRestrictionTower
import Atlas.Knowledge.CycloField
import Atlas.Knowledge.CycloFieldOfDegree
import Atlas.Knowledge.FiniteAbelianSubfieldOrder
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LocalNormSubgroupExistence
import Atlas.Knowledge.NormIndexAbelian
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.RamificationGroupAutCongr
import Atlas.Knowledge.RealHigherUnitGroup
import Atlas.Knowledge.StandardCompositum
import Atlas.Knowledge.StandardLubinTateLevelClosure
import Atlas.Knowledge.StandardLubinTateUniformizerUnit
import Atlas.Knowledge.StandardOpenSubgroups
import Atlas.Knowledge.UnitsFiniteIndexOpen
import Atlas.Knowledge.UpperRamificationGroup
import Atlas.Knowledge.UpperRamificationGroupSubfloor

/-!
# ramification descent to finite abelian floors

How a statement of the form "the Artin image of a subgroup of `Kˣ` is the upper ramification
group at an index" travels from the standard compositum to every finite abelian floor: every
finite abelian subfield of the closure lies in some standard compositum, because its norm
subgroup contains a standard subgroup `⟨π ^ d⟩ ⊔ U^i`, which contains the compositum's norm
subgroup, and the order reversal turns that around; restriction carries both sides down a
subfloor; and a compatible isomorphism carries them to an abstract floor. The last two are
stated for an arbitrary subgroup and index, so the compatibility at `t > 0` and the inertia
endpoint descend by the same three lines each.

## Main statements

* `exists_le_standardCompositum` — every finite abelian subfield lies in a standard
  compositum.
* `map_eq_upperRamificationGroup_of_le` — descent along a subfloor.
* `map_eq_upperRamificationGroup_of_algEquiv` — transport to an abstract floor.
* `map_realHigherUnitGroup_of_finiteAbelian` / `map_units_of_finiteAbelian` — the two
  statements on every finite abelian subfield of the closure.

## Implementation notes

The embedding is Phase 1's existence input rerun with the compositum named: the norm subgroup
has finite index by `Atlas.Knowledge.normIndexAbelian`, so it is open and contains
`⟨π ^ d⟩ ⊔ U^i` with `d` its index (`Atlas.Knowledge.StandardOpenSubgroups`), and the
compositum of the level `i − 1` with the cyclotomic floor of degree `d` has norm subgroup
inside that by the standard-subgroup intersection of
`Atlas.Knowledge.LocalNormSubgroupExistence`. Descent along a subfloor is the uniqueness of
Artin restrictions against the restricted map, `Subgroup.map_map`, and
`Atlas.Knowledge.UpperRamificationGroupSubfloor`; transport to an abstract floor is
`Atlas.Knowledge.ArtinRestrictionAutCongr` with `Atlas.Knowledge.RamificationGroupAutCongr`,
the injectivity of `Subgroup.map` under an injective map closing.

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

/-- **Every finite abelian subfield of the closure lies in a standard compositum**: its norm
subgroup contains a standard subgroup, which contains the norm subgroup of the compositum of
the corresponding level with the cyclotomic floor of degree its index
([Serre 1979, Chap. XV, §2, Thm. 2, p.228][Serre1979] — the reduction; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/FiniteAbelian.lean:30`). -/
theorem exists_le_standardCompositum (L' : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L'] [IsAbelianGalois K L'] :
    ∃ (π : 𝒪[K]) (hπ : Irreducible π) (n d : ℕ), 0 < d ∧ L' ≤ standardCompositum K hπ n d := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[K])
  have hπ0 : (π : K) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext h0)
  let πu : Kˣ := Units.mk0 (π : K) hπ0
  have hπv : normalizedValuation K πu = 1 := normalizedValuation_irreducible K π hπ πu rfl
  have hunit : standardLubinTateUniformizerUnit K hπ = πu := Units.ext rfl
  haveI hfi : (localNormSubgroup K L').FiniteIndex := by
    haveI : Finite (Kˣ ⧸ localNormSubgroup K L') :=
      Nat.finite_of_card_ne_zero (by
        change Nat.card (Kˣ ⧸ (Units.map (Algebra.norm K : L' →* K)).range) ≠ 0
        rw [normIndexAbelian K L']
        exact Module.finrank_pos.ne')
    exact Subgroup.finiteIndex_of_finite_quotient
  have hopen : IsOpen ((localNormSubgroup K L' : Subgroup Kˣ) : Set Kˣ) :=
    unitsFiniteIndexOpen K _ hfi
  obtain ⟨i, hstd⟩ :=
    exists_zpowers_sup_higherUnitGroup_le_of_isOpen_finiteIndex K (localNormSubgroup K L')
      hopen π hπ
  set d := (localNormSubgroup K L').index with hd_def
  have hd : 0 < d := Nat.pos_of_ne_zero hfi.index_ne_zero
  refine ⟨π, hπ, (i : ℕ) - 1, d, hd, ?_⟩
  haveI := standardCompositum_isAbelianGalois K hπ ((i : ℕ) - 1) d hd
  have hi : (⟨(i : ℕ) - 1 + 1, Nat.succ_pos _⟩ : ℕ+) = i := PNat.eq (Nat.sub_add_cancel i.pos)
  have hNF : localNormSubgroup K (standardCompositum K hπ ((i : ℕ) - 1) d) ≤
      localNormSubgroup K L' := by
    intro x hx
    apply hstd
    have hT : x ∈ Subgroup.zpowers πu ⊔ higherUnitGroup K i := by
      have h := localNormSubgroup_le_of_le K
        (le_sup_left : standardLubinTateLevelClosure K hπ ((i : ℕ) - 1) ≤
          standardCompositum K hπ ((i : ℕ) - 1) d) hx
      have hN : localNormSubgroup K (standardLubinTateLevelClosure K hπ ((i : ℕ) - 1)) =
          Subgroup.zpowers πu ⊔ higherUnitGroup K i := by
        rw [← hunit, ← hi]
        exact standardLubinTateLevelClosure_localNormSubgroup K hπ ((i : ℕ) - 1)
      rwa [hN] at h
    have hE : x ∈ Subgroup.comap (normalizedValuationHom K)
        (Subgroup.zpowers (Multiplicative.ofAdd (d : ℤ))) := by
      have h := localNormSubgroup_le_of_le K
        (le_sup_right : cycloField K (Nat.card 𝓀[K] ^ d - 1) ≤
          standardCompositum K hπ ((i : ℕ) - 1) d) hx
      rwa [cycloField_localNormSubgroup K hd] at h
    exact zpowers_sup_higherUnitGroup_inf_comap_le K πu hπv d i ⟨hT, hE⟩
  exact (finiteAbelian_le_iff_localNormSubgroup_le K L' _).2 hNF

/-- **Descent along a subfloor**: if the Artin image of `S` is the upper group at `v` on
every Artin restriction of `F`, then it is on every Artin restriction of a finite abelian
`E ≤ F` — the subfloor's map is the restricted one, and restriction carries both sides
([Serre 1979, Chap. XIII, §4, Prop. 12, p.197][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/Core.lean:130`). -/
theorem map_eq_upperRamificationGroup_of_le {E F : IntermediateField K (AlgebraicClosure K)}
    [FiniteDimensional K F] [IsAbelianGalois K F] [FiniteDimensional K E] [IsAbelianGalois K E]
    (hle : E ≤ F) (S : Subgroup Kˣ) (v : ℝ)
    (hF : ∀ ρF : Kˣ →* (F ≃ₐ[K] F), IsArtinRestriction K F ρF →
      Subgroup.map ρF S = upperRamificationGroup K F v)
    (ρ : Kˣ →* (E ≃ₐ[K] E)) (hρ : IsArtinRestriction K E ρ) :
    Subgroup.map ρ S = upperRamificationGroup K E v := by
  obtain ⟨ρF, hρF⟩ := exists_isArtinRestriction K F
  rw [hρ.unique K E (hρF.intermediateFieldRestrict K hle), ← Subgroup.map_map, hF ρF hρF,
    map_upperRamificationGroup_intermediateFieldRestrictNormalHom K hle v]

/-- **Transport to an abstract floor**: a statement holding on every finite abelian subfield
of the closure holds on an abstract finite abelian floor, through the range of its structure
map (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/FiniteAbelian.lean:30`, the final
transport of its proof). -/
theorem map_eq_upperRamificationGroup_of_algEquiv (L : Type*) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] [Algebra L (AlgebraicClosure K)]
    [IsScalarTower K L (AlgebraicClosure K)] (S : Subgroup Kˣ) (v : ℝ)
    (h : ∀ (L' : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L']
      [IsAbelianGalois K L'] (ρ' : Kˣ →* (L' ≃ₐ[K] L')), IsArtinRestriction K L' ρ' →
        Subgroup.map ρ' S = upperRamificationGroup K L' v)
    (ρ : Kˣ →* (L ≃ₐ[K] L)) (hρ : IsArtinRestriction K L ρ) :
    Subgroup.map ρ S = upperRamificationGroup K L v := by
  let i : L →ₐ[K] AlgebraicClosure K := IsScalarTower.toAlgHom K L (AlgebraicClosure K)
  let L' : IntermediateField K (AlgebraicClosure K) := i.fieldRange
  let e : L ≃ₐ[K] L' := AlgEquiv.ofInjectiveField i
  haveI : FiniteDimensional K L' := e.toLinearEquiv.finiteDimensional
  haveI : IsAbelianGalois K L' := IsAbelianGalois.of_algHom e.symm.toAlgHom
  have hρ' := IsArtinRestriction.of_algEquiv K e (fun x => rfl) hρ
  have hh := h L' _ hρ'
  rw [← Subgroup.map_map] at hh
  exact Subgroup.map_injective (AlgEquiv.autCongr e).injective
    (hh.trans (upperRamificationGroup_map_autCongr K e v).symm)

/-- **Ramification compatibility on every finite abelian subfield of the closure**, `t > 0`:
descended from the standard compositum it lies in
([Serre 1979, Chap. XV, §2, Thm. 2, p.228][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/FiniteAbelian.lean:30`). -/
theorem map_realHigherUnitGroup_of_finiteAbelian (L' : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L'] [IsAbelianGalois K L'] (ρ : Kˣ →* (L' ≃ₐ[K] L'))
    (hρ : IsArtinRestriction K L' ρ) {t : ℝ} (ht : 0 < t) :
    Subgroup.map ρ (realHigherUnitGroup K t) = upperRamificationGroup K L' t := by
  obtain ⟨π, hπ, n, d, hd, hle⟩ := exists_le_standardCompositum K L'
  haveI := standardCompositum_isAbelianGalois K hπ n d hd
  exact map_eq_upperRamificationGroup_of_le K hle _ t
    (fun ρF hρF => map_realHigherUnitGroup_standardCompositum K hπ n d hd ρF hρF ht) ρ hρ

/-- **The inertia endpoint on every finite abelian subfield of the closure**: the Artin image
of the full unit group is `G^0`, descended from the standard compositum
([Serre 1979, Chap. XIII, §4, Cor. to Prop. 13, p.198][Serre1979]). -/
theorem map_units_of_finiteAbelian (L' : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L'] [IsAbelianGalois K L'] (ρ : Kˣ →* (L' ≃ₐ[K] L'))
    (hρ : IsArtinRestriction K L' ρ) :
    Subgroup.map ρ (MonoidHom.range (Units.map (𝒪[K].subtype : ↥𝒪[K] →* K))) =
      upperRamificationGroup K L' 0 := by
  obtain ⟨π, hπ, n, d, hd, hle⟩ := exists_le_standardCompositum K L'
  haveI := standardCompositum_isAbelianGalois K hπ n d hd
  exact map_eq_upperRamificationGroup_of_le K hle _ 0
    (fun ρF hρF => map_units_standardCompositum K hπ n d hd ρF hρF) ρ hρ

end Atlas.Knowledge
