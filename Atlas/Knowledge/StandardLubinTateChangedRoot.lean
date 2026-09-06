import Mathlib
import Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField
import Atlas.Knowledge.IntegerValuation
import Atlas.Knowledge.NormalizedValuationAlgEquiv
import Atlas.Knowledge.StandardLubinTateCompositum
import Atlas.Knowledge.StandardLubinTateConjugateCeiling
import Atlas.Knowledge.StandardLubinTateRootProximity

/-!
# standard Lubin–Tate changed root

Krasner's argument closes the changed-uniformizer comparison: for a unit `u` of depth
`n + 1`, the changed primitive polynomial `Φ_{πu}` has a root inside the `π`-level
field. At the compositum of the two level fields, the root-proximity pigeonhole places
a `πu`-primitive root `r` strictly inside the Krasner gap of the `π`-generator `ξ`;
any automorphism over `K⟮ρ⟯` fixing `ρ` would displace `ξ` by at most the conjugate
ceiling while moving it by at least the gap, so every such automorphism fixes `ξ` and
`ξ ∈ K⟮ρ⟯`; the degree squeeze — `[K⟮ξ⟯ : K]` is the full level degree while
`[K⟮ρ⟯ : K]` is at most it — turns the inclusion around, and the compositum embedding
carries the root back into the level field of the separable closure, together with the
fact that it generates it. The statement is unconditional: every valuative instance is
obtained inside the proof.

## Main statements

* `exists_standardLubinTateChangedRoot` — a `πu`-primitive root inside the `π`-level
  field, generating it; proved.

## Implementation notes

The compositum carrier makes every elaboration step re-normalize the join of two
adjoins, and the default heartbeat budget drowns in `whnf` there; the raised budget
carries a reason comment. The automorphism argument runs at the integer level — the
ceiling, the gap, and the invariance are `integerValuation` statements — with one
packaging step turning the restricted automorphism into an `↥𝒪[K]`-algebra map so the
primitive polynomial transports along it. The exit to the level field is the
`Atlas.Knowledge.val_compositumGenerator` bridge: the image of `K⟮ξ⟯` under the
compositum embedding is the adjoin of the chosen root, which is the level field by
definition — one identification serving both the membership and the generation
conjunct.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section Krasner

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable {π : ↥𝒪[K]} (hπ : Irreducible π) {n : ℕ}

set_option maxHeartbeats 800000 in
-- every step at the compositum re-elaborates the join of two adjoins; the default
-- heartbeat budget drowns in `whnf` on that carrier
/-- **The changed primitive root lives in the original level field**: a depth-`n + 1`
unit change of the uniformizer has a primitive root already inside the `π`-level
field, and the root generates it — Krasner's argument at the compositum, closed by the
degree squeeze
([Milne 2020, Chap. I, §3, Thm. 3.9 and Prop. 3.10, pp.40–43][MilneCFT] — Milne's
Thm. 3.9 gives the independence only after composing with `K^{un}` and for every unit,
through the formal-group isomorphism of Prop. 3.10 over the completion of `K^{un}`;
the depth-`n + 1` restriction here is what buys the equality at finite level;
Yamaguchi 2026, `LubinTate/FiniteLevel/HigherUnitLevelEquiv.lean:1363` — the source's
changed-level equivalence, whose field-level input this root existence is). -/
theorem exists_standardLubinTateChangedRoot {u : (↥𝒪[K])ˣ}
    (hu : u ∈ integerHigherUnitGroup K (n + 1)) :
    ∃ z : ↥(standardLubinTateLevelField K hπ n),
      Polynomial.aeval z
        (standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K (π * (u : ↥𝒪[K])) n)
        = 0 ∧
      IntermediateField.adjoin K {((standardLubinTateLevelField K hπ n).val z)} =
        standardLubinTateLevelField K hπ n := by
  classical
  have hπ' : Irreducible (π * (u : ↥𝒪[K])) :=
    (Associated.irreducible_iff ⟨u, rfl⟩).mp hπ
  -- the compositum carrier and its instances
  obtain ⟨vM, tM, hVE, _, hMCL⟩ := exists_extension_isMixedCharLocalField K
    ↥(standardLubinTateCompositum K hπ hπ' n)
  letI := vM
  letI := tM
  haveI := hVE
  haveI := hMCL
  -- the two primitive roots in the compositum
  set x := compositumGeneratorInteger K hπ hπ' n
  set y := compositumGeneratorInteger' K hπ hπ' n
  have hrx : Polynomial.aeval x (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0 :=
    aeval_compositumGeneratorInteger K hπ hπ' n
  have hry : Polynomial.aeval y
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] (π * (u : ↥𝒪[K])) n) = 0 :=
    aeval_compositumGeneratorInteger' K hπ hπ' n
  -- the Krasner-gap root of the changed polynomial
  obtain ⟨r, -, hrprim, hcase⟩ :=
    standardLubinTateRootProximity_lt K ↥(standardLubinTateCompositum K hπ hπ' n)
      hπ hu hrx hry
  -- the two field-level points
  set ξ := (x : ↥(standardLubinTateCompositum K hπ hπ' n)) with hξ
  set ρ := (r : ↥(standardLubinTateCompositum K hπ hπ' n)) with hρ
  -- the Krasner claim: `ξ` lies in `K⟮ρ⟯`
  have hmem : ξ ∈ IntermediateField.adjoin K {ρ} := by
    rcases hcase with heq | hgap
    · rw [hξ, hρ, ← heq]
      exact IntermediateField.mem_adjoin_simple_self K ξ
    · -- every automorphism over `K⟮ρ⟯` fixes `ξ`
      have hfix : ∀ σ : ↥(standardLubinTateCompositum K hπ hπ' n) ≃ₐ[
          ↥(IntermediateField.adjoin K {ρ})]
          ↥(standardLubinTateCompositum K hπ hπ' n), σ ξ = ξ := by
        intro σ
        by_contra hne
        set σK := σ.restrictScalars K
        set σO := algEquivIntegerRestrict K
          ↥(standardLubinTateCompositum K hπ hπ' n) σK
        -- the automorphism image is again a primitive root
        have hcomm : ∀ c : ↥𝒪[K],
            σO (algebraMap ↥𝒪[K] ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)] c) =
            algebraMap ↥𝒪[K] ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)] c := by
          intro c
          apply Subtype.ext
          change σK ((algebraMap ↥𝒪[K]
            ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)] c :
              ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)]) :
            ↥(standardLubinTateCompositum K hπ hπ' n)) = _
          have hcs : ((algebraMap ↥𝒪[K]
              ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)] c :
                ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)]) :
              ↥(standardLubinTateCompositum K hπ hπ' n)) =
              algebraMap K ↥(standardLubinTateCompositum K hπ hπ' n) (c : K) := rfl
          rw [hcs]
          exact σK.commutes (c : K)
        set σA : ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)] →ₐ[↥𝒪[K]]
            ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)] :=
          ⟨σO.toRingHom, hcomm⟩
        have hσx_root : Polynomial.aeval (σO x)
            (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0 := by
          have h := Polynomial.aeval_algHom_apply σA x
            (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n)
          rw [hrx, map_zero] at h
          exact h
        have hσx_ne : σO x ≠ x := fun h0 => hne (congrArg Subtype.val h0)
        -- the ceiling caps the displacement, the gap exceeds it
        have hceil := standardLubinTateConjugateCeiling K
          ↥(standardLubinTateCompositum K hπ hπ' n) hπ hrx hσx_root hσx_ne
        have hfixr : σO r = r := by
          apply Subtype.ext
          change σK (r : ↥(standardLubinTateCompositum K hπ hπ' n)) = _
          have hρF : ρ ∈ IntermediateField.adjoin K {ρ} :=
            IntermediateField.mem_adjoin_simple_self K ρ
          have := σ.commutes ⟨ρ, hρF⟩
          exact this
        have hinv := integerValuation_algEquivIntegerRestrict K
          ↥(standardLubinTateCompositum K hπ hπ' n) σK (x - r)
        have hσdiff : σO (x - r) = σO x - r := by
          rw [map_sub, hfixr]
        have hkey : x - σO x = (x - r) + -(σO (x - r)) := by
          rw [hσdiff]
          ring
        have hsumne : x - σO x ≠ 0 := sub_ne_zero.mpr (Ne.symm hσx_ne)
        have hmin := min_le_integerValuation_add
          ↥(standardLubinTateCompositum K hπ hπ' n)
          (y := x - r) (z := -(σO (x - r))) (by rw [← hkey]; exact hsumne)
        rw [← hkey, integerValuation_neg, hinv, min_self] at hmin
        omega
      have hbot : ξ ∈ (⊥ : IntermediateField
          ↥(IntermediateField.adjoin K {ρ})
          ↥(standardLubinTateCompositum K hπ hπ' n)) :=
        (IsGalois.mem_bot_iff_fixed ξ).mpr hfix
      rw [IntermediateField.mem_bot] at hbot
      obtain ⟨⟨w, hw⟩, hwξ⟩ := hbot
      rw [← hwξ]
      exact hw
  -- the two field-level annihilations
  have hξfield : Polynomial.aeval ξ
      (standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n) = 0 :=
    aeval_compositumGenerator_field K hπ hπ' n
  have hρfield : Polynomial.aeval ρ
      (standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K (π * (u : ↥𝒪[K])) n)
      = 0 := by
    letI : IsScalarTower ↥𝒪[K] ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)]
        ↥(standardLubinTateCompositum K hπ hπ' n) :=
      Valuation.HasExtension.instIsScalarTowerInteger
        (vR := valuation K)
        (vA := valuation ↥(standardLubinTateCompositum K hπ hπ' n))
    have h := congrArg (IsScalarTower.toAlgHom ↥𝒪[K]
      ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)]
      ↥(standardLubinTateCompositum K hπ hπ' n)) hrprim
    rw [map_zero, ← Polynomial.aeval_algHom_apply] at h
    rwa [standardLubinTatePrimitivePolynomialOverField,
      Polynomial.aeval_map_algebraMap]
  -- the degree squeeze identifies the two simple extensions
  have hmonicF : (standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n).Monic :=
    (standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n).map _
  have hmonicF' : (standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K
      (π * (u : ↥𝒪[K])) n).Monic :=
    (standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] _ n).map _
  have hintξ : IsIntegral K ξ :=
    ⟨_, hmonicF, by rw [← Polynomial.aeval_def]; exact hξfield⟩
  have hintρ : IsIntegral K ρ :=
    ⟨_, hmonicF', by rw [← Polynomial.aeval_def]; exact hρfield⟩
  have hminξ : minpoly K ξ = standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n :=
    (minpoly.eq_of_irreducible_of_monic
      (standardLubinTatePrimitivePolynomialOverField_irreducible K hπ n)
      hξfield hmonicF).symm
  have hDξ : Module.finrank K ↥(IntermediateField.adjoin K {ξ}) =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
    rw [IntermediateField.adjoin.finrank hintξ, hminξ,
      standardLubinTatePrimitivePolynomialOverField,
      (standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n).natDegree_map,
      standardLubinTatePrimitivePolynomial_natDegree]
  have hDρ : Module.finrank K ↥(IntermediateField.adjoin K {ρ}) ≤
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
    rw [IntermediateField.adjoin.finrank hintρ]
    calc (minpoly K ρ).natDegree ≤
        (standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K
          (π * (u : ↥𝒪[K])) n).natDegree :=
          Polynomial.natDegree_le_of_dvd (minpoly.dvd K ρ hρfield) hmonicF'.ne_zero
      _ = (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ n := by
          rw [standardLubinTatePrimitivePolynomialOverField,
            (standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] _ n).natDegree_map,
            standardLubinTatePrimitivePolynomial_natDegree]
  have hle : IntermediateField.adjoin K {ξ} ≤ IntermediateField.adjoin K {ρ} := by
    rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
    exact hmem
  have heqF : IntermediateField.adjoin K {ξ} = IntermediateField.adjoin K {ρ} :=
    IntermediateField.eq_of_le_of_finrank_le hle (by rw [hDξ]; exact hDρ)
  have hρmem : ρ ∈ IntermediateField.adjoin K {ξ} := by
    rw [heqF]
    exact IntermediateField.mem_adjoin_simple_self K ρ
  -- push into the separable closure through the compositum embedding
  have hvalξ : (standardLubinTateCompositum K hπ hπ' n).val ξ =
      chosenStandardLubinTatePrimitiveRoot K hπ n :=
    val_compositumGenerator K hπ hπ' n
  have hmap : (standardLubinTateCompositum K hπ hπ' n).val ρ ∈
      standardLubinTateLevelField K hπ n := by
    have h1 : (standardLubinTateCompositum K hπ hπ' n).val ρ ∈
        (IntermediateField.adjoin K {ξ}).map
          (standardLubinTateCompositum K hπ hπ' n).val :=
      ⟨ρ, hρmem, rfl⟩
    rw [IntermediateField.adjoin_map, Set.image_singleton] at h1
    rw [hvalξ] at h1
    exact h1
  -- the image of `K⟮ξ⟯ = K⟮ρ⟯` is the level field, which is the generation conjunct
  have hgen : IntermediateField.adjoin K
      {((standardLubinTateCompositum K hπ hπ' n).val ρ)} =
      standardLubinTateLevelField K hπ n := by
    have h3 := congrArg
      (IntermediateField.map (standardLubinTateCompositum K hπ hπ' n).val) heqF
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_map,
      Set.image_singleton, Set.image_singleton] at h3
    rw [hvalξ] at h3
    exact h3.symm
  refine ⟨⟨(standardLubinTateCompositum K hπ hπ' n).val ρ, hmap⟩, ?_, hgen⟩
  have hinjL : Function.Injective (standardLubinTateLevelField K hπ n).val :=
    (standardLubinTateLevelField K hπ n).val.toRingHom.injective
  apply hinjL
  rw [map_zero, ← Polynomial.aeval_algHom_apply]
  have h2 := Polynomial.aeval_algHom_apply
    (standardLubinTateCompositum K hπ hπ' n).val ρ
    (standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K (π * (u : ↥𝒪[K])) n)
  rw [hρfield, map_zero] at h2
  exact h2

end Krasner

end Atlas.Knowledge
