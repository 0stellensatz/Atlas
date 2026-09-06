import Mathlib
import Atlas.Knowledge.ArtinRestrictionNormQuotient
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.NormIndexAbelian
import Atlas.Knowledge.StandardOpenSubgroups
import Atlas.Knowledge.UnitsFiniteIndexOpen

/-!
# conductor exponent

The conductor exponent of an extension of valued fields: the least `n` for which the `n`th
unit step `U^n` of the base lies in the norm group, as an element of `ℕ∞` — total, with `⊤`
recording that no step ever falls in. For a finite abelian extension of a
mixed-characteristic local field the exponent is finite (the norm subgroup is open and the
unit steps are cofinal), and against a reciprocity map it is exactly the cutoff of the Artin
images of the unit filtration: the image of `U^n` is trivial iff `n` is at least the
exponent. All four statements are proved.

## Main definitions

* `conductorExponent` — `sInf` of the set of levels whose unit step is normic, in `ℕ∞`.

## Main statements

* `conductorExponent_le_iff` — the defining characterization at finite levels.
* `conductorExponent_ne_top` — finiteness for a finite abelian extension of a
  mixed-characteristic local field.
* `conductorExponent_cutoff` / `conductorExponent_cutoff_zero` — the Artin image of the
  `n`th unit step is trivial iff `conductorExponent ≤ n`, with the `U^0` endpoint separate.

## Implementation notes

The definition needs no local-field structure and no finiteness — `sInf` is total on the
complete lattice `ℕ∞`, an empty set of normic levels giving `⊤`; for an infinite extension
Mathlib's `Algebra.norm` is the constant `1`, so the norm range collapses to the trivial
subgroup, no level is normic for any field with a nontrivial unit step, and the exponent
junks to `⊤` — the junk region is owned here once. The unit steps are phrased through the
`(↥𝒪[K])ˣ`-carrier of the source's principal units, which
`Atlas.Knowledge.mem_higherUnitGroup_iff` identifies with the layer's translate-set
filtration; at level `0` the condition ranges over all of `𝒪[K]ˣ` since `𝓂[K]^0 = ⊤`, so the
`U^0` semantics needs no case split. Agreement with the source's ℕ-valued `Nat.find` form
(`LocalClassFieldTheory/Finite/Conductor.lean:48`) is exactly the finiteness claim.
Finiteness was recorded over every nonarchimedean local field and is proved here over mixed
characteristic only — the layer's reciprocity, which supplies the norm subgroup's finite
index through `Atlas.Knowledge.normIndexAbelian`, lives there, and so does the openness of
finite-index subgroups (`Atlas.Knowledge.unitsFiniteIndexOpen`) that makes a unit step fall
in (`Atlas.Knowledge.exists_higherUnitGroup_le_of_isOpen`); the source reaches its
`IsNonarchimedeanLocalField` scope through a topological reciprocity the layer does not carry
in equal characteristic
(`LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean`). The extension
enters with no embedding into the closure, so the proof picks one by `IsAlgClosed.lift` and
counts the norm index at its range. The cutoff claims take the reciprocity map through
`Atlas.Knowledge.IsArtinRestriction` and are one rewrite each:
`Atlas.Knowledge.IsArtinRestriction.ker` pins the kernel as the norm subgroup, and the image
of a step is trivial iff the step lies in the kernel; they are stated only over mixed
characteristic for that reason, while the definition and `conductorExponent_le_iff` keep full
generality. Declarations touching the subtype `↥(𝓂[K] ^ m)` carry a scoped
`synthInstance.maxHeartbeats` bump, as `Atlas.Knowledge.HigherUnitGroup` already does.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

set_option synthInstance.maxHeartbeats 40000 in
-- The instance search on the subtype `↥(𝓂[K] ^ m : Ideal ↥𝒪[K])` does not fit the budget.
/-- The **conductor exponent** of an extension `L` of a valued field `K`: the least level `n`
whose unit step — the units of `𝒪[K]` congruent to `1` modulo `𝓂[K] ^ n`, read in `Kˣ` — lies
in the norm group of `L` over `K`, as an element of `ℕ∞`, with `⊤` when no level works
([Serre 1979, Chap. XV, §2, Cor. 2 to Thm. 1, p.228][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Conductor.lean:48`). -/
noncomputable def conductorExponent (K L : Type*) [Field K] [ValuativeRel K]
    [Field L] [Algebra K L] : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ m : ℕ, n = m ∧
    ∀ u : (↥𝒪[K])ˣ, ((u : ↥𝒪[K]) - 1) ∈ (𝓂[K] ^ m : Ideal ↥𝒪[K]) →
      Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u ∈
        MonoidHom.range (Units.map (Algebra.norm K : L →* K))}

set_option synthInstance.maxHeartbeats 40000 in
-- The instance search on the subtype `↥(𝓂[K] ^ n : Ideal ↥𝒪[K])` does not fit the budget.
/-- The defining characterization of the conductor exponent at finite levels:
`conductorExponent K L ≤ n` iff the `n`th unit step is normic — antitonicity of the steps
makes the infimum a threshold
([Serre 1979, Chap. XV, §2, Cor. 2 to Thm. 1, p.228][Serre1979]). -/
theorem conductorExponent_le_iff (K L : Type*) [Field K] [ValuativeRel K]
    [Field L] [Algebra K L] (n : ℕ) :
    conductorExponent K L ≤ n ↔
      ∀ u : (↥𝒪[K])ˣ, ((u : ↥𝒪[K]) - 1) ∈ (𝓂[K] ^ n : Ideal ↥𝒪[K]) →
        Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u ∈
          MonoidHom.range (Units.map (Algebra.norm K : L →* K)) := by
  unfold conductorExponent
  constructor
  · intro h
    have hne : {N : ℕ∞ | ∃ m : ℕ, N = m ∧
        ∀ u : (↥𝒪[K])ˣ, ((u : ↥𝒪[K]) - 1) ∈ (𝓂[K] ^ m : Ideal ↥𝒪[K]) →
          Units.map (𝒪[K].subtype : ↥𝒪[K] →* K) u ∈
            MonoidHom.range (Units.map (Algebra.norm K : L →* K))}.Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro he
      rw [he, sInf_empty] at h
      simp at h
    obtain ⟨m, hm, hPm⟩ := csInf_mem hne
    rw [hm] at h
    intro u hu
    exact hPm u (Ideal.pow_le_pow_right (Nat.cast_le.mp h) hu)
  · intro h
    exact sInf_le ⟨n, rfl, h⟩

/-- The conductor exponent of a finite abelian extension of a mixed-characteristic local
field is finite: the norm subgroup has finite index, hence is open, and some unit step lies
in every open subgroup. This is the identification with the source's ℕ-valued conductor, and
the one genuinely class-field-theoretic input of the item
([Serre 1979, Chap. XV, §2, Cor. 2 to Thm. 1, p.228][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/Conductor.lean:35`). -/
theorem conductorExponent_ne_top (K L : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] :
    conductorExponent K L ≠ ⊤ := by
  haveI : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let i : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let L' : IntermediateField K (AlgebraicClosure K) := i.fieldRange
  let e : L ≃ₐ[K] L' := AlgEquiv.ofInjectiveField i
  haveI : FiniteDimensional K L' := e.toLinearEquiv.finiteDimensional
  haveI : IsAbelianGalois K L' := IsAbelianGalois.of_algHom e.symm.toAlgHom
  have hfi : (Units.map (Algebra.norm K : L →* K)).range.FiniteIndex := by
    rw [← range_normUnits_fieldRange K L i]
    haveI : Finite (Kˣ ⧸ (Units.map (Algebra.norm K : L' →* K)).range) :=
      Nat.finite_of_card_ne_zero (by rw [normIndexAbelian K L']; exact Module.finrank_pos.ne')
    exact Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨n, hn⟩ := exists_higherUnitGroup_le_of_isOpen K _ (unitsFiniteIndexOpen K _ hfi)
  have hle : conductorExponent K L ≤ (n : ℕ) := by
    rw [conductorExponent_le_iff]
    intro u hu
    exact hn ((mem_higherUnitGroup_iff K n _).2 ⟨u, hu, rfl⟩)
  exact ne_top_of_le_ne_top (ENat.coe_ne_top _) hle

section Cutoff

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsAbelianGalois K L]
  [Algebra L (AlgebraicClosure K)] [IsScalarTower K L (AlgebraicClosure K)]

/-- The conductor exponent as the cutoff of the Artin images: the reciprocity image of the
`n`th higher unit group is trivial iff `n` reaches the exponent
([Serre 1979, Chap. XV, §2, Cor. 3 to Thm. 1, p.228][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/Core.lean:43`). -/
theorem conductorExponent_cutoff (ρ : Kˣ →* (L ≃ₐ[K] L))
    (hρ : IsArtinRestriction K L ρ) (n : ℕ+) :
    Subgroup.map ρ (higherUnitGroup K n) = ⊥ ↔
      conductorExponent K L ≤ (n : ℕ) := by
  rw [Subgroup.map_eq_bot_iff, hρ.ker, conductorExponent_le_iff]
  constructor
  · intro h u hu
    exact h ((mem_higherUnitGroup_iff K n _).2 ⟨u, hu, rfl⟩)
  · intro h x hx
    obtain ⟨u, hu, rfl⟩ := (mem_higherUnitGroup_iff K n x).1 hx
    exact h u hu

/-- The `U^0` endpoint of the cutoff: the reciprocity image of the full unit group is trivial
iff the conductor exponent is `0` — iff the extension is unramified
([Serre 1979, Chap. XV, §2, Cor. 3 to Thm. 1, p.228][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/Core.lean:43`). -/
theorem conductorExponent_cutoff_zero (ρ : Kˣ →* (L ≃ₐ[K] L))
    (hρ : IsArtinRestriction K L ρ) :
    Subgroup.map ρ (MonoidHom.range (Units.map (𝒪[K].subtype : ↥𝒪[K] →* K))) = ⊥ ↔
      conductorExponent K L = 0 := by
  have h0 := conductorExponent_le_iff K L 0
  simp only [Nat.cast_zero, pow_zero, Ideal.one_eq_top, Submodule.mem_top, true_implies] at h0
  rw [Subgroup.map_eq_bot_iff, hρ.ker, ← nonpos_iff_eq_zero, h0]
  constructor
  · intro h u
    exact h ⟨u, rfl⟩
  · rintro h _ ⟨u, rfl⟩
    exact h u

end Cutoff

end Atlas.Knowledge
