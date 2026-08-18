import Mathlib
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.IsArtinRestriction

/-!
# conductor exponent

The conductor exponent of an extension of valued fields: the least `n` for which the `n`th
unit step `U^n` of the base lies in the norm group, as an element of `ℕ∞` — total, with `⊤`
recording that no step ever falls in. For a finite abelian extension of a local field the
exponent is finite (the norm subgroup is open and the unit steps are cofinal), and against a
reciprocity map it is exactly the cutoff of the Artin images of the unit filtration: the
image of `U^n` is trivial iff `n` is at least the exponent. Finiteness and the cutoff are
recorded ahead of their proofs; the definition and the defining `≤`-characterization land
proved.

## Main definitions

* `conductorExponent` — `sInf` of the set of levels whose unit step is normic, in `ℕ∞`.

## Main statements

* `conductorExponent_le_iff` — the defining characterization at finite levels.
* `conductorExponent_ne_top` — finiteness for a finite abelian extension of a
  nonarchimedean local field, recorded ahead of its proof.
* `conductorExponent_cutoff` / `conductorExponent_cutoff_zero` — the Artin image of the
  `n`th unit step is trivial iff `conductorExponent ≤ n`, with the `U^0` endpoint separate;
  both recorded ahead of their proofs.

## Implementation notes

The definition needs no local-field structure and no finiteness — `sInf` is total on the
complete lattice `ℕ∞`, an empty set of normic levels giving `⊤`; for an infinite extension
Mathlib's `Algebra.norm` is the constant `1`, every level is normic, and the exponent junks
to `0` — the junk region is owned here once. The unit steps are phrased through the
`(↥𝒪[K])ˣ`-carrier of the source's principal units, which
`Atlas.Knowledge.mem_higherUnitGroup_iff` identifies with the layer's translate-set
filtration; at level `0` the condition ranges over all of `𝒪[K]ˣ` since `𝓂[K]^0 = ⊤`, so
the `U^0` semantics needs no case split. Agreement with the source's ℕ-valued `Nat.find`
form (`Finite/Conductor.lean:48`) is exactly the finiteness claim. The cutoff claims take
the reciprocity map through `Atlas.Knowledge.IsArtinRestriction` and are true because the
characterization pins the kernel as the norm subgroup; they are stated only over mixed
characteristic for that reason, while the definition and `conductorExponent_le_iff` keep
full generality. Declarations touching the subtype `↥(𝓂[K] ^ m)` carry a scoped
`synthInstance.maxHeartbeats` bump, as `Atlas.Knowledge.HigherUnitGroup` already does.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

set_option synthInstance.maxHeartbeats 40000 in
-- The instance search on the subtype `↥(𝓂[K] ^ m : Ideal ↥𝒪[K])` does not fit the budget.
/-- The **conductor exponent** of an extension `L` of a valued field `K`: the least level
`n` whose unit step — the units of `𝒪[K]` congruent to `1` modulo `𝓂[K] ^ n`, read in `Kˣ`
— lies in the norm group of `L` over `K`, as an element of `ℕ∞`, with `⊤` when no level
works ([Serre 1979, Chap. XV, §2, Cor. 2 to Thm. 1, p.228][Serre1979];
[Yamaguchi 2026, `LocalClassFieldTheory/Finite/Conductor.lean:48`][Yamaguchi2026]). -/
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

/-- The conductor exponent of a finite abelian extension of a nonarchimedean local field is
finite: the norm subgroup is open and the unit steps are cofinal among neighborhoods of `1`.
This is the identification with the source's ℕ-valued conductor, and the one genuinely
class-field-theoretic input of the item. Claim recorded ahead of its proof
([Serre 1979, Chap. XV, §2, Cor. 2 to Thm. 1, p.228][Serre1979];
[Yamaguchi 2026, `LocalClassFieldTheory/Finite/Conductor.lean:35`][Yamaguchi2026]). -/
theorem conductorExponent_ne_top (K L : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L] :
    conductorExponent K L ≠ ⊤ := by
  sorry

section Cutoff

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsAbelianGalois K L]
  [Algebra L (AlgebraicClosure K)] [IsScalarTower K L (AlgebraicClosure K)]

/-- The conductor exponent as the cutoff of the Artin images: the reciprocity image of the
`n`th higher unit group is trivial iff `n` reaches the exponent. Claim recorded ahead of its
proof ([Serre 1979, Chap. XV, §2, Cor. 3 to Thm. 1, p.228][Serre1979];
[Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/Core.lean:43`][Yamaguchi2026]). -/
theorem conductorExponent_cutoff (ρ : Kˣ →* (L ≃ₐ[K] L))
    (hρ : IsArtinRestriction K L ρ) (n : ℕ+) :
    Subgroup.map ρ (higherUnitGroup K n) = ⊥ ↔
      conductorExponent K L ≤ (n : ℕ) := by
  sorry

/-- The `U^0` endpoint of the cutoff: the reciprocity image of the full unit group is
trivial iff the conductor exponent is `0` — iff the extension is unramified. Claim recorded
ahead of its proof
([Serre 1979, Chap. XV, §2, Cor. 3 to Thm. 1, p.228][Serre1979];
[Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Filtered/Core.lean:43`][Yamaguchi2026]). -/
theorem conductorExponent_cutoff_zero (ρ : Kˣ →* (L ≃ₐ[K] L))
    (hρ : IsArtinRestriction K L ρ) :
    Subgroup.map ρ (MonoidHom.range (Units.map (𝒪[K].subtype : ↥𝒪[K] →* K))) = ⊥ ↔
      conductorExponent K L = 0 := by
  sorry

end Cutoff

end Atlas.Knowledge
