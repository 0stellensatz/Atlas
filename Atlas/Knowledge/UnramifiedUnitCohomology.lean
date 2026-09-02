import Mathlib
import Atlas.Knowledge.GalUnits
import Atlas.Knowledge.HilbertNinety
import Atlas.Knowledge.LowerRamificationGroup
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.NormalizedValuationAlgEquiv
import Atlas.Knowledge.UnramifiedNormRange

/-!
# unramified unit cohomology

The two elementwise halves of the cohomological triviality of the
units of a finite unramified extension of mixed-characteristic local
fields: every base unit is the norm of a unit — `Ĥ⁰(G, U_L) = 0` —
and every norm-one unit is a `σ`-quotient of a unit at a generator —
`Ĥ⁻¹(G, U_L) = 0`. These are the concrete facts the local
instantiation's unramified-unit-cohomology discharge transfers to the
abstract datum (#104).

## Main statements

* `unramifiedUnitNorm_surjective` — a base unit is the norm of a
  unit; proved.
* `unramifiedUnitPrimitive` — a norm-one unit is a `σ`-quotient of a
  unit; proved.

## Implementation notes

Neither statement has a source counterpart: at the pin the source
derives the abstract unit-cohomology axiom from the Tate-cohomology
reading of the class-field axiom (`Reciprocity/Core.lean:413`), the
derivation `Atlas.Knowledge.ClassFieldAxiom`'s notes replace by a
direct local discharge — these two theorems are that discharge's
concrete floor, formalized from the literature. The first closes on
`Atlas.Knowledge.unramifiedNormRange` (itself index-counting against
the class-field axiom) with the valuation multiplicativity pinning
the preimage to a unit; the second is Hilbert 90 with the witness
rescaled by a base uniformizer power, which the Galois action fixes,
to a unit — the `σ`-quotient direction is the layer's Hilbert-90
direction `y / σ y`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), course notes, 2020.
* [Serre1979] J.-P. Serre, *Local fields*, Graduate Texts in Mathematics 67,
  Springer, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] [IsMixedCharLocalField L] [IsGalois K L]

/-- **Every base unit of an unramified extension is the norm of a
unit** — the elementwise `Ĥ⁰(G, U_L) = 0`
([Milne 2020, Chap. III, §1, Prop. 1.2, p.98][MilneCFT];
[Serre 1979, Chap. V, §2, Prop. 3 and Cor., p.82][Serre1979]). -/
theorem unramifiedUnitNorm_surjective
    (h : lowerRamificationGroup K L 0 = ⊥)
    (u : Kˣ) (hu : normalizedValuation K u = 0) :
    ∃ ε : Lˣ, normalizedValuation L ε = 0 ∧
      Units.map ((Algebra.norm K) : L →* K) ε = u := by
  have hmem : u ∈ (Units.map ((Algebra.norm K) : L →* K)).range := by
    rw [unramifiedNormRange K L h, Subgroup.mem_comap,
      Subgroup.mem_zpowers_iff]
    refine ⟨0, ?_⟩
    change _ = Multiplicative.ofAdd (normalizedValuation K u)
    rw [hu, zpow_zero]
    rfl
  obtain ⟨y, hy⟩ := hmem
  refine ⟨y, ?_, hy⟩
  have hval := normalizedValuation_norm_of_unramified K L h y
  rw [hy, hu] at hval
  have hn : (Module.finrank K L : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr Module.finrank_pos.ne'
  exact (mul_eq_zero.mp hval.symm).resolve_left hn

/-- **Every norm-one unit of an unramified extension is a
`σ`-quotient of a unit at a generator** — the elementwise
`Ĥ⁻¹(G, U_L) = 0`, by Hilbert 90 with the witness rescaled to a unit
by a base uniformizer power
([Milne 2020, Chap. III, §1, Prop. 1.1, p.97][MilneCFT]). -/
theorem unramifiedUnitPrimitive
    (h : lowerRamificationGroup K L 0 = ⊥)
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ)
    (u : Lˣ) (hnorm : Algebra.norm K (u : L) = 1) :
    ∃ ε : Lˣ, normalizedValuation L ε = 0 ∧
      (ε : L) / σ (ε : L) = (u : L) := by
  obtain ⟨y, hy⟩ := hilbertNinety (K := K) (L := L) (σ := σ) hgen hnorm
  obtain ⟨π, hπ⟩ := normalizedValuation_surjective K 1
  set πL : Lˣ := Units.map ((algebraMap K L) : K →* L) π with hπL
  have hπLval : normalizedValuation L πL = 1 := by
    rw [hπL, normalizedValuation_algebraMap_of_unramified K L h π, hπ]
  set m : ℤ := normalizedValuation L y with hm
  refine ⟨y * πL ^ (-m), ?_, ?_⟩
  · rw [normalizedValuation_mul, normalizedValuation_zpow, hπLval,
      mul_one, ← hm, add_neg_cancel]
  · have hσπ : σ ((πL : L) ^ (-m)) = (πL : L) ^ (-m) := by
      have hcoe : (πL : L) = algebraMap K L π := rfl
      rw [hcoe, map_zpow₀, AlgEquiv.commutes]
    calc ((y * πL ^ (-m) : Lˣ) : L) / σ ((y * πL ^ (-m) : Lˣ) : L)
        = ((y : L) * (πL : L) ^ (-m)) /
            (σ (y : L) * σ ((πL : L) ^ (-m))) := by
          push_cast
          rw [map_mul]
    _ = ((y : L) * (πL : L) ^ (-m)) /
            (σ (y : L) * (πL : L) ^ (-m)) := by rw [hσπ]
    _ = (y : L) / σ (y : L) := by
          rw [mul_div_mul_right]
          exact zpow_ne_zero _ (Units.ne_zero πL)
    _ = (u : L) := hy

end

end Atlas.Knowledge
