import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# lower-numbering ramification group

The ramification groups of a finite Galois extension of local fields, in the lower numbering:
`G_i` is the set of automorphisms with `v_L (s a - a) ≥ i + 1` for every `a` in `𝒪_L`, a
decreasing chain of normal subgroups of the Galois group with `G_{-1} = G` and `G_0` the
inertia subgroup. This file gives the `ℤ`-indexed family and its basic API—membership unwound,
the value `⊤` below the start of the chain, antitonicity, normality—and records eventual
triviality as a claim. The real-indexed version is
`Atlas.Knowledge.RealLowerRamificationGroup`, the Herbrand functions that renumber the chain
are `Atlas.Knowledge.HerbrandPhi` and `Atlas.Knowledge.HerbrandPsi`, and the numbering they
produce is `Atlas.Knowledge.UpperRamificationGroup`.

## Main definitions

* `lowerRamificationGroup` — `G_i ≤ L ≃ₐ[K] L` for `i : ℤ`: the automorphisms moving every
  element of the integral closure of `𝒪[K]` in `L` by an element of the `(i + 1)`-st power of
  the Jacobson radical.

## Main statements

* `mem_lowerRamificationGroup_iff` — membership unwound.
* `lowerRamificationGroup_eq_top` — `G_i = ⊤` for `i ≤ -1`.
* `lowerRamificationGroup_antitone` — the chain decreases.
* `exists_lowerRamificationGroup_eq_bot` — the chain reaches `⊥`, recorded ahead of its proof.

## Implementation notes

The encoding is the one `Atlas.Knowledge.AbsoluteInertiaSubgroup` already uses one floor up:
an automorphism restricts to the integral closure of `𝒪[K]` in `L` by `galRestrict`, and the
valuation inequality `v_L (s a - a) ≥ i + 1` becomes membership of `s a - a` in the
`(i + 1)`-st power of `Ideal.jacobson ⊥`, which needs no choice of maximal ideal and is
preserved by every ring automorphism. For `K` complete under a discrete valuation and `L` a
finite separable extension, the integral closure is the valuation ring `𝒪_L`, local with the
radical as its maximal ideal, and the condition is literally the source's. The index is `ℤ`,
truncated by `Int.toNat`: every `i ≤ -1` gives the power `0`, hence the whole group—at
`i = -1` that is the source's `G_{-1} = G`, below it the source defines nothing and the value
is junk. The definition asks nothing of `L` beyond being an algebraic field extension of
`K`—no valuation on `L`, no completeness, no finiteness; the classical hypotheses enter only
the recorded claim.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- The **lower-numbering ramification group** `G_i` of `L` over `K`: the automorphisms moving
every element of the integral closure of `𝒪[K]` in `L` by an element of the `(i + 1)`-st power
of the Jacobson radical—the encoding of `v_L (s a - a) ≥ i + 1` for all `a ∈ 𝒪_L`
([Serre 1979, Chap. IV, §1, Lem. 1 and Prop. 1, pp.61–62][Serre1979]). -/
noncomputable def lowerRamificationGroup (i : ℤ) : Subgroup (L ≃ₐ[K] L) where
  carrier := {s | ∀ x : integralClosure 𝒪[K] L,
    galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) s x - x ∈
      Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) ^ (i + 1).toNat}
  one_mem' := by
    intro x
    simp
  mul_mem' := by
    intro s t hs ht x
    have h : galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) (s * t) x =
        galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) s
          (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t x) := by
      simp
    rw [h, ← sub_add_sub_cancel _ (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t x) x]
    exact add_mem (hs _) (ht x)
  inv_mem' := by
    intro s hs x
    have h : galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) s
        ((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) s⁻¹) x) = x := by
      rw [map_inv, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    have hy := hs ((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) s⁻¹) x)
    rw [h] at hy
    simpa using neg_mem hy

/-- Membership in the lower-numbering ramification group, unwound: `s ∈ G_i` iff `s` moves
every element of the integral closure by an element of the `(i + 1)`-st radical power
([Serre 1979, Chap. IV, §1, Lem. 1, p.61][Serre1979]). -/
theorem mem_lowerRamificationGroup_iff {i : ℤ} {s : L ≃ₐ[K] L} :
    s ∈ lowerRamificationGroup K L i ↔
      ∀ x : integralClosure 𝒪[K] L,
        galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) s x - x ∈
          Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) ^ (i + 1).toNat :=
  Iff.rfl

/-- Below the start of the chain the ramification group is everything: `G_i = ⊤` for
`i ≤ -1`—at `i = -1` this is the source's `G_{-1} = G`, below it the value is junk
([Serre 1979, Chap. IV, §1, Prop. 1, p.62][Serre1979]). -/
theorem lowerRamificationGroup_eq_top {i : ℤ} (hi : i ≤ -1) :
    lowerRamificationGroup K L i = ⊤ := by
  ext s
  simp only [Subgroup.mem_top, iff_true, mem_lowerRamificationGroup_iff]
  intro x
  have h0 : (i + 1).toNat = 0 := by omega
  rw [h0, pow_zero, Ideal.one_eq_top]
  exact Submodule.mem_top

/-- The lower-numbering ramification groups decrease as the index grows
([Serre 1979, Chap. IV, §1, Prop. 1, p.62][Serre1979]). -/
theorem lowerRamificationGroup_antitone : Antitone (lowerRamificationGroup K L) := by
  intro i j hij s hs x
  exact Ideal.pow_le_pow_right (by omega) (hs x)

instance (i : ℤ) : (lowerRamificationGroup K L i).Normal := by
  constructor
  intro s hs t
  rw [mem_lowerRamificationGroup_iff] at hs ⊢
  intro x
  have hmul : galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) (t * s * t⁻¹) x =
      galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t
        (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) s
          ((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t).symm x)) := by
    rw [map_mul, map_mul, map_inv]
    simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv]
  have hτx : galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t
      ((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t).symm x) = x :=
    AlgEquiv.apply_symm_apply _ x
  rw [hmul]
  nth_rewrite 2 [← hτx]
  rw [← map_sub]
  -- An automorphism preserves each power of the Jacobson radical, elementwise.
  have hσ := hs ((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t).symm x)
  have hmem : galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t
      (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) s
          ((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t).symm x) -
        (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t).symm x) ∈
      Ideal.map
        ((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t : _ ≃ₐ[𝒪[K]] _).toRingEquiv :
          integralClosure 𝒪[K] L →+* integralClosure 𝒪[K] L)
        (Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) ^ (i + 1).toNat) :=
    Ideal.mem_map_of_mem _ hσ
  have hbij : Function.Bijective
      ⇑((galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t).toRingEquiv :
        integralClosure 𝒪[K] L →+* integralClosure 𝒪[K] L) :=
    (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) t).bijective
  rwa [Ideal.map_pow, Ideal.map_jacobson_of_bijective hbij, Ideal.map_bot] at hmem

/-- The chain of lower-numbering ramification groups of a finite extension of a
mixed-characteristic local field reaches the trivial subgroup. Claim recorded ahead of its
proof ([Serre 1979, Chap. IV, §1, Prop. 1, p.62][Serre1979]). -/
theorem exists_lowerRamificationGroup_eq_bot [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] : ∃ n : ℤ, lowerRamificationGroup K L n = ⊥ := by
  sorry

end Atlas.Knowledge
