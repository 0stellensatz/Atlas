import Mathlib
import Atlas.Knowledge.IntegerHigherUnitGroup
import Atlas.Knowledge.StandardLubinTateChangedRoot
import Atlas.Knowledge.StandardLubinTateLevelField
import Atlas.Knowledge.StandardLubinTateNormSubgroup
import Atlas.Knowledge.StandardLubinTateNormUniformizer
import Atlas.Knowledge.StandardLubinTatePolynomial

/-!
# standard Lubin–Tate norm membership

The containment half of the norm-subgroup description: the subgroup of `Kˣ` generated
by the uniformizer and the `(n+1)`-st higher units lies inside the norms from level
`n`. The uniformizer is the norm of the negated level generator, recorded in
`Atlas.Knowledge.standardLubinTate_norm_neg_levelGenerator`; a changed uniformizer
`πu` with `u` of depth `n + 1` is the norm of the negated changed root of
`Atlas.Knowledge.exists_standardLubinTateChangedRoot`, whose generation conjunct makes
the root a power-basis generator so the norm reads off the constant coefficient of the
changed primitive polynomial; and a higher unit itself is the norm of the quotient of
the two negated roots.

## Main statements

* `exists_standardLubinTate_norm_neg_eq_changedUniformizer` — `N(−z) = πu` for some
  `z` in the level field; proved.
* `standardLubinTateNormMembership` — `⟨π⟩ ⊔ U^{(n+1)} ≤ Nm(Lₙˣ)`; proved.

## Implementation notes

The generation conjunct enters through `IntermediateField.equivOfEq`: the power basis
of the simple extension of the root's image transports to a power basis of the level
field whose generator is the root itself, and
`Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly` reads the norm off the changed
primitive polynomial, which is the minimal polynomial by irreducibility. The two sign
factors — one from the formula, one from negating the generator — cancel as an even
power of `−1` through `Atlas.Knowledge.algebraNorm_neg`, exactly as in the recorded
`u = 1` case. The subgroup statement splits over the join: `Subgroup.zpowers_le` on
the uniformizer half, and on the higher-unit half the witness in `Lₙˣ` is the
quotient of the two negated roots, whose norms divide to the unit's image.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section Membership

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable {π : ↥𝒪[K]} (hπ : Irreducible π)

/-- The **changed uniformizer is a norm**: for a unit `u` of depth `n + 1`, the product
`πu` is the norm of a negated element of the `π`-level field
([Milne 2020, Chap. I, §3, Thm. 3.6 (c), p.38, proof p.39][MilneCFT] — Milne's
computation is the `u = 1` case, and the changed parameter needs the depth-`n + 1`
root; [Yamaguchi 2026, `LubinTate/FiniteLevel/HigherUnitLevelEquiv.lean:1393`]
[Yamaguchi2026]). -/
theorem exists_standardLubinTate_norm_neg_eq_changedUniformizer {n : ℕ}
    {u : (↥𝒪[K])ˣ} (hu : u ∈ integerHigherUnitGroup K (n + 1)) :
    ∃ z : ↥(standardLubinTateLevelField K hπ n),
      Algebra.norm K (-z) = algebraMap ↥𝒪[K] K (π * (u : ↥𝒪[K])) := by
  obtain ⟨z, hzroot, hzgen⟩ := exists_standardLubinTateChangedRoot K hπ hu
  refine ⟨z, ?_⟩
  have hπ' : Irreducible (π * (u : ↥𝒪[K])) :=
    (Associated.irreducible_iff ⟨u, rfl⟩).mp hπ
  have hmonicF : (standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K
      (π * (u : ↥𝒪[K])) n).Monic :=
    (standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] _ n).map _
  have hmin : minpoly K z = standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K
      (π * (u : ↥𝒪[K])) n :=
    (minpoly.eq_of_irreducible_of_monic
      (standardLubinTatePrimitivePolynomialOverField_irreducible K hπ' n)
      hzroot hmonicF).symm
  -- the root's image is integral over `K`, and its adjoin is the level field
  have hvroot : Polynomial.aeval ((standardLubinTateLevelField K hπ n).val z)
      (standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K
        (π * (u : ↥𝒪[K])) n) = 0 := by
    have h := Polynomial.aeval_algHom_apply (standardLubinTateLevelField K hπ n).val z
      (standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K (π * (u : ↥𝒪[K])) n)
    rw [hzroot, map_zero] at h
    exact h
  have hvint : IsIntegral K ((standardLubinTateLevelField K hπ n).val z) :=
    ⟨_, hmonicF, by rw [← Polynomial.aeval_def]; exact hvroot⟩
  -- the power basis with generator `z`, transported through the generation conjunct
  set pb := (IntermediateField.adjoin.powerBasis hvint).map
    (IntermediateField.equivOfEq hzgen) with hpb
  have hgen_eq : pb.gen = z := by
    apply Subtype.ext
    rfl
  have hkey : Algebra.norm K z =
      (-1 : K) ^ pb.dim * algebraMap ↥𝒪[K] K (π * (u : ↥𝒪[K])) := by
    have h := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly pb
    rw [hgen_eq] at h
    rw [h, hmin, standardLubinTatePrimitivePolynomialOverField, Polynomial.coeff_map,
      standardLubinTatePrimitivePolynomial_coeff_zero]
  rw [algebraNorm_neg K z, hkey, ← mul_assoc, ← pow_add, pb.finrank,
    Even.neg_one_pow ⟨_, rfl⟩, one_mul]

/-- The negated witness of a nonzero norm value is nonzero. -/
private theorem neg_ne_zero_of_norm_eq {n : ℕ} {c : ↥𝒪[K]} (hc : c ≠ 0)
    {z : ↥(standardLubinTateLevelField K hπ n)}
    (hz : Algebra.norm K (-z) = algebraMap ↥𝒪[K] K c) : (-z) ≠ 0 := by
  intro h0
  rw [h0, Algebra.norm_zero] at hz
  exact hc (IsFractionRing.injective ↥𝒪[K] K (by rw [map_zero]; exact hz.symm))

/-- **Norm membership of the principal side**: the subgroup generated by the
uniformizer and the `(n+1)`-st higher units lies inside the norms from level `n` —
the containment half of the norm-subgroup description
([Milne 2020, Chap. I, §1, p.25][MilneCFT] — the containment half of
`Nm(K_{π,n}) = (1 + 𝔪ⁿ)·π^ℤ`;
[Yamaguchi 2026, `LubinTate/FiniteLevel/HigherUnitLevelEquiv.lean:1393`]
[Yamaguchi2026]). -/
theorem standardLubinTateNormMembership (n : ℕ) :
    Subgroup.zpowers (standardLubinTateUniformizerUnit K hπ) ⊔
        (integerHigherUnitGroup K (n + 1)).map
          (Units.map (algebraMap 𝒪[K] K).toMonoidHom) ≤
      (Units.map (Algebra.norm K
        (S := standardLubinTateLevelField K hπ n))).range := by
  have hpix := standardLubinTate_norm_neg_levelGenerator K hπ n
  have hpine : (-(standardLubinTateLevelGenerator K hπ n :
      standardLubinTateLevelField K hπ n)) ≠ 0 :=
    neg_ne_zero_of_norm_eq K hπ hπ.ne_zero hpix
  refine sup_le ?_ ?_
  · rw [Subgroup.zpowers_le]
    refine ⟨Units.mk0 _ hpine, ?_⟩
    ext
    simp only [Units.coe_map, Units.val_mk0]
    rw [hpix]
    rfl
  · rw [Subgroup.map_le_iff_le_comap]
    intro v hv
    have hπv : Irreducible (π * (v : ↥𝒪[K])) :=
      (Associated.irreducible_iff ⟨v, rfl⟩).mp hπ
    obtain ⟨z, hz⟩ := exists_standardLubinTate_norm_neg_eq_changedUniformizer K hπ hv
    have hzne : (-z) ≠ 0 := neg_ne_zero_of_norm_eq K hπ hπv.ne_zero hz
    rw [Subgroup.mem_comap]
    refine ⟨Units.mk0 _ hzne * (Units.mk0 _ hpine)⁻¹, ?_⟩
    ext
    have hpi0 : algebraMap ↥𝒪[K] K π ≠ 0 := fun h0 =>
      hπ.ne_zero (IsFractionRing.injective ↥𝒪[K] K (by rw [h0, map_zero]))
    simp only [map_mul, map_inv, Units.coe_map, Units.val_mul, Units.val_inv_eq_inv_val,
      Units.val_mk0]
    rw [hz, hpix, map_mul, mul_comm (algebraMap ↥𝒪[K] K π), mul_inv_cancel_right₀ hpi0]
    rfl

end Membership

end Atlas.Knowledge
