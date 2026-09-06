import Mathlib
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.NormIndexAbelian

/-!
# norm quotient of an Artin restriction

An Artin restriction is the reciprocity isomorphism of its floor: for a finite abelian
extension `L` of a mixed-characteristic local field `K`, a map `ρ : Kˣ →* (L ≃ₐ[K] L)`
satisfying `Atlas.Knowledge.IsArtinRestriction` has kernel exactly the norm subgroup
`N_{L/K} (Lˣ)` and is surjective, so it induces `Kˣ ⧸ N_{L/K} (Lˣ) ≃* (L ≃ₐ[K] L)`. This is
the finite-level content of the predicate, extracted once so that every consumer — the
conductor cutoffs, the ramification compatibility — reads the kernel off the predicate
instead of unwinding the absolute map.

## Main statements

* `IsArtinRestriction.ker` — the kernel is the range of the unit norm.
* `IsArtinRestriction.surjective` — the restriction is onto the Galois group.
* `range_normUnits_fieldRange` — the unit-norm range is invariant under realizing the
  extension as a subfield of an ambient field.

## Implementation notes

The kernel is the `normKernel` field of `Atlas.Knowledge.IsLocalReciprocity` read at the
range of `L` inside the algebraic closure: a lift of `φ x` restricts trivially to `L` exactly
when it fixes that range pointwise, and the field identifies the preimage of the fixing
subgroup with the norm subgroup of the range, which `range_normUnits_fieldRange` carries back
to `L`. Surjectivity is a count — the quotient by the kernel has the degree's cardinality by
`Atlas.Knowledge.normIndexAbelian`, and so does the Galois group — and the count is taken at
the range so that `L` may live in any universe, the norm-index item binding both fields in
one. The transport lemma carries no local-field hypotheses and is stated ahead of them.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]

/-- The range of the unit norm is unchanged by realizing `L` as the range of an embedding `i`
into an ambient field: the norm is invariant under the induced isomorphism onto
`i.fieldRange`. -/
theorem range_normUnits_fieldRange {Ω : Type*} [Field Ω] [Algebra K Ω] (i : L →ₐ[K] Ω) :
    (Units.map (Algebra.norm K : ↥i.fieldRange →* K)).range =
      (Units.map (Algebra.norm K : L →* K)).range := by
  let e : L ≃ₐ[K] i.fieldRange := AlgEquiv.ofInjectiveField i
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map e.symm.toAlgHom.toMonoidHom y, ?_⟩
    ext
    simp [Algebra.norm_eq_of_algEquiv]
  · rintro ⟨y, rfl⟩
    refine ⟨Units.map e.toAlgHom.toMonoidHom y, ?_⟩
    ext
    simp [Algebra.norm_eq_of_algEquiv]

variable [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  [Algebra L (AlgebraicClosure K)] [IsScalarTower K L (AlgebraicClosure K)]
  [FiniteDimensional K L] [IsAbelianGalois K L]

/-- **The kernel of an Artin restriction is the norm subgroup**: `ρ x = 1` iff `x` is the
norm of a unit of `L` — the norm-residue property of the reciprocity map at the floor `L`
([Serre 1979, Chap. XIII, §4, p.197][Serre1979];
[Milne 2020, Chap. I, §1, Thm. 1.1 (b), p.20][MilneCFT]). -/
theorem IsArtinRestriction.ker {ρ : Kˣ →* (L ≃ₐ[K] L)} (hρ : IsArtinRestriction K L ρ) :
    ρ.ker = (Units.map (Algebra.norm K : L →* K)).range := by
  obtain ⟨φ, hφ, hlift⟩ := hρ
  let i : L →ₐ[K] AlgebraicClosure K := IsScalarTower.toAlgHom K L (AlgebraicClosure K)
  let L' : IntermediateField K (AlgebraicClosure K) := i.fieldRange
  let e : L ≃ₐ[K] L' := AlgEquiv.ofInjectiveField i
  haveI : FiniteDimensional K L' := e.toLinearEquiv.finiteDimensional
  haveI : IsGalois K L' := IsGalois.of_algEquiv e
  have hcomm : ∀ σ τ : L' ≃ₐ[K] L', σ * τ = τ * σ := by
    intro σ τ
    apply (AlgEquiv.autCongr e.symm).injective
    rw [map_mul, map_mul]
    exact IsMulCommutative.is_comm.comm _ _
  have hN := hφ.normKernel L' hcomm
  rw [← range_normUnits_fieldRange K L i, ← hN]
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · intro hx
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk_surjective (φ x)
    refine ⟨σ, (IntermediateField.mem_fixingSubgroup_iff L' σ).2 ?_, hσ⟩
    rintro _ ⟨a, rfl⟩
    have h := hlift x σ hσ
    rw [hx] at h
    have hc := AlgEquiv.restrictNormal_commutes σ L a
    change AlgEquiv.restrictNormal σ L = 1 at h
    rw [h] at hc
    exact hc.symm
  · rintro ⟨σ, hσ, hσx⟩
    have h := hlift x σ hσx
    rw [← h]
    ext a
    apply (algebraMap L (AlgebraicClosure K)).injective
    change algebraMap L (AlgebraicClosure K) (AlgEquiv.restrictNormal σ L a) = _
    rw [AlgEquiv.restrictNormal_commutes]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ ⟨a, rfl⟩

/-- **An Artin restriction is surjective**: every automorphism of the floor is `ρ x` for some
`x` — with `IsArtinRestriction.ker`, the induced map is the reciprocity isomorphism
`Kˣ ⧸ N_{L/K} (Lˣ) ≃* (L ≃ₐ[K] L)` ([Serre 1979, Chap. XIII, §4, p.197][Serre1979];
[Milne 2020, Chap. I, §1, Thm. 1.1 (b), p.20][MilneCFT]). -/
theorem IsArtinRestriction.surjective {ρ : Kˣ →* (L ≃ₐ[K] L)}
    (hρ : IsArtinRestriction K L ρ) : Function.Surjective ρ := by
  rw [← MonoidHom.range_eq_top]
  let i : L →ₐ[K] AlgebraicClosure K := IsScalarTower.toAlgHom K L (AlgebraicClosure K)
  let L' : IntermediateField K (AlgebraicClosure K) := i.fieldRange
  let e : L ≃ₐ[K] L' := AlgEquiv.ofInjectiveField i
  haveI : FiniteDimensional K L' := e.toLinearEquiv.finiteDimensional
  haveI : IsAbelianGalois K L' := IsAbelianGalois.of_algHom e.symm.toAlgHom
  apply Subgroup.eq_top_of_card_eq
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv, hρ.ker,
    ← range_normUnits_fieldRange K L i, normIndexAbelian K L', ← e.toLinearEquiv.finrank_eq,
    IsGalois.card_aut_eq_finrank]

end Atlas.Knowledge
