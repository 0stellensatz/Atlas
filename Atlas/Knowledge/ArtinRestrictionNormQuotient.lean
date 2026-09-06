import Mathlib
import Atlas.Knowledge.FiniteNormQuotientEquivNormQuotient
import Atlas.Knowledge.IsArtinRestriction
import Atlas.Knowledge.IsLocalReciprocity
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.NormIndexAbelian

/-!
# norm quotient of an Artin restriction

An Artin restriction is the reciprocity isomorphism of its floor: for a finite abelian
extension `L` of a mixed-characteristic local field `K`, a map `ρ : Kˣ →* (L ≃ₐ[K] L)`
satisfying `Atlas.Knowledge.IsArtinRestriction` has kernel exactly the norm subgroup
`N_{L/K} (Lˣ)` and is surjective, and the isomorphism `Kˣ ⧸ N_{L/K} (Lˣ) ≃* (L ≃ₐ[K] L)` it
induces is declared here. This is the finite-level content of the predicate, extracted once
so that every consumer — the conductor cutoffs, the ramification compatibility — reads the
kernel off the predicate instead of unwinding the absolute map.

## Main definitions

* `IsArtinRestriction.normQuotientMulEquiv` — the induced isomorphism
  `Kˣ ⧸ N_{L/K} (Lˣ) ≃* (L ≃ₐ[K] L)`.

## Main statements

* `IsArtinRestriction.ker` — the kernel is the range of the unit norm.
* `IsArtinRestriction.surjective` — the restriction is onto the Galois group.

## Implementation notes

The kernel is the `normKernel` field of `Atlas.Knowledge.IsLocalReciprocity` read at the
range of `L` inside the algebraic closure: a lift of `φ x` restricts trivially to `L` exactly
when it fixes that range pointwise, and the field identifies the preimage of the fixing
subgroup with the norm subgroup of the range, which
`Atlas.Knowledge.normUnits_range_fieldRange` carries back to `L`. Surjectivity is a count —
the quotient by the kernel has the degree's cardinality by
`Atlas.Knowledge.normIndexAbelian`, and so does the Galois group — and the count is taken at
the range so that `L` may live in any universe, the norm-index item binding both fields in
one; the predicate itself is universe-polymorphic in `L`, and the consumers of the kernel
keep that generality. The isomorphism is Mathlib's quotient-by-kernel equivalence transported
along the kernel identity.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  (L : Type*) [Field L] [Algebra K L] [Algebra L (AlgebraicClosure K)]
  [IsScalarTower K L (AlgebraicClosure K)] [FiniteDimensional K L] [IsAbelianGalois K L]

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
  rw [← normUnits_range_fieldRange L i, ← hN]
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
`x` — the quotient by the kernel and the Galois group both have the degree's cardinality
([Serre 1979, Chap. XIII, §4, p.197][Serre1979];
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
    ← normUnits_range_fieldRange L i, normIndexAbelian K L', ← e.toLinearEquiv.finrank_eq,
    IsGalois.card_aut_eq_finrank]

/-- **The reciprocity isomorphism of the floor**, `Kˣ ⧸ N_{L/K} (Lˣ) ≃* (L ≃ₐ[K] L)`, induced
by an Artin restriction: the quotient by its kernel, read through `IsArtinRestriction.ker`,
mapped onto the Galois group by `IsArtinRestriction.surjective`
([Serre 1979, Chap. XIII, §4, p.197][Serre1979];
[Milne 2020, Chap. I, §1, Thm. 1.1 (b), p.20][MilneCFT]). -/
noncomputable def IsArtinRestriction.normQuotientMulEquiv {ρ : Kˣ →* (L ≃ₐ[K] L)}
    (hρ : IsArtinRestriction K L ρ) :
    Kˣ ⧸ (Units.map (Algebra.norm K : L →* K)).range ≃* (L ≃ₐ[K] L) :=
  (QuotientGroup.quotientMulEquivOfEq hρ.ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ρ hρ.surjective)

/-- The reciprocity isomorphism sends the class of `x` to `ρ x`. -/
theorem IsArtinRestriction.normQuotientMulEquiv_mk {ρ : Kˣ →* (L ≃ₐ[K] L)}
    (hρ : IsArtinRestriction K L ρ) (x : Kˣ) :
    hρ.normQuotientMulEquiv K L (QuotientGroup.mk x) = ρ x :=
  rfl

end Atlas.Knowledge
