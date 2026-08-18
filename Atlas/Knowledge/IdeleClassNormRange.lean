import Mathlib
import Atlas.Knowledge.IdeleClassGroup

/-!
# idele class norm range

The norm subgroup `N_{L/K} (C_L) ≤ C_K` of a finite extension of number fields, on the
tensor model: the image in the idele class group of the units of `𝔸_K ⊗[K] L` under the
`𝔸_K`-algebra norm, carried through the adele-units comparison of
`Atlas.Knowledge.IdeleGroup`. This is the subgroup every statement of global class field
theory quantifies over — the reciprocity kernel, the existence theorem's image, the
conductor's object — and it is definable from pinned Mathlib exactly because the tensor
model sidesteps completions: Mathlib has no algebra structure between adic completions at
places over places and no adele base change, but `𝔸_K ⊗[K] L` is a finite free
`𝔸_K`-algebra by base change alone. What the model owes the classical vocabulary is
proved here where it is cheap: the principal idele of a field norm lies in the subgroup.

## Main definitions

* `ideleClassNormRange` — `N_{L/K} (C_L)` as a subgroup of `IdeleClassGroup K`.

## Main statements

* `principalIdele_norm_mem_ideleClassNormRange` — the diagonal of `N_{L/K} (x)` is in the
  norm subgroup; proved.
* `norm_one_tmul` — `Algebra.norm 𝔸_K (1 ⊗ x) = algebraMap (Algebra.norm K x)`; proved,
  the base-change norm compatibility Mathlib does not yet state.

## Implementation notes

The classical `N_{L/K} : C_L → C_K` (Milne's componentwise `b_v = ∏_{w ∣ v} Nm (a_w)`,
p.177) presents the same subgroup through the decomposition `𝔸_K ⊗ L ≅ 𝔸_L`; that
equivalence is completion-comparison machinery this layer does not yet have, so the
subgroup is *defined* on the tensor side and the componentwise reading is recorded as its
classical face — the source's identification is the base-change equivalence
(`AlgebraicNumberTheory/Idele/BaseChange.lean:554`) with the norm transported through it
(`AlgebraicNumberTheory/Idele/Extension/IdeleNorm.lean:36`), and its own norm is built the
same way (`AlgebraicNumberTheory/Idele/Extension/BaseChange.lean:104`). Because
`Algebra.norm` is total with junk value `1`, only `[FiniteDimensional K L]` is
load-bearing — off it the norm degenerates and the subgroup collapses — and no
`NumberField` structure on `L` enters at all.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- The **norm subgroup** `N_{L/K} (C_L)` of the idele class group, on the tensor model:
the image of `(𝔸_K ⊗[K] L)ˣ` under the `𝔸_K`-algebra norm, read through the adele-units
comparison and the class-group projection
([Milne 2020, Chap. V, §4, p.177, and §5, Thm. 5.3, pp.178–179][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/Extension/BaseChange.lean:104`]
[Yamaguchi2026]). -/
noncomputable def ideleClassNormRange
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] :
    Subgroup (IdeleClassGroup K) :=
  MonoidHom.range
    ((QuotientGroup.mk' (principalIdeleSubgroup K)).comp
      ((ideleGroupEquivAdeleRingUnits K).symm.toMonoidHom.comp
        (Units.map (Algebra.norm (AdeleRing (𝓞 K) K) :
          (AdeleRing (𝓞 K) K ⊗[K] L) →* AdeleRing (𝓞 K) K))))

/-- The adelic norm of `1 ⊗ x` is the diagonal image of the field norm — the base-change
compatibility of `Algebra.norm`, proved from `LinearMap.det_baseChange`
([Milne 2020, Chap. V, §4, p.177][MilneCFT]). -/
theorem norm_one_tmul (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] (x : L) :
    Algebra.norm (AdeleRing (𝓞 K) K) ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] x) =
      algebraMap K (AdeleRing (𝓞 K) K) (Algebra.norm K x) := by
  rw [Algebra.norm_apply, Algebra.norm_apply]
  have h : Algebra.lmul (AdeleRing (𝓞 K) K) (AdeleRing (𝓞 K) K ⊗[K] L)
        ((1 : AdeleRing (𝓞 K) K) ⊗ₜ[K] x) =
      (Algebra.lmul K L x).baseChange (AdeleRing (𝓞 K) K) := by
    apply LinearMap.restrictScalars_injective K
    apply TensorProduct.ext'
    intro a l
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [h, LinearMap.det_baseChange]

/-- The principal idele of a field norm lies in the norm subgroup: the tensor model owes
the classical vocabulary its diagonal compatibility, and pays
([Milne 2020, Chap. V, §4, p.177][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/Extension/BaseChange.lean:161`]
[Yamaguchi2026]). -/
theorem principalIdele_norm_mem_ideleClassNormRange
    (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L] (x : Lˣ) :
    QuotientGroup.mk' (principalIdeleSubgroup K)
        (principalIdele K (Units.map (Algebra.norm K : L →* K) x)) ∈
      ideleClassNormRange K L := by
  refine MonoidHom.mem_range.2
    ⟨Units.map (Algebra.TensorProduct.includeRight :
        L →ₐ[K] AdeleRing (𝓞 K) K ⊗[K] L).toRingHom.toMonoidHom x, ?_⟩
  have hnorm :
      Units.map (Algebra.norm (AdeleRing (𝓞 K) K) :
          (AdeleRing (𝓞 K) K ⊗[K] L) →* AdeleRing (𝓞 K) K)
        (Units.map (Algebra.TensorProduct.includeRight :
          L →ₐ[K] AdeleRing (𝓞 K) K ⊗[K] L).toRingHom.toMonoidHom x) =
      Units.map (algebraMap K (AdeleRing (𝓞 K) K)).toMonoidHom
        (Units.map (Algebra.norm K : L →* K) x) := by
    ext
    simpa using norm_one_tmul K L (x : L)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  rw [hnorm]
  rfl

end Atlas.Knowledge

end
