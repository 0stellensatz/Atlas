import Mathlib
import Atlas.Knowledge.FiniteResidueFrobenius

/-!
# Frobenius on an infinite residue extension

The finite Frobenius coordinates commute with restriction, so they assemble in
the inverse-limit presentation of an infinite Galois group: the canonical
continuous homomorphism `ℤ̂ → Gal(Ω/k)` for an algebraic Galois extension of a
finite field, restricting on every finite Galois intermediate field to the
finite coordinates, with `1 ∈ ℤ̂` acting as the actual arithmetic Frobenius.
The construction itself requires no bijectivity — that is the next brick's
content.

## Main definitions

* `residueAbsoluteFrobenius` — the continuous `ℤ̂ → Gal(Ω/k)`.

## Main statements

* `restrictNormalHom_residueAbsoluteFrobenius` — restriction recovers the
  finite coordinates; proved.
* `residueAbsoluteFrobenius_one` — `1 ∈ ℤ̂` acts as the arithmetic Frobenius
  on the whole extension; proved.

## Implementation notes

The limit point is a compatible family over Mathlib's
`InfiniteGalois.asProfiniteGaloisGroupFunctor`, compatibility being the tower
law of the finite coordinates, and the assembly composes with the inverse of
Mathlib's `InfiniteGalois.continuousMulEquivToLimit`; continuity holds because
each component lands in a discrete finite group.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp

variable (k : Type u) (Omega : Type v)
  [Field k] [Fintype k] [Field Omega] [Algebra k Omega]
  [IsGalois k Omega]

/-- The finite Frobenius action on a finite Galois intermediate field. -/
def finiteResidueFrobeniusIntermediate
    (E : FiniteGaloisIntermediateField k Omega) :
    ProfiniteIntegerMul →ₜ* (E ≃ₐ[k] E) := by
  letI : Finite E := Module.finite_of_finite k
  exact finiteResidueFrobeniusFromZHat k E

/- The compatible finite Frobenius coordinates attached to one profinite
integer. -/
private def residueFrobeniusLimitPoint (z : ProfiniteIntegerMul) :
    limit (InfiniteGalois.asProfiniteGaloisGroupFunctor k Omega) where
  val := fun E => finiteResidueFrobeniusIntermediate k Omega E.unop z
  property := by
    intro E F f
    algebraize [Subsemiring.inclusion <| leOfHom f.1]
    haveI : IsScalarTower k F.unop E.unop :=
      IsScalarTower.of_algebraMap_eq (congrFun rfl)
    letI : Finite F.unop := Module.finite_of_finite k
    letI : Finite E.unop := Module.finite_of_finite k
    change AlgEquiv.restrictNormalHom F.unop
        (finiteResidueFrobeniusFromZHat k E.unop z) =
      finiteResidueFrobeniusFromZHat k F.unop z
    exact restrictNormalHom_finiteResidueFrobeniusFromZHat
      (k := k) (E := F.unop) (F := E.unop) z

/-- The compatible Frobenius coordinates as a continuous homomorphism into the
finite-Galois inverse limit. -/
def residueFrobeniusToLimit :
    ProfiniteIntegerMul →ₜ*
      limit (InfiniteGalois.asProfiniteGaloisGroupFunctor k Omega) where
  toFun := residueFrobeniusLimitPoint k Omega
  map_one' := by
    apply Subtype.ext
    funext E
    exact (finiteResidueFrobeniusIntermediate k Omega E.unop).map_one
  map_mul' x y := by
    apply Subtype.ext
    funext E
    exact (finiteResidueFrobeniusIntermediate k Omega E.unop).map_mul x y
  continuous_toFun := by
    have hcontinuous (E : (FiniteGaloisIntermediateField k Omega)ᵒᵖ) :
        @Continuous ProfiniteIntegerMul (E.unop ≃ₐ[k] E.unop)
          inferInstance (krullTopology k E.unop)
          (finiteResidueFrobeniusIntermediate k Omega E.unop) :=
      (finiteResidueFrobeniusIntermediate k Omega E.unop).continuous_toFun
    letI (E : (FiniteGaloisIntermediateField k Omega)ᵒᵖ) :
        TopologicalSpace (E.unop ≃ₐ[k] E.unop) :=
      ((InfiniteGalois.asProfiniteGaloisGroupFunctor k
        Omega).obj E).toProfinite.toTop.str
    apply Continuous.subtype_mk
    exact continuous_pi fun E => by
      change @Continuous ProfiniteIntegerMul (E.unop ≃ₐ[k] E.unop)
        inferInstance inferInstance
        (finiteResidueFrobeniusIntermediate k Omega E.unop)
      rw [show
        (inferInstance : TopologicalSpace (E.unop ≃ₐ[k] E.unop)) =
          krullTopology k E.unop by
        change (⊥ : TopologicalSpace (E.unop ≃ₐ[k] E.unop)) =
          krullTopology k E.unop
        exact (@DiscreteTopology.eq_bot _
          (krullTopology k E.unop) inferInstance).symm]
      exact hcontinuous E

omit [IsGalois k Omega] in
/-- The limit map computes componentwise. -/
@[simp]
theorem residueFrobeniusToLimit_apply_component (z : ProfiniteIntegerMul)
    (E : (FiniteGaloisIntermediateField k Omega)ᵒᵖ) :
    (residueFrobeniusToLimit k Omega z).val E =
      finiteResidueFrobeniusIntermediate k Omega E.unop z :=
  rfl

/-- **The Frobenius-parameter homomorphism** `ℤ̂ → Gal(Ω/k)` for an algebraic
Galois extension of a finite field
([Milne 2020, Chap. I, Appendix A, p.55][MilneCFT] — the Galois group as the
projective limit of the finite ones;
[Yamaguchi 2026, `LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAbsoluteFrobenius.lean:102`]
[Yamaguchi2026]). -/
def residueAbsoluteFrobenius : ProfiniteIntegerMul →ₜ* (Omega ≃ₐ[k] Omega) :=
  (ContinuousMonoidHom.toContinuousMonoidHom
    (InfiniteGalois.continuousMulEquivToLimit k Omega).symm).comp
    (residueFrobeniusToLimit k Omega)

/-- **Restriction recovers the finite coordinates**. -/
theorem restrictNormalHom_residueAbsoluteFrobenius
    (z : ProfiniteIntegerMul) (E : FiniteGaloisIntermediateField k Omega) :
    AlgEquiv.restrictNormalHom E (residueAbsoluteFrobenius k Omega z) =
      finiteResidueFrobeniusIntermediate k Omega E z := by
  have hcomponent := congrArg (fun q => q.val (op E))
    ((InfiniteGalois.continuousMulEquivToLimit k Omega).apply_symm_apply
      (residueFrobeniusToLimit k Omega z))
  exact hcomponent

/-- `1 ∈ ℤ̂` gives the arithmetic Frobenius on every finite Galois
subextension. -/
theorem restrictNormalHom_residueAbsoluteFrobenius_one
    (E : FiniteGaloisIntermediateField k Omega) :
    AlgEquiv.restrictNormalHom E
        (residueAbsoluteFrobenius k Omega
          (Multiplicative.ofAdd (1 : ProfiniteInteger))) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E := by
  rw [restrictNormalHom_residueAbsoluteFrobenius]
  letI : Finite E := Module.finite_of_finite k
  exact finiteResidueFrobeniusFromZHat_one k E

/-- The arithmetic Frobenius restricts to the arithmetic Frobenius on every
finite Galois intermediate field. -/
theorem restrictNormalHom_frobeniusAlgEquivOfAlgebraic
    (E : FiniteGaloisIntermediateField k Omega) :
    AlgEquiv.restrictNormalHom E
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E Omega).injective
  calc
    algebraMap E Omega
        ((AlgEquiv.restrictNormalHom E
          (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)) x) =
        FiniteField.frobeniusAlgEquivOfAlgebraic k Omega
          (algebraMap E Omega x) :=
      AlgEquiv.restrictNormal_commutes
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega) E x
    _ = algebraMap E Omega
        (FiniteField.frobeniusAlgEquivOfAlgebraic k E x) := by
      simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
      exact (map_pow (algebraMap E Omega) x (Fintype.card k)).symm

/-- **`1 ∈ ℤ̂` acts as the arithmetic Frobenius on the whole extension**
([Yamaguchi 2026, `LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAbsoluteFrobenius.lean:156`]
[Yamaguchi2026]). -/
@[simp]
theorem residueAbsoluteFrobenius_one :
    residueAbsoluteFrobenius k Omega
        (Multiplicative.ofAdd (1 : ProfiniteInteger)) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k Omega := by
  apply (InfiniteGalois.continuousMulEquivToLimit k Omega).injective
  apply Subtype.ext
  funext E
  change AlgEquiv.restrictNormalHom E.unop
      (residueAbsoluteFrobenius k Omega
        (Multiplicative.ofAdd (1 : ProfiniteInteger))) =
    AlgEquiv.restrictNormalHom E.unop
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)
  rw [restrictNormalHom_residueAbsoluteFrobenius_one,
    restrictNormalHom_frobeniusAlgEquivOfAlgebraic]

end

end Atlas.Knowledge
