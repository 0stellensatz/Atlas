import Mathlib
import Atlas.Knowledge.AbstractExtensionUnitsRepIso
import Atlas.Knowledge.NormUnits
import Atlas.Knowledge.SeparableFixedFieldNorm

/-!
# relative norms on fixed fields

The abstract relative norm on fixed units is the field norm between the corresponding fixed
fields. The relative extension need not be normal: its left cosets are identified with field
embeddings into the separably closed ambient field, and both norms are the product over those
embeddings.

## Main statements

* `relativeNorm_abstractFixedFieldUnit_eq_normUnits` — the abstract relative norm is the
  ordinary unit norm, without a normality hypothesis.

## Implementation notes

This extends the Galois comparison in `Atlas.Knowledge.AbstractRelativeUnitsNorm` to the
nonnormal base changes of `Atlas.Knowledge.ArtinMapNormNaturality`. The base and ambient
fields occupy independent universes. The source's relative subgroup is expressed as
`Subgroup.subgroupOf`, and finite sets of embeddings use Mathlib's existing `Fintype` instance.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable (k : Type u) (Ω : Type v) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω] [IsSepClosed Ω]

/-- A left coset of the abstract fixing subgroup restricts to an embedding
of the upper concrete fixed field into the common ambient field.
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldRelativeNorm.lean:37`). -/
def abstractFixedFieldCosetToAlgHom
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) →
      (abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω) := fun q =>
  Quotient.liftOn' q
    (fun σ => (abstractSubgroupEquivGaloisGroup k Ω K σ).toAlgHom.comp
      (abstractRelativeFixedField k Ω hLK).val)
    (by
      intro σ τ hστ
      have hmem : σ⁻¹ * τ ∈ L.toSubgroup.subgroupOf K.toSubgroup :=
        QuotientGroup.leftRel_apply.mp hστ
      let η : L.toSubgroup := ⟨(σ⁻¹ * τ).1, hmem⟩
      have hτ : τ = σ * Subgroup.inclusion hLK η := by
        apply Subtype.ext
        change τ.1 = σ.1 * η.1
        simp [η]
      apply AlgHom.ext
      intro x
      have hηfix : η.1 (x : Ω) = (x : Ω) :=
        (IntermediateField.mem_fixedField_iff L.toSubgroup
          (x : Ω)).1 x.property η.1 η.2
      change σ.1 (x : Ω) = τ.1 (x : Ω)
      calc
        σ.1 (x : Ω) = σ.1 (η.1 (x : Ω)) :=
          congrArg σ.1 hηfix.symm
        _ = (σ.1 * η.1) (x : Ω) := rfl
        _ = τ.1 (x : Ω) := by
          have hτ' := congrArg Subtype.val hτ
          change τ.1 = σ.1 * η.1 at hτ'
          rw [hτ'])

omit [IsSepClosed Ω] in
/-- The embedding attached to a coset representative is its restriction to the upper field
(Yamaguchi 2026, `FixedFieldRelativeNorm.lean:73`). -/
@[simp]
theorem abstractFixedFieldCosetToAlgHom_mk
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) (σ : K.toSubgroup) :
    abstractFixedFieldCosetToAlgHom k Ω K L hLK
        (QuotientGroup.mk σ) =
      (abstractSubgroupEquivGaloisGroup k Ω K σ).toAlgHom.comp
        (abstractRelativeFixedField k Ω hLK).val :=
  rfl

private theorem abstractFixedFieldCosetToAlgHom_surjective
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK)] :
    Function.Surjective
      (abstractFixedFieldCosetToAlgHom k Ω K L hLK) := by
  intro f
  letI : Algebra.IsSeparable (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) Ω
  letI : Algebra.IsSeparable (abstractRelativeFixedField k Ω hLK) Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) Ω
  obtain ⟨φ, hφ⟩ :=
    (IsSepClosed.surjective_restrictDomain_of_isSeparable
      (K := abstractFixedField k Ω K)
      (L := abstractRelativeFixedField k Ω hLK)
      (M := Ω) (E := Ω)) f
  let σReal : Gal(Ω/abstractFixedField k Ω K) :=
    AlgEquiv.ofBijective φ
      (Normal.toIsAlgebraic.algHom_bijective₂
        φ (AlgHom.id (abstractFixedField k Ω K) Ω)).1
  let σ : K.toSubgroup :=
    (abstractSubgroupEquivGaloisGroup k Ω K).symm σReal
  refine ⟨QuotientGroup.mk σ, ?_⟩
  apply AlgHom.ext
  intro x
  have hx := congrArg
    (fun ψ : abstractRelativeFixedField k Ω hLK →ₐ[
      abstractFixedField k Ω K] Ω => ψ x) hφ
  change σReal (x : Ω) = f x
  change φ (x : Ω) = f x at hx
  exact hx

omit [IsSepClosed Ω] in
private theorem abstractFixedFieldCosetToAlgHom_injective
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    Function.Injective
      (abstractFixedFieldCosetToAlgHom k Ω K L hLK) := by
  intro q r hqr
  rw [← Quotient.out_eq q, ← Quotient.out_eq r] at hqr ⊢
  apply Quotient.sound'
  apply QuotientGroup.leftRel_apply.mpr
  have hfix : (Quotient.out q).1⁻¹ * (Quotient.out r).1 ∈
      (abstractFixedField k Ω L).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    let y : abstractRelativeFixedField k Ω hLK := ⟨x, hx⟩
    have hy := congrArg
      (fun ψ : abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω => ψ y) hqr
    change (Quotient.out q).1 (y : Ω) =
      (Quotient.out r).1 (y : Ω) at hy
    change (Quotient.out q).1⁻¹ ((Quotient.out r).1 x) = x
    rw [← hy]
    simp [y]
  rw [InfiniteGalois.fixingSubgroup_fixedField L] at hfix
  change (Quotient.out q).1⁻¹ * (Quotient.out r).1 ∈ L.toSubgroup
  exact hfix

/-- Abstract relative left cosets are precisely the embeddings of the upper
concrete fixed field into the ambient separably closed field.
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldRelativeNorm.lean:151`). -/
def abstractFixedFieldCosetEquivAlgHom
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK)] :
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) ≃
      (abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω) :=
  Equiv.ofBijective (abstractFixedFieldCosetToAlgHom k Ω K L hLK)
    ⟨abstractFixedFieldCosetToAlgHom_injective k Ω K L hLK,
      abstractFixedFieldCosetToAlgHom_surjective k Ω K L hLK⟩

omit [IsSepClosed Ω] in
/-- The action of a relative coset on a fixed-field unit is evaluation under its associated
field embedding. (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldRelativeNorm.lean:165`). -/
theorem relativeCosetAction_abstractFixedFieldUnit_val
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (x : (abstractRelativeFixedField k Ω hLK)ˣ)
    (q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :
    ((Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω) =
      abstractFixedFieldCosetToAlgHom k Ω K L hLK q
        (x : abstractRelativeFixedField k Ω hLK) := by
  refine Quotient.inductionOn' q ?_
  intro σ
  rfl

/-- The class-formation relative norm on fixed coefficients is the ordinary
field norm between the two concrete fixed fields, without a normality
assumption on the intermediate extension. (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FixedFieldRelativeNorm.lean:184`). -/
theorem relativeNorm_abstractFixedFieldUnit_eq_normUnits
    (K L : ClosedSubgroup (Gal(Ω/k)))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    [hKabsolute : Finite
      ((baseField Gal(Ω/k)).toSubgroup ⧸
        K.toSubgroup.subgroupOf (baseField Gal(Ω/k)).toSubgroup)]
    (x : (abstractRelativeFixedField k Ω hLK)ˣ) :
    relativeNorm (galoisAmbientUnitsRep k Ω) K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) =
      abstractFixedFieldUnitsEquivGaloisFixed k Ω K
        (Additive.ofMul
          (normUnits (abstractFixedField k Ω K)
            (abstractRelativeFixedField k Ω hLK) x)) := by
  letI : FiniteDimensional (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    abstractRelativeFixedField_finiteDimensional
      k Ω K L hLK hKabsolute hfinite
  letI : Algebra.IsSeparable (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) :=
    Algebra.isSeparable_tower_bot_of_isSeparable
      (abstractFixedField k Ω K)
      (abstractRelativeFixedField k Ω hLK) Ω
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  let Q := K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup
  letI := Fintype.ofFinite Q
  change
    ((Additive.toMul
      (relativeNormValue (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x))) : Ωˣ) : Ω) = _
  rw [relativeNormValue]
  change
    (↑(Additive.toMul (∑ q : Q,
      relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω) = _
  rw [toMul_sum]
  change (Units.coeHom Ω) (∏ q : Q,
    Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep k Ω)
        K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed
          k Ω K L hLK (Additive.ofMul x)) q)) = _
  rw [map_prod]
  change
    (∏ q : Q,
      ((Additive.toMul
        (relativeCosetAction (galoisAmbientUnitsRep k Ω)
          K L hLK
          (abstractRelativeFixedFieldUnitsEquivGaloisFixed
            k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω)) = _
  calc
    _ = ∏ σ : abstractRelativeFixedField k Ω hLK →ₐ[
        abstractFixedField k Ω K] Ω,
        σ (x : abstractRelativeFixedField k Ω hLK) := by
      exact Fintype.prod_equiv
        (abstractFixedFieldCosetEquivAlgHom k Ω K L hLK)
        (fun q : Q =>
          ((Additive.toMul
            (relativeCosetAction (galoisAmbientUnitsRep k Ω)
              K L hLK
              (abstractRelativeFixedFieldUnitsEquivGaloisFixed
                k Ω K L hLK (Additive.ofMul x)) q) : Ωˣ) : Ω))
        (fun σ : abstractRelativeFixedField k Ω hLK →ₐ[
          abstractFixedField k Ω K] Ω =>
            σ (x : abstractRelativeFixedField k Ω hLK))
        (relativeCosetAction_abstractFixedFieldUnit_val
          k Ω K L hLK x)
    _ = algebraMap (abstractFixedField k Ω K) Ω
        (Algebra.norm (abstractFixedField k Ω K)
          (x : abstractRelativeFixedField k Ω hLK)) :=
      (algebraMap_norm_eq_prod_embeddings_of_isSepClosed
        (abstractFixedField k Ω K) Ω
        (abstractRelativeFixedField k Ω hLK)
        (x : abstractRelativeFixedField k Ω hLK)).symm


end

end Atlas.Knowledge
