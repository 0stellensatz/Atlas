import Mathlib
import Atlas.Knowledge.GaloisExtensionQuotient
import Atlas.Knowledge.IntermediateFieldUnitsFixedSubgroup
import Atlas.Knowledge.NormUnits
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.SeparableNormProduct

/-!
# abstract norm as the field norm

The engine's norm on the ambient unit module, compared with the ordinary
field norm — for every finite subextension of an algebraically closed Galois
ambient field, normal or not. Left cosets of the fixing subgroup are the
`K`-embeddings of the subextension, the coset action on a unit is evaluation
under the corresponding embedding, and the coset sum is therefore the product
of embeddings — the field norm. This is the identification through which the
valuation datum's range computation reads the engine's norm (#104).

## Main definitions

* `baseUnitsEquivGaloisAmbientFixed` — `Kˣ` as the coefficients fixed by the
  bottom fixing subgroup.
* `baseFixingCosetEquivAlgHom` — cosets of the fixing subgroup are the
  `K`-embeddings.

## Main statements

* `relativeNorm_intermediateFieldUnit_val_of_isSeparable` — the engine's
  coset norm is the field norm, without normality; proved.
* `relativeNorm_intermediateFieldUnit_of_isSeparable` — its equivariant
  form through the fixed-unit dictionaries; proved.

## Implementation notes

The comparison is stated over a separably closed ambient field, as in
the source, so it serves imperfect ground fields — the ambient of the
local instantiation is the chosen separable closure of an arbitrary
base field, whose `IsSepClosed` is Mathlib's instance while its
`IsAlgClosed` is neither an instance nor a theorem, failing exactly at
imperfect base fields. The closing product formula is the layer's
`Atlas.Knowledge.algebraMap_norm_eq_prod_embeddings_of_isSepClosed`; an
earlier revision strengthened the ambient to `IsAlgClosed` to close on
Mathlib's product formula instead, which the concrete transport cannot
instantiate, and this file records the correction. The source's
Galois-only comparison is not ported — the separable form subsumes it
at every use site.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

omit [IsSepClosed Ω] in
/-- **`Kˣ` is the coefficient group fixed by the bottom fixing subgroup**
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:32`]
[Yamaguchi2026]). -/
def baseUnitsEquivGaloisAmbientFixed :
    Additive Kˣ ≃+ ambientFixedAddSubgroup
      (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup (⊥ : IntermediateField K Ω)) := by
  let eBot : Additive Kˣ ≃+
      Additive (⊥ : IntermediateField K Ω)ˣ :=
    MulEquiv.toAdditive
      (Units.mapEquiv (IntermediateField.botEquiv K Ω).symm.toMulEquiv)
  exact eBot.trans
    (intermediateFieldUnitsEquivGaloisFixed K Ω ⊥)

omit [IsSepClosed Ω] in
/-- The base equivalence reads as the structure map on the underlying element
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:45`]
[Yamaguchi2026]). -/
@[simp]
theorem baseUnitsEquivGaloisAmbientFixed_val (x : Kˣ) :
    ((Additive.toMul
      ((baseUnitsEquivGaloisAmbientFixed K Ω (Additive.ofMul x)).1 :
        Additive Ωˣ) : Ωˣ) : Ω) = algebraMap K Ω (x : K) := by
  rfl

section CosetsAndEmbeddings

variable (E : IntermediateField K Ω)

omit [IsSepClosed Ω] in
/-- Restriction to `E` sends a left coset of its fixing subgroup to a
`K`-embedding of `E` ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean:36`]
[Yamaguchi2026]). -/
def baseFixingCosetToAlgHom :
    ((closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      (closedFixingSubgroup E).toSubgroup.subgroupOf
        (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup) →
      (E →ₐ[K] Ω) := fun q =>
  Quotient.liftOn' q
    (fun σ => σ.1.toAlgHom.comp E.val)
    (by
      intro σ τ hστ
      have hmem : σ⁻¹ * τ ∈
          (closedFixingSubgroup E).toSubgroup.subgroupOf
            (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup :=
        QuotientGroup.leftRel_apply.mp hστ
      let η : (closedFixingSubgroup E).toSubgroup :=
        ⟨(σ⁻¹ * τ).1, hmem⟩
      have hτ : τ = σ * Subgroup.inclusion
          (fixingSubgroupLeBase K Ω E) η := by
        apply Subtype.ext
        change τ.1 = σ.1 * η.1
        simp [η]
      apply AlgHom.ext
      intro x
      have hηfix :=
        (IntermediateField.mem_fixingSubgroup_iff E η.1).mp η.2
      have hηx : η.1 (x : Ω) = (x : Ω) := hηfix x x.2
      have hτ' := congrArg Subtype.val hτ
      change τ.1 = σ.1 * η.1 at hτ'
      change σ.1 (x : Ω) = τ.1 (x : Ω)
      calc
        σ.1 (x : Ω) = σ.1 (η.1 (x : Ω)) :=
          congrArg σ.1 hηx.symm
        _ = (σ.1 * η.1) (x : Ω) := rfl
        _ = τ.1 (x : Ω) := by rw [hτ'])

omit [IsSepClosed Ω] in
/-- The coset reading restricts the representative ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean:75`]
[Yamaguchi2026]). -/
@[simp]
theorem baseFixingCosetToAlgHom_mk
    (σ : (closedFixingSubgroup
      (⊥ : IntermediateField K Ω)).toSubgroup) :
    baseFixingCosetToAlgHom K Ω E (QuotientGroup.mk σ) =
      σ.1.toAlgHom.comp E.val :=
  rfl

/- Surjectivity: every embedding extends to the ambient field
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean:82`]
[Yamaguchi2026]). -/
private theorem baseFixingCosetToAlgHom_surjective
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    Function.Surjective (baseFixingCosetToAlgHom K Ω E) := by
  intro f
  letI : Algebra.IsSeparable E Ω :=
    Algebra.isSeparable_tower_top_of_isSeparable K E Ω
  obtain ⟨φ, hφ⟩ :=
    (IsSepClosed.surjective_restrictDomain_of_isSeparable
      (K := K) (L := E) (M := Ω) (E := Ω)) f
  let σ : Ω ≃ₐ[K] Ω :=
    AlgEquiv.ofBijective φ
      (Normal.toIsAlgebraic.algHom_bijective₂
        φ (AlgHom.id K Ω)).1
  have hσ : σ ∈ (closedFixingSubgroup
      (⊥ : IntermediateField K Ω)).toSubgroup := by
    change σ ∈ (⊥ : IntermediateField K Ω).fixingSubgroup
    rw [IntermediateField.fixingSubgroup_bot]
    exact Subgroup.mem_top σ
  let σbase : (closedFixingSubgroup
      (⊥ : IntermediateField K Ω)).toSubgroup := ⟨σ, hσ⟩
  refine ⟨QuotientGroup.mk σbase, ?_⟩
  apply AlgHom.ext
  intro x
  have hx := congrArg (fun ψ : E →ₐ[K] Ω => ψ x) hφ
  change φ (x : Ω) = f x
  change φ (x : Ω) = f x at hx
  exact hx

omit [IsSepClosed Ω] in
/- Injectivity: agreeing on `E` means lying in the same coset
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean:111`]
[Yamaguchi2026]). -/
private theorem baseFixingCosetToAlgHom_injective :
    Function.Injective (baseFixingCosetToAlgHom K Ω E) := by
  intro q r hqr
  rw [← Quotient.out_eq q, ← Quotient.out_eq r] at hqr ⊢
  apply Quotient.sound'
  apply QuotientGroup.leftRel_apply.mpr
  apply Subgroup.mem_subgroupOf.2
  change ((Quotient.out q)⁻¹ * Quotient.out r).1 ∈ E.fixingSubgroup
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  let y : E := ⟨x, hx⟩
  have hy := congrArg (fun ψ : E →ₐ[K] Ω => ψ y) hqr
  change (Quotient.out q).1 (y : Ω) =
    (Quotient.out r).1 (y : Ω) at hy
  change (Quotient.out q).1⁻¹ ((Quotient.out r).1 x) = x
  rw [← hy]
  simp [y]

/-- **Left cosets of the fixing subgroup are the `K`-embeddings** of a finite
separable subextension ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean:134`]
[Yamaguchi2026]). -/
def baseFixingCosetEquivAlgHom
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    ((closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      (closedFixingSubgroup E).toSubgroup.subgroupOf
        (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup) ≃
      (E →ₐ[K] Ω) :=
  Equiv.ofBijective (baseFixingCosetToAlgHom K Ω E)
    ⟨baseFixingCosetToAlgHom_injective K Ω E,
      baseFixingCosetToAlgHom_surjective K Ω E⟩

/-- The engine's relative coset space at a finite separable subextension is
finite ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean:146`]
[Yamaguchi2026]). -/
instance baseFixingExtensionQuotient_finite_of_isSeparable
    [FiniteDimensional K E] [Algebra.IsSeparable K E] :
    Finite
      ((closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup ⧸
        (closedFixingSubgroup E).toSubgroup.subgroupOf
          (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup) :=
  (baseFixingCosetEquivAlgHom K Ω E).finite_iff.mpr inferInstance

end CosetsAndEmbeddings

section NormAsProduct

variable (E : IntermediateField K Ω)
  [FiniteDimensional K E] [Algebra.IsSeparable K E]

omit [IsSepClosed Ω] [FiniteDimensional K E] [Algebra.IsSeparable K E] in
/-- The coset action on an `E`-unit is evaluation under the corresponding
embedding ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean:173`]
[Yamaguchi2026]). -/
theorem relativeCosetAction_intermediateFieldUnit_val_of_isSeparable
    (x : Eˣ)
    (q : (closedFixingSubgroup
        (⊥ : IntermediateField K Ω)).toSubgroup ⧸
      (closedFixingSubgroup E).toSubgroup.subgroupOf
        (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup) :
    ((Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q) : Ωˣ) : Ω) =
      baseFixingCosetToAlgHom K Ω E q (x : E) := by
  refine Quotient.inductionOn' q ?_
  intro σ
  rfl

/-- **The engine's coset norm is the field norm**, for every finite separable
subextension, normal or not ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean:193`]
[Yamaguchi2026]). -/
theorem relativeNorm_intermediateFieldUnit_val_of_isSeparable (x : Eˣ) :
    ((Additive.toMul
      ((relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
      algebraMap K Ω (Algebra.norm K (x : E)) := by
  let Q := (closedFixingSubgroup
      (⊥ : IntermediateField K Ω)).toSubgroup ⧸
    (closedFixingSubgroup E).toSubgroup.subgroupOf
      (closedFixingSubgroup (⊥ : IntermediateField K Ω)).toSubgroup
  letI := Fintype.ofFinite Q
  change
    ((Additive.toMul
      (relativeNormValue (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x))) : Ωˣ) : Ω) = _
  rw [relativeNormValue]
  change
    (↑(Additive.toMul (∑ q : Q,
      relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q) : Ωˣ) : Ω) = _
  rw [toMul_sum]
  change (Units.coeHom Ω) (∏ q : Q,
    Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) q)) = _
  rw [map_prod]
  change
    (∏ q : Q,
      ((Additive.toMul
        (relativeCosetAction (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E)
          (intermediateFieldUnitsEquivGaloisFixed K Ω E
            (Additive.ofMul x)) q) : Ωˣ) : Ω)) = _
  calc
    _ = ∏ σ : E →ₐ[K] Ω, σ (x : E) := by
      exact Fintype.prod_equiv
        (baseFixingCosetEquivAlgHom K Ω E)
        (fun q : Q =>
          ((Additive.toMul
            (relativeCosetAction (galoisAmbientUnitsRep K Ω)
              (closedFixingSubgroup (⊥ : IntermediateField K Ω))
              (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E)
              (intermediateFieldUnitsEquivGaloisFixed K Ω E
                (Additive.ofMul x)) q) : Ωˣ) : Ω))
        (fun σ : E →ₐ[K] Ω => σ (x : E))
        (relativeCosetAction_intermediateFieldUnit_val_of_isSeparable
          K Ω E x)
    _ = algebraMap K Ω (Algebra.norm K (x : E)) :=
      (algebraMap_norm_eq_prod_embeddings_of_isSepClosed
        K Ω ↥E (x : E)).symm

/-- Equivariant form of the nonnormal finite-separable norm comparison, with
both fixed coefficient groups identified with the corresponding field unit
groups ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableFixedFieldNorm.lean:258`]
[Yamaguchi2026]). -/
theorem relativeNorm_intermediateFieldUnit_of_isSeparable (x : Eˣ) :
    relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E)
        (intermediateFieldUnitsEquivGaloisFixed K Ω E
          (Additive.ofMul x)) =
      baseUnitsEquivGaloisAmbientFixed K Ω
        (Additive.ofMul (normUnits K E x)) := by
  apply Subtype.ext
  apply Additive.ext
  apply Units.ext
  exact relativeNorm_intermediateFieldUnit_val_of_isSeparable K Ω E x

end NormAsProduct

end

end Atlas.Knowledge
