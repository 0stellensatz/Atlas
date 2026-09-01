import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ResidueDatumIn

/-!
# units of an intermediate field as a fixed subgroup

The coefficient-module dictionary of the reciprocity engine: for the Galois
representation on the ambient units — Mathlib's `Rep.ofAlgebraAutOnUnits`,
written additively — the subgroup fixed by the fixing subgroup of an
intermediate field `E` is exactly the image of `Eˣ`, and the identification
is a canonical additive equivalence. The embedded form, for an extension
realized by an embedding into the ambient field, is what the engine's finite
abstract extensions instantiate to (#104).

## Main definitions

* `intermediateFieldUnitsEquivGaloisFixed` — `Eˣ ≃ A^{Gal(Ω/E)}`.
* `embeddedFieldUnitsEquivGaloisFixed` — the same along an embedding.

## Main statements

* `mem_galoisAmbientUnits_fixed_iff` — an ambient unit is fixed by
  `Gal(Ω/E)` exactly when it lies in `E`; proved.
* `intermediateFieldUnitsToGaloisAmbient_range` — the image of `Eˣ` is the
  fixed subgroup; proved.

## Implementation notes

The source names the representation `galoisAmbientUnitsRep`, an abbreviation
of Mathlib's `Rep.ofAlgebraAutOnUnits`; the layer spells the Mathlib name.
The source works over `Type` and notes Mathlib's `Rep` once fixed the acting
group to universe zero; that restriction is gone, and the file is
universe-polymorphic like the rest of the engine layer.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v w

variable (K : Type u) (Ω : Type v) [Field K] [Field Ω] [Algebra K Ω]

/-- Inclusion of the units of an intermediate field into the ambient units,
in additive notation ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean:34`]
[Yamaguchi2026]). -/
def intermediateFieldUnitsToGaloisAmbient
    (E : IntermediateField K Ω) :
    Additive Eˣ →+ Additive Ωˣ :=
  MonoidHom.toAdditive (Units.map E.val.toRingHom)

/-- The inclusion computes as the mapped unit ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean:41`]
[Yamaguchi2026]). -/
@[simp]
theorem intermediateFieldUnitsToGaloisAmbient_apply
    (E : IntermediateField K Ω) (x : Eˣ) :
    intermediateFieldUnitsToGaloisAmbient K Ω E (Additive.ofMul x) =
      Additive.ofMul (Units.map E.val.toRingHom x) :=
  rfl

variable [IsGalois K Ω]

/-- **An ambient unit is fixed by `Gal(Ω/E)` exactly when it lies in `E`**
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean:51`]
[Yamaguchi2026]). -/
theorem mem_galoisAmbientUnits_fixed_iff
    (E : IntermediateField K Ω)
    (x : Additive Ωˣ) :
    x ∈ ambientFixedAddSubgroup (Rep.ofAlgebraAutOnUnits K Ω)
        (closedFixingSubgroup E) ↔
      ((Additive.toMul x : Ωˣ) : Ω) ∈ E := by
  change
    (show Rep.ofAlgebraAutOnUnits K Ω from x) ∈
        ambientFixedAddSubgroup (Rep.ofAlgebraAutOnUnits K Ω)
          (closedFixingSubgroup E) ↔
      ((Additive.toMul x : Ωˣ) : Ω) ∈ E
  rw [mem_ambientFixedAddSubgroup_iff]
  constructor
  · intro hx
    rw [← InfiniteGalois.fixedField_fixingSubgroup E,
      IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have hσclosed :
        σ ∈ (closedFixingSubgroup E).toSubgroup := by
      simpa only [closedFixingSubgroup] using hσ
    have hfixed := hx ⟨σ, hσclosed⟩
    have hρ :
        (Rep.ofAlgebraAutOnUnits K Ω).ρ σ x =
          Additive.ofMul
            (Units.mapEquiv σ.toMulEquiv (Additive.toMul x)) :=
      rfl
    rw [hρ] at hfixed
    have hval := congrArg
      (fun z : Additive Ωˣ ↦ ((Additive.toMul z : Ωˣ) : Ω)) hfixed
    convert hval using 1
    rfl
  · intro hx σ
    have hσE : σ.1 ∈ E.fixingSubgroup := by
      simpa only [closedFixingSubgroup] using σ.2
    have hρ :
        (Rep.ofAlgebraAutOnUnits K Ω).ρ
            (σ : Ω ≃ₐ[K] Ω) x =
          Additive.ofMul
            (Units.mapEquiv
              (σ : Ω ≃ₐ[K] Ω).toMulEquiv (Additive.toMul x)) :=
      rfl
    rw [hρ]
    apply Additive.ext
    rw [toMul_ofMul]
    apply Units.ext
    convert (IntermediateField.mem_fixingSubgroup_iff E σ.1).1 hσE _ hx using 1
    rfl

/-- **The image of `Eˣ` in the ambient units is the fixed subgroup** the
engine attaches to `E` ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean:101`]
[Yamaguchi2026]). -/
theorem intermediateFieldUnitsToGaloisAmbient_range
    (E : IntermediateField K Ω) :
    (intermediateFieldUnitsToGaloisAmbient K Ω E).range =
      ambientFixedAddSubgroup (Rep.ofAlgebraAutOnUnits K Ω)
        (closedFixingSubgroup E) := by
  apply AddSubgroup.ext
  intro x
  constructor
  · rintro ⟨y, rfl⟩
    change
      (show Rep.ofAlgebraAutOnUnits K Ω from
        intermediateFieldUnitsToGaloisAmbient K Ω E y) ∈
        ambientFixedAddSubgroup (Rep.ofAlgebraAutOnUnits K Ω)
          (closedFixingSubgroup E)
    apply (mem_galoisAmbientUnits_fixed_iff K Ω E _).2
    rw [← ofMul_toMul y, intermediateFieldUnitsToGaloisAmbient_apply,
      toMul_ofMul, Units.coe_map]
    exact (Additive.toMul y : Eˣ).1.property
  · intro hx
    have hxE :
        ((Additive.toMul x : Ωˣ) : Ω) ∈ E :=
      (mem_galoisAmbientUnits_fixed_iff K Ω E x).1 hx
    let y₀ : E :=
      ⟨((Additive.toMul x : Ωˣ) : Ω), hxE⟩
    have hy₀ : y₀ ≠ 0 := by
      intro h
      have h' :
          ((Additive.toMul x : Ωˣ) : Ω) = 0 :=
        congrArg E.val h
      exact (Additive.toMul x : Ωˣ).ne_zero h'
    let y : Eˣ := Units.mk0 y₀ hy₀
    refine ⟨Additive.ofMul y, ?_⟩
    rw [intermediateFieldUnitsToGaloisAmbient_apply]
    apply Additive.ext
    rw [toMul_ofMul]
    apply Units.ext
    rw [Units.coe_map]
    rfl

/-- **The canonical additive equivalence `Eˣ ≃ A^{Gal(Ω/E)}`** for the
ambient-unit representation ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean:142`]
[Yamaguchi2026]). -/
def intermediateFieldUnitsEquivGaloisFixed
    (E : IntermediateField K Ω) :
    Additive Eˣ ≃+ ambientFixedAddSubgroup (Rep.ofAlgebraAutOnUnits K Ω)
      (closedFixingSubgroup E) := by
  let eRange : Additive Eˣ ≃+
      (intermediateFieldUnitsToGaloisAmbient K Ω E).range :=
    AddMonoidHom.ofInjective (by
      intro x y hxy
      apply Additive.toMul.injective
      exact (Units.map_injective E.val.injective) (congrArg Additive.toMul hxy))
  exact eRange.trans
    (AddEquiv.addSubgroupCongr
      (intermediateFieldUnitsToGaloisAmbient_range K Ω E))

/-- The equivalence forgets to the inclusion ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean:158`]
[Yamaguchi2026]). -/
@[simp]
theorem intermediateFieldUnitsEquivGaloisFixed_coe
    (E : IntermediateField K Ω) (x : Additive Eˣ) :
    (intermediateFieldUnitsEquivGaloisFixed K Ω E x).1 =
        intermediateFieldUnitsToGaloisAmbient K Ω E x :=
  rfl

/-- **The fixed coefficient group of an embedded extension is its unit
group**: the form the engine's realized finite extensions use
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean:168`]
[Yamaguchi2026]). -/
def embeddedFieldUnitsEquivGaloisFixed
    (L : Type w) [Field L] [Algebra K L]
    (i : L →ₐ[K] Ω) :
    Additive Lˣ ≃+ ambientFixedAddSubgroup (Rep.ofAlgebraAutOnUnits K Ω)
      (closedFixingSubgroup (AlgHom.fieldRange i)) :=
  (MulEquiv.toAdditive
    (Units.mapEquiv (AlgEquiv.ofInjectiveField i).toMulEquiv)).trans
      (intermediateFieldUnitsEquivGaloisFixed K Ω (AlgHom.fieldRange i))

/-- The embedded equivalence forgets to the mapped unit ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbsoluteUnitsFixedField.lean:179`]
[Yamaguchi2026]). -/
@[simp]
theorem embeddedFieldUnitsEquivGaloisFixed_coe
    (L : Type w) [Field L] [Algebra K L]
    (i : L →ₐ[K] Ω) (x : Lˣ) :
    (embeddedFieldUnitsEquivGaloisFixed K Ω L i (Additive.ofMul x)).1 =
      Additive.ofMul (Units.map i.toRingHom.toMonoidHom x) :=
  rfl

end

end Atlas.Knowledge
