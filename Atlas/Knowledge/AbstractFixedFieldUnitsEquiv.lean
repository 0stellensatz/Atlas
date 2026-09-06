import Mathlib
import Atlas.Knowledge.AbstractFixedField
import Atlas.Knowledge.IntermediateFieldUnitsFixedSubgroup

/-!
# units of an abstract fixed field as fixed coefficients

The engine-facing form of the units dictionary: for an arbitrary closed
subgroup `H`, the units of its concrete fixed field are canonically the
coefficients of the ambient-unit representation fixed by `H` itself — not
merely by the fixing subgroup of the fixed field. This is the identification
the valuation datum's norm-range computation consumes (#104).

## Main definitions

* `abstractFixedFieldUnitsEquivGaloisFixed` — the units of the fixed field
  of `H`, identified with `A^H`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable (k : Type u) (Ω : Type v) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω]

/-- **The units of the fixed field of a closed subgroup are the coefficients
it fixes** (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean:32`). -/
def abstractFixedFieldUnitsEquivGaloisFixed
    (H : ClosedSubgroup (Ω ≃ₐ[k] Ω)) :
    Additive (abstractFixedField k Ω H)ˣ ≃+
      ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) H where
  toFun x := ⟨intermediateFieldUnitsToGaloisAmbient k Ω
      (abstractFixedField k Ω H) x, by
    intro σ
    apply Additive.ext
    apply Units.ext
    exact (IntermediateField.mem_fixedField_iff H.toSubgroup
      ((Additive.toMul x : (abstractFixedField k Ω H)ˣ) : Ω)).1
        (Additive.toMul x : (abstractFixedField k Ω H)ˣ).1.property σ.1 σ.2⟩
  invFun a := by
    have ha : ((Additive.toMul a.1 : Ωˣ) : Ω) ∈
        abstractFixedField k Ω H := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hfixed := a.2 ⟨σ, hσ⟩
      exact congrArg
        (fun z : Additive Ωˣ => ((Additive.toMul z : Ωˣ) : Ω)) hfixed
    let y₀ : abstractFixedField k Ω H :=
      ⟨((Additive.toMul a.1 : Ωˣ) : Ω), ha⟩
    have hy₀ : y₀ ≠ 0 := by
      intro h
      have h' : ((Additive.toMul a.1 : Ωˣ) : Ω) = 0 :=
        congrArg (abstractFixedField k Ω H).val h
      exact (Additive.toMul a.1 : Ωˣ).ne_zero h'
    exact Additive.ofMul (Units.mk0 y₀ hy₀)
  left_inv x := by
    apply Additive.ext
    apply Units.ext
    rfl
  right_inv a := by
    apply Subtype.ext
    apply Additive.ext
    apply Units.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl

omit [IsGalois k Ω] in
/-- The equivalence forgets to the ambient inclusion (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldUnits.lean:76`). -/
@[simp]
theorem abstractFixedFieldUnitsEquivGaloisFixed_coe
    (H : ClosedSubgroup (Ω ≃ₐ[k] Ω))
    (x : Additive (abstractFixedField k Ω H)ˣ) :
    ((abstractFixedFieldUnitsEquivGaloisFixed k Ω H x).1 :
        Additive Ωˣ) =
      intermediateFieldUnitsToGaloisAmbient k Ω
        (abstractFixedField k Ω H) x :=
  rfl

end

end Atlas.Knowledge
