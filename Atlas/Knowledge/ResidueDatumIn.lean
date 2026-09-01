import Mathlib
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.ResidueAbsoluteDegreeIn

/-!
# residue degree datum

The arithmetic-Frobenius degree on a residue algebraic closure, packaged as the
reciprocity engine's opening datum (#104): the intrinsic degree map is a
continuous surjection `Gal(Ω/k) → ℤ̂`, and for every finite Galois subextension
of degree `n` the degree image of its fixing subgroup is exactly `n·ℤ̂` — so the
engine's abstract residue degree of the corresponding closed subgroup is the
ordinary field degree.

## Main definitions

* `closedFixingSubgroup` — a subextension's fixing subgroup as a closed
  subgroup.
* `residueDatumIn` — the degree datum on `Gal(Ω/k)`.

## Main statements

* `residueDatumIn_fieldImage_closedFixingSubgroup` — the degree image of the
  fixing subgroup of a degree-`n` subextension is `n·ℤ̂`; proved.
* `residueDatumIn_fieldImage_index_closedFixingSubgroup` — its index is the
  field degree; proved.

## Implementation notes

The fixing subgroup is closed by Mathlib's
`InfiniteGalois.fixingSubgroup_isClosed`; the `n·ℤ̂` identification reads the
kernel law of the finite Frobenius coordinates through the span–kernel identity
of the `ℤ̂` item, and the multiplicative reading is
`AddSubgroup.toSubgroup` of `Atlas.Knowledge.ProfiniteInteger.spanAddSubgroup`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

local instance (L : Type v) [Field L] [Finite L] [Algebra k L] :
    NeZero (Module.finrank k L) := ⟨Module.finrank_pos.ne'⟩

/-- **A subextension's fixing subgroup as a closed subgroup** — closedness is
Mathlib's `InfiniteGalois.fixingSubgroup_isClosed`
([Yamaguchi 2026, `RamificationTheory/GaloisValuation/ClosedFixingSubgroup.lean:15`]
[Yamaguchi2026]). -/
def closedFixingSubgroup (E : IntermediateField k Omega) :
    ClosedSubgroup (Omega ≃ₐ[k] Omega) where
  toSubgroup := E.fixingSubgroup
  isClosed' := InfiniteGalois.fixingSubgroup_isClosed E

/-- **The residue degree datum**: the intrinsic degree map with its
surjectivity ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean:29`]
[Yamaguchi2026]). -/
def residueDatumIn : DegreeData (Omega ≃ₐ[k] Omega) where
  degree := residueAbsoluteDegreeIn k Omega
  degree_surjective := (residueAbsoluteFrobeniusEquivIn k Omega).symm.surjective

omit [Fintype k] [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega] in
/- Membership in the fixing subgroup is trivial restriction. -/
private theorem mem_fixingSubgroup_iff_restrictNormalHom_eq_one
    (E : FiniteGaloisIntermediateField k Omega)
    (sigma : Omega ≃ₐ[k] Omega) :
    sigma ∈ E.toIntermediateField.fixingSubgroup ↔
      AlgEquiv.restrictNormalHom E sigma = 1 := by
  constructor
  · intro hsigma
    rw [IntermediateField.mem_fixingSubgroup_iff] at hsigma
    apply AlgEquiv.ext
    intro x
    apply Subtype.ext
    change ((AlgEquiv.restrictNormalHom E sigma x : E) : Omega) = (x : Omega)
    rw [AlgEquiv.restrictNormalHom_apply]
    exact hsigma x x.property
  · intro hsigma
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    let y : E := ⟨x, hx⟩
    have hy := congrArg (fun tau : E ≃ₐ[k] E => tau y) hsigma
    have hyval := congrArg Subtype.val hy
    rw [AlgEquiv.restrictNormalHom_apply] at hyval
    simpa [y] using hyval

/-- **The degree image of the fixing subgroup of a degree-`n` subextension is
`n·ℤ̂`** — the finite-coordinate compatibility read through the span–kernel
identity ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean:59`]
[Yamaguchi2026]). -/
theorem residueDatumIn_fieldImage_closedFixingSubgroup
    (E : FiniteGaloisIntermediateField k Omega) :
    (residueDatumIn k Omega).fieldImage
        (closedFixingSubgroup k Omega E) =
      AddSubgroup.toSubgroup
        (ProfiniteInteger.spanAddSubgroup (Module.finrank k E)) := by
  ext z
  letI : Finite E := Module.finite_of_finite k
  have hker : ∀ w : ProfiniteInteger,
      w ∈ ProfiniteInteger.spanAddSubgroup (Module.finrank k E) ↔
        ProfiniteInteger.reduction (Module.finrank k E) w = 0 := by
    intro w
    change w ∈ Ideal.span
        {((Module.finrank k E : ℕ) : ProfiniteInteger)} ↔ _
    rw [ProfiniteInteger.span_natCast_eq_ker_reduction, RingHom.mem_ker]
  constructor
  · rintro ⟨sigma, rfl⟩
    change (residueAbsoluteDegreeIn k Omega sigma.1).toAdd ∈
      ProfiniteInteger.spanAddSubgroup (Module.finrank k E)
    rw [hker]
    have hrestrict : AlgEquiv.restrictNormalHom E sigma.1 = 1 :=
      (mem_fixingSubgroup_iff_restrictNormalHom_eq_one
        k Omega E sigma.1).1 sigma.2
    have hcoordinate :=
      finiteResidueFrobeniusExponentEquiv_symm_restrict_in
        k Omega sigma.1 E
    rw [hrestrict, map_one] at hcoordinate
    exact (congrArg Multiplicative.toAdd hcoordinate).symm
  · intro hz
    change z.toAdd ∈
      ProfiniteInteger.spanAddSubgroup (Module.finrank k E) at hz
    rw [hker] at hz
    refine ⟨⟨residueAbsoluteFrobenius k Omega z, ?_⟩, ?_⟩
    · apply (mem_fixingSubgroup_iff_restrictNormalHom_eq_one
        k Omega E (residueAbsoluteFrobenius k Omega z)).2
      rw [restrictNormalHom_residueAbsoluteFrobenius]
      change finiteResidueFrobeniusFromZHat k E z = 1
      rw [finiteResidueFrobeniusFromZHat_apply]
      rw [show ProfiniteInteger.reduction (Module.finrank k E) z.toAdd = 0
        from hz]
      simp
    · exact (residueAbsoluteFrobeniusEquivIn k Omega).symm_apply_apply z

/-- **The degree image of the fixing subgroup has index the field degree** —
the finite-coordinate calculation behind the engine's residue degrees
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueDatum.lean:104`]
[Yamaguchi2026]). -/
theorem residueDatumIn_fieldImage_index_closedFixingSubgroup
    (E : FiniteGaloisIntermediateField k Omega) :
    ((residueDatumIn k Omega).fieldImage
        (closedFixingSubgroup k Omega E)).index = Module.finrank k E := by
  letI : Finite E := Module.finite_of_finite k
  rw [residueDatumIn_fieldImage_closedFixingSubgroup k Omega E,
    AddSubgroup.index_toSubgroup]
  exact ProfiniteInteger.index_span_natCast (Module.finrank k E)

end

end Atlas.Knowledge
