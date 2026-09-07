import Mathlib
import Atlas.Knowledge.FiniteAbelianSubextension
import Atlas.Knowledge.FiniteAbelianSubfieldOrder
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.NormSubgroupSurjectivity
import Atlas.Knowledge.ResidueDatumIn

/-!
# norm subgroup of a compositum of finite abelian subfields

The compositum law of local class field theory on concrete subfields of the algebraic closure
of a mixed-characteristic local field: the norm subgroup of `E₁ ⊔ E₂` is the intersection of
the norm subgroups of `E₁` and `E₂`. This is the layer's abstract compositum law
`Atlas.Knowledge.localFiniteAbelianNormSubgroup_compositum` read through the packaging of
`Atlas.Knowledge.FiniteAbelianSubfieldOrder`, and it is what makes the norm subgroup of the
standard Lubin–Tate compositum computable — the input the inertia endpoint of the
ramification compatibility counts with.

## Main statements

* `toFiniteAbelianSubextension_sup` — the packaging of a compositum is the abstract
  compositum.
* `localNormSubgroup_sup` — `N (E₁ ⊔ E₂) = N (E₁) ⊓ N (E₂)`.

## Implementation notes

The abstract compositum's subgroup is the intersection of the two fixing subgroups, which
`IntermediateField.fixingSubgroup_sup` identifies with the fixing subgroup of the compositum,
so the two packagings agree by extensionality on the closed subgroup; the norm law then
transports along `Atlas.Knowledge.finiteAbelianNormSubgroup_toFiniteAbelianSubextension` at
the three fields. The compositum's commutativity enters as an instance argument, since Lean
does not find `IsAbelianGalois` on a `⊔` by search; `Atlas.Knowledge.isAbelianGalois_sup`
supplies it, and once it is declared as an instance for a named compositum both statements
apply there directly. Finiteness of a `⊔` is found by search, and the finiteness binder here
is discharged by it.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
-/

namespace Atlas.Knowledge

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- The packaging of a compositum of finite abelian subfields is the abstract compositum of
their packagings: both are represented by the intersection of the two fixing subgroups. -/
theorem toFiniteAbelianSubextension_sup (E₁ E₂ : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E₁] [IsAbelianGalois K E₁] [FiniteDimensional K E₂]
    [IsAbelianGalois K E₂]
    [FiniteDimensional K (E₁ ⊔ E₂ : IntermediateField K (AlgebraicClosure K))]
    [IsAbelianGalois K (E₁ ⊔ E₂ : IntermediateField K (AlgebraicClosure K))] :
    toFiniteAbelianSubextension K (E₁ ⊔ E₂) =
      (toFiniteAbelianSubextension K E₁).compositum (toFiniteAbelianSubextension K E₂) := by
  apply FiniteAbelianSubextension.ext
  apply ClosedSubgroup.ext
  have hs : (closedFixingSubgroup (E₁ ⊔ E₂ : IntermediateField K (AlgebraicClosure K))).toSubgroup =
      (closedFixingSubgroup E₁ ⊓ closedFixingSubgroup E₂ : ClosedSubgroup _).toSubgroup := by
    change (E₁ ⊔ E₂ : IntermediateField K (AlgebraicClosure K)).fixingSubgroup =
      E₁.fixingSubgroup ⊓ E₂.fixingSubgroup
    exact IntermediateField.fixingSubgroup_sup
  exact congrArg (fun H : Subgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) => H.carrier) hs

/-- **The norm subgroup of a compositum is the intersection of the norm subgroups**
([Milne 2020, Chap. I, §1, Cor. 1.2 (c), p.20][MilneCFT]). -/
theorem localNormSubgroup_sup (E₁ E₂ : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E₁] [IsAbelianGalois K E₁] [FiniteDimensional K E₂]
    [IsAbelianGalois K E₂]
    [FiniteDimensional K (E₁ ⊔ E₂ : IntermediateField K (AlgebraicClosure K))]
    [IsAbelianGalois K (E₁ ⊔ E₂ : IntermediateField K (AlgebraicClosure K))] :
    localNormSubgroup K (E₁ ⊔ E₂ : IntermediateField K (AlgebraicClosure K)) =
      localNormSubgroup K E₁ ⊓ localNormSubgroup K E₂ := by
  rw [← finiteAbelianNormSubgroup_toFiniteAbelianSubextension K (E₁ ⊔ E₂),
    toFiniteAbelianSubextension_sup, localFiniteAbelianNormSubgroup_compositum,
    finiteAbelianNormSubgroup_toFiniteAbelianSubextension,
    finiteAbelianNormSubgroup_toFiniteAbelianSubextension]

end Atlas.Knowledge
