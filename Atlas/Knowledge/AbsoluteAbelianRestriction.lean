import Mathlib
import Atlas.Knowledge.AbsoluteFiniteQuotientEquiv

/-!
# absolute abelian restriction

Every finite abelian subextension of the algebraic closure determines a
restriction homomorphism from the abelianized absolute Galois group
onto its Galois group, and the kernel is an open normal subgroup that
remembers the subextension: its pullback to the absolute Galois group
is the fixing subgroup, and the finite quotient field it cuts out is
the subextension itself — the finite-level inverse to the open-subgroup
dictionary of `Atlas.Knowledge.AbsoluteFiniteQuotientEquiv`, on the
target side of the absolute Artin map (#104).

## Main definitions

* `absoluteAbelianRestriction` — restriction from the abelianized
  absolute Galois group to the Galois group of a finite abelian
  subextension.
* `absoluteAbelianRestrictionKernel` — its kernel, an open normal
  subgroup of the abelianization.

## Main statements

* `absoluteAbelianRestriction_mk` — a quotient class restricts as any
  representative; proved.
* `absoluteAbelianRestriction_continuous` — the restriction is
  continuous; proved.
* `absoluteAbelianRestriction_surjective` — the restriction is onto;
  proved.
* `mem_absoluteAbelianRestrictionKernel_iff` — kernel membership is
  vanishing of the restriction; proved.
* `absoluteFiniteQuotientPreimage_restrictionKernel` — the kernel pulls
  back to the fixing subgroup; proved.
* `absoluteFiniteQuotientField_restrictionKernel` — the kernel cuts out
  the original subextension; proved.

## Implementation notes

The continuity fork of the arc, first:
`Atlas.Knowledge.IsLocalReciprocity` has no continuity field, so the
source's `→ₜ*` restriction is restated as the plain `→*` — the
`QuotientGroup.lift` its `q` names, over the same
`r`/`hcomm`/`hkerClosed`/`hclosure` scaffold — and the structure's
continuity field (its `:51`) is split off as the separate theorem
`absoluteAbelianRestriction_continuous`, the route of
`Atlas.Knowledge.absoluteAbelianizationMulEquiv_continuous`; the
kernel's openness (its `:87`) then rides the split-off theorem where
the source reads it off `continuous_toFun`. The ambient conversion of
the arc: the source works over its pinned `SeparableClosure K` with its
wrapper names `intrinsicAbsoluteGalois` and
`localAbsoluteAbelianProfinite`, the layer over `AlgebraicClosure K`
against Mathlib's `Field.absoluteGaloisGroup` and
`Field.absoluteGaloisGroupAbelianization`. `[CharZero K]` — the
hypothesis that makes the closure Galois, which the infinite Galois
correspondence needs — enters for the fixed-field identification
`absoluteFiniteQuotientField_restrictionKernel` alone, whose proof
closes with `InfiniteGalois.fixedField_fixingSubgroup`; every other
declaration is stated without it. The two source `@[simp]` lemmas keep
their source statements: both left sides — a `QuotientGroup.mk`
application and a bare membership — already sit at simp's normal form,
so no respelling was needed (the `mk'` hazard recorded on
`Atlas.Knowledge.AbsoluteLocalArtinMonoidHom` does not arise).
Everything else ports token-for-token up to two proof-shape changes: in
the definition's scaffold the closed-kernel step's rewrite is hoisted
into a `have` stating the kernel equation at the scaffold's `r`, since
`rw` does not unfold a tactic-`let` variable here, and the kernel's
`isNormal' := by infer_instance` is left to the field's identical
autoParam, the layer's convention. The file is the source's
`LocalClassFieldTheory/Infinite/FiniteAbelianQuotientKernels.lean:30`–`:129`,
the generic half: the local-field identification (its `:138`) is
`Atlas.Knowledge.absoluteLocalArtinMonoidHom_comap_restrictionKernel`,
and the closing cofinality theorem (its `:180`) stays unported with
that item.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

open scoped IsMulCommutative

variable (K : Type*) [Field K]

/-- **Restriction from the abelianized absolute Galois group to the
Galois group of a finite abelian subextension**: the descent of
`AlgEquiv.restrictNormalHom` through the topological abelianization
([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/FiniteAbelianQuotientKernels.lean:30`]
[Yamaguchi2026]). -/
noncomputable def absoluteAbelianRestriction
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    Field.absoluteGaloisGroupAbelianization K →* (E ≃ₐ[K] E) := by
  let r : Field.absoluteGaloisGroup K →* (E ≃ₐ[K] E) :=
    AlgEquiv.restrictNormalHom E
  have hcomm : commutator (Field.absoluteGaloisGroup K) ≤ r.ker :=
    Abelianization.commutator_subset_ker r
  have hker : r.ker = E.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker E
  have hkerClosed : IsClosed (r.ker : Set (Field.absoluteGaloisGroup K)) := by
    rw [hker]
    exact IntermediateField.fixingSubgroup_isClosed E
  have hclosure :
      (commutator (Field.absoluteGaloisGroup K)).topologicalClosure ≤ r.ker :=
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure_minimal
      hcomm hkerClosed
  exact QuotientGroup.lift
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure r
    (fun σ hσ ↦ MonoidHom.mem_ker.mp (hclosure hσ))

/-- The restriction sends a quotient class to the restriction of any
representative ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/FiniteAbelianQuotientKernels.lean:60`]
[Yamaguchi2026]). -/
@[simp]
theorem absoluteAbelianRestriction_mk
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (σ : Field.absoluteGaloisGroup K) :
    absoluteAbelianRestriction K E
        (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization K) =
      AlgEquiv.restrictNormalHom E σ :=
  rfl

/-- The restriction to a finite abelian subextension is continuous —
the continuity field of the source's bundled structure, split off as
its own theorem ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/FiniteAbelianQuotientKernels.lean:51`]
[Yamaguchi2026]). -/
theorem absoluteAbelianRestriction_continuous
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    Continuous (absoluteAbelianRestriction K E) := by
  apply (QuotientGroup.isQuotientMap_mk
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure).continuous_iff.2
  refine (InfiniteGalois.restrictNormalHom_continuous E).congr ?_
  intro σ
  exact (absoluteAbelianRestriction_mk K E σ).symm

/-- Restriction to a finite abelian subextension is onto after passing
to the abelianized absolute Galois group ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/FiniteAbelianQuotientKernels.lean:71`]
[Yamaguchi2026]). -/
theorem absoluteAbelianRestriction_surjective
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    Function.Surjective (absoluteAbelianRestriction K E) := by
  intro τ
  rcases AlgEquiv.restrictNormalHom_surjective
      (F := K) (K₁ := E) (E := AlgebraicClosure K) τ with ⟨σ, rfl⟩
  exact ⟨QuotientGroup.mk σ, absoluteAbelianRestriction_mk K E σ⟩

/-- The open normal kernel attached to a finite abelian subextension
([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/FiniteAbelianQuotientKernels.lean:81`]
[Yamaguchi2026]). -/
noncomputable def absoluteAbelianRestrictionKernel
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K) where
  toOpenSubgroup :=
    { toSubgroup := (absoluteAbelianRestriction K E).ker
      isOpen' := by
        change IsOpen (absoluteAbelianRestriction K E ⁻¹' {1})
        exact (isOpen_discrete {1}).preimage
          (absoluteAbelianRestriction_continuous K E) }

/-- Membership in the restriction kernel is vanishing of the
restriction ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/FiniteAbelianQuotientKernels.lean:95`]
[Yamaguchi2026]). -/
@[simp]
theorem mem_absoluteAbelianRestrictionKernel_iff
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E]
    (x : Field.absoluteGaloisGroupAbelianization K) :
    x ∈ absoluteAbelianRestrictionKernel K E ↔
      absoluteAbelianRestriction K E x = 1 :=
  Iff.rfl

/-- Pulling the restriction kernel back to the absolute Galois group
gives the fixing subgroup of the original finite subextension
([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/FiniteAbelianQuotientKernels.lean:105`]
[Yamaguchi2026]). -/
theorem absoluteFiniteQuotientPreimage_restrictionKernel
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    (absoluteFiniteQuotientPreimage K
      (absoluteAbelianRestrictionKernel K E)).toSubgroup =
        E.fixingSubgroup := by
  ext σ
  change absoluteAbelianRestriction K E
      (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization K) = 1 ↔
    σ ∈ E.fixingSubgroup
  rw [absoluteAbelianRestriction_mk,
    ← IntermediateField.restrictNormalHom_ker E]
  rfl

variable [CharZero K]

/-- **The finite field cut out by the restriction kernel is the
original finite abelian subextension** ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/FiniteAbelianQuotientKernels.lean:121`]
[Yamaguchi2026]). -/
theorem absoluteFiniteQuotientField_restrictionKernel
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    absoluteFiniteQuotientField K (absoluteAbelianRestrictionKernel K E) = E := by
  change IntermediateField.fixedField
      (absoluteFiniteQuotientPreimage K
        (absoluteAbelianRestrictionKernel K E)).toSubgroup = E
  rw [absoluteFiniteQuotientPreimage_restrictionKernel,
    InfiniteGalois.fixedField_fixingSubgroup]

end

end Atlas.Knowledge
