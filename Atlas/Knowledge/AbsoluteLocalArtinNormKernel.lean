import Mathlib
import Atlas.Knowledge.AbsoluteAbelianRestriction
import Atlas.Knowledge.AbsoluteFiniteArtinMap
import Atlas.Knowledge.AbsoluteFiniteQuotientEquiv
import Atlas.Knowledge.AbsoluteLocalArtinMonoidHom
import Atlas.Knowledge.NormQuotient

/-!
# absolute local Artin norm kernel

Over a mixed-characteristic local field, pulling the restriction kernel
of a finite abelian subextension back along the absolute local Artin
homomorphism gives exactly the norm subgroup of that subextension: the
finite-level kernel identification on the source side of the absolute
Artin map, through which the `normKernel` demand of
`Atlas.Knowledge.IsLocalReciprocity` is discharged (#104).

## Main statements

* `absoluteLocalArtinMonoidHom_comap_restrictionKernel` — the comap of
  a restriction kernel along the absolute Artin map is the norm
  subgroup; proved.

## Implementation notes

The continuity fork of the arc, first: the source states the
identification through its
`topologicalProfiniteCompletionPreimageIndex` device (its
`LocalClassFieldTheory/Infinite/ProfiniteCompletion.lean:296`) — the
open-finite-index packaging of the comap that feeds the
profinite-completion machinery of its
`ProfiniteCompletionCriteria.lean`, which stays unported with the
stripped continuity — so the theorem is restated as the bare
`Subgroup.comap` equality, and renamed from the source's
`separableAbsoluteLocalArtinMap_preimage_restrictionKernel`: its
"separable" reads its pinned `SeparableClosure K` ambient, wrong at the
layer's `AlgebraicClosure K`, and the arc names restatements after the
plain hom `Atlas.Knowledge.absoluteLocalArtinMonoidHom` — the
conventions recorded on that item. The source's proof route — the
finite projection plus the finite kernel identification, both
directions through `QuotientGroup.eq_one_iff` — uses no topology and is
kept, against the layer's projection identity
`Atlas.Knowledge.absoluteLocalArtinMonoidHom_finiteProjection`, whose
left side sits at simp's normal form where the source's applies
`QuotientGroup.mk'`; the source's `let`-abbreviated kernel is spelled
out, its fixed-field equation hoisted ahead of the extensionality. The
source file's closing cofinality theorem (its `:180`) — pullbacks of
restriction kernels are cofinal among the open finite-index normal
subgroups of `Kˣ` — stays unported: it consumes the finite local
existence theorem (`finiteAbelianNormSubgroupMap_surjective`, its
`LocalClassFieldTheory/Finite/Existence/Classification.lean`) and is
the arithmetic input for injectivity of the map from the profinite
completion, the deferred second claim whose ledger is #104. The
variable block is the local-field block of the consumed coordinates, at
a shared `Type u` since the #104 hoist — `[IsMixedCharLocalField K]` in
place of the source's `[IsNonarchimedeanLocalField K]`, the arc
convention — and `IsMixedCharLocalField` extends `CharZero`, which is
what lets the fixed-field identification of
`Atlas.Knowledge.AbsoluteAbelianRestriction` fire with no explicit
binder. The right side `localNormSubgroup K E` unfolds definitionally
to `MonoidHom.range (Units.map (Algebra.norm K))`, the spelling the
`normKernel` field of `Atlas.Knowledge.IsLocalReciprocity` speaks, so
the assembly needs no bridge lemma there.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- **Pulling a finite restriction kernel back along the absolute local
Artin map gives exactly the norm subgroup of that finite abelian
subextension** ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/FiniteAbelianQuotientKernels.lean:138`]
[Yamaguchi2026]). -/
theorem absoluteLocalArtinMonoidHom_comap_restrictionKernel
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    Subgroup.comap (absoluteLocalArtinMonoidHom K)
        (absoluteAbelianRestrictionKernel K E).toSubgroup =
      localNormSubgroup K E := by
  have hfield :
      absoluteFiniteQuotientField K (absoluteAbelianRestrictionKernel K E) = E :=
    absoluteFiniteQuotientField_restrictionKernel K E
  ext a
  change absoluteLocalArtinMonoidHom K a ∈ absoluteAbelianRestrictionKernel K E ↔
    a ∈ localNormSubgroup K E
  constructor
  · intro ha
    have hfinite :
        absoluteFiniteArtinMap K (absoluteAbelianRestrictionKernel K E) a = 1 := by
      rw [← absoluteLocalArtinMonoidHom_finiteProjection K
        (absoluteAbelianRestrictionKernel K E) a]
      exact (QuotientGroup.eq_one_iff
        (absoluteLocalArtinMonoidHom K a)).2 ha
    have hker :
        a ∈ (absoluteFiniteArtinMap K (absoluteAbelianRestrictionKernel K E)).ker :=
      MonoidHom.mem_ker.mpr hfinite
    rw [absoluteFiniteArtinMap_ker, hfield] at hker
    exact hker
  · intro ha
    have hker :
        a ∈ (absoluteFiniteArtinMap K (absoluteAbelianRestrictionKernel K E)).ker := by
      rw [absoluteFiniteArtinMap_ker, hfield]
      exact ha
    apply (QuotientGroup.eq_one_iff
      (absoluteLocalArtinMonoidHom K a)).mp
    calc
      (absoluteLocalArtinMonoidHom K a :
          Field.absoluteGaloisGroupAbelianization K ⧸
            (absoluteAbelianRestrictionKernel K E).toSubgroup) =
        absoluteFiniteArtinMap K (absoluteAbelianRestrictionKernel K E) a :=
          absoluteLocalArtinMonoidHom_finiteProjection K
            (absoluteAbelianRestrictionKernel K E) a
      _ = 1 := MonoidHom.mem_ker.mp hker

end

end Atlas.Knowledge
