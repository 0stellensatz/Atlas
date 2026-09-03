import Mathlib
import Atlas.Knowledge.AbsoluteFiniteArtinLimit
import Atlas.Knowledge.AbsoluteFiniteArtinLimitMap
import Atlas.Knowledge.AbsoluteFiniteArtinMap

/-!
# absolute local Artin homomorphism

The absolute local Artin map of a mixed-characteristic local field: the
compatible cone of finite Artin coordinates, read back through the
limit identification into the abelianized absolute Galois group itself.
Its projection to every open finite quotient is the finite Artin
coordinate there, and its range is dense — the candidate homomorphism
realizing the dense-range demand of
`Atlas.Knowledge.IsLocalReciprocity` (#104).

## Main definitions

* `absoluteLocalArtinMonoidHom` — the absolute local Artin homomorphism
  `Kˣ →* Field.absoluteGaloisGroupAbelianization K`.

## Main statements

* `absoluteLocalArtinMonoidHom_finiteProjection` — its projection to an
  open finite quotient is the finite Artin coordinate; proved.
* `absoluteLocalArtinMonoidHom_denseRange` — it has dense range;
  proved.

## Implementation notes

The continuity fork of the arc, first:
`Atlas.Knowledge.IsLocalReciprocity` has no continuity field, so the
source's `→ₜ*` composite is restated as the plain `→*` — the inverse of
the limit identification enters as its underlying `MulEquiv`'s monoid
homomorphism, where the source (its `:206`) composes continuous
homomorphisms. The dense range stays, and so does the source's route to
it: transporting the cone's dense range backwards needs the inverse
identification surjective and continuous, and the kept `≃ₜ*` of
`Atlas.Knowledge.AbsoluteFiniteArtinLimit` supplies both even though
the composite is stated plain. The map is renamed from the source's
`separableAbsoluteLocalArtinMap`: its "separable" reads its pinned
`SeparableClosure K` ambient, wrong at the layer's `AlgebraicClosure K`
(the ambient conversion of the arc), and the arc names the plain-hom
restatements `MonoidHom` — the convention of
`Atlas.Knowledge.abelianLocalArtinMonoidHom`. In the projection
identity the source's closing `simpa` unfolding the definition is
replaced by a definitional `exact`: after the source's `change`, the
hypothesis is the goal up to unfolding the definition and the coercion
chain — the syntactic route in fact strands the two sides at different
coercion spellings under simp's current normal form — and the
comparison never enters `abelianLocalArtinMonoidHom`, so the
recursion-limit hazard recorded on
`Atlas.Knowledge.AbsoluteFiniteArtinMap` does not bite. The variable
block is the local-field Type-pinned block of the consumed coordinates,
that block's recorded universe seam. Everything else ports
token-for-token; the file is the source's
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:206`–`:235`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- **The absolute local Artin homomorphism** into the abelianized
absolute Galois group: the compatible cone of finite Artin coordinates
read back through the limit identification ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:206`]
[Yamaguchi2026]). -/
noncomputable def absoluteLocalArtinMonoidHom :
    Kˣ →* Field.absoluteGaloisGroupAbelianization K :=
  ((absoluteGaloisAbelianizationLimitEquiv K).symm.toMulEquiv.toMonoidHom).comp
    (absoluteFiniteArtinLimitMap K)

/-- Projection of the absolute local Artin map to an open finite
quotient is the corresponding finite Artin coordinate ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:215`]
[Yamaguchi2026]). -/
@[simp]
theorem absoluteLocalArtinMonoidHom_finiteProjection
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) (a : Kˣ) :
    QuotientGroup.mk' N.toSubgroup
        (absoluteLocalArtinMonoidHom K a) =
      absoluteFiniteArtinMap K N a := by
  let e := absoluteGaloisAbelianizationLimitEquiv K
  let y := absoluteFiniteArtinLimitMap K a
  have h := congrArg (fun z => z.1 N) (e.apply_symm_apply y)
  change
    QuotientGroup.mk' N.toSubgroup (e.symm y) =
      absoluteFiniteArtinMap K N a at h
  exact h

/-- **The absolute local Artin map has dense range** ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:229`]
[Yamaguchi2026]). -/
theorem absoluteLocalArtinMonoidHom_denseRange :
    DenseRange (absoluteLocalArtinMonoidHom K) := by
  let e := absoluteGaloisAbelianizationLimitEquiv K
  change DenseRange
    (fun a => e.symm (absoluteFiniteArtinLimitMap K a))
  exact e.symm.surjective.denseRange.comp
    (absoluteFiniteArtinLimitMap_denseRange K) e.symm.continuous

end

end Atlas.Knowledge
