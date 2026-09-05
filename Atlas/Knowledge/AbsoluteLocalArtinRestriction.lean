import Mathlib
import Atlas.Knowledge.AbsoluteFiniteArtinMap
import Atlas.Knowledge.AbsoluteFiniteQuotientEquiv
import Atlas.Knowledge.AbsoluteLocalArtinMonoidHom

/-!
# absolute local Artin restriction

The absolute local Artin homomorphism read at a finite level: its
coordinate in an open finite quotient, carried through the dictionary
to the Galois group of the corresponding finite abelian field, is the
abelian local Artin homomorphism of that field — so every lift to the
absolute Galois group of the absolute Artin image of a unit restricts
to that field as the finite Artin image of the unit. The restriction
identity the Frobenius normalization of
`Atlas.Knowledge.IsLocalReciprocity` is assembled through (#104).

## Main statements

* `absoluteFiniteQuotientMulEquiv_absoluteLocalArtinMonoidHom` — the
  finite coordinate of the absolute Artin map, through the dictionary,
  is the abelian local Artin homomorphism of the quotient's field;
  proved.
* `restrictNormalHom_absoluteLocalArtinMonoidHom_lift` — every lift of
  the absolute Artin image of a unit restricts to the quotient's field
  as the finite Artin image; proved.

## Implementation notes

Both identities are stated at the dictionary's own field
`absoluteFiniteQuotientField K N`, not at an arbitrary finite abelian
`E` with `N` its restriction kernel: the identification of the two
fields,
`Atlas.Knowledge.absoluteFiniteQuotientField_restrictionKernel`, is a
propositional equality of intermediate fields, and carrying
`abelianLocalArtinMonoidHom` across it is the dependent transport the
#216 review recorded — its instance arguments are terms in the field,
so a rewrite's motive fails to type. Consumers transport propositions
along the equality instead (membership of a root of unity, triviality
of the inertia group), which is all the Frobenius normalization needs.
The first identity is the merged finite-projection identity read
through the inverse of the dictionary's isomorphism; the second
composes it with the dictionary's representative formula, which is
definitional. The source has no counterpart at the local infinite level
— its `absoluteLocalArtinMap` is consumed only inside
`LocalClassFieldTheory/Infinite/` — and states the projection identity
alone — `AbsoluteArtin.lean:215` at the separable model,
`ProfiniteLocalReciprocity.lean:375` at the standard model the layer
uses; the composition with `AlgEquiv.restrictNormalHom` appears on its
global side, in the statement of `restrict_globalArtinMonoidHom_apply`
(`GlobalClassFieldTheory/Reciprocity/GlobalArtin.lean:217`), for the
global Artin map.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- The finite coordinate of the absolute local Artin homomorphism in
an open finite quotient, read through the dictionary as an automorphism
of the quotient's field, is the abelian local Artin homomorphism of
that field ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:215`]
[Yamaguchi2026]). -/
theorem absoluteFiniteQuotientMulEquiv_absoluteLocalArtinMonoidHom
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) (u : Kˣ) :
    absoluteFiniteQuotientMulEquiv K N
        (absoluteLocalArtinMonoidHom K u :
          Field.absoluteGaloisGroupAbelianization K ⧸ N.toSubgroup) =
      abelianLocalArtinMonoidHom K (absoluteFiniteQuotientField K N) u := by
  rw [absoluteLocalArtinMonoidHom_finiteProjection]
  exact MulEquiv.apply_symm_apply _ _

/-- **Every lift of the absolute Artin image of a unit restricts to the
quotient's field as the finite Artin image of the unit**: for `σ` in
the absolute Galois group whose class in the abelianization is
`absoluteLocalArtinMonoidHom K u`, the restriction of `σ` to
`absoluteFiniteQuotientField K N` is
`abelianLocalArtinMonoidHom K _ u`. -/
theorem restrictNormalHom_absoluteLocalArtinMonoidHom_lift
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) (u : Kˣ)
    (σ : Field.absoluteGaloisGroup K)
    (hσ : (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization K) =
      absoluteLocalArtinMonoidHom K u) :
    AlgEquiv.restrictNormalHom (absoluteFiniteQuotientField K N) σ =
      abelianLocalArtinMonoidHom K (absoluteFiniteQuotientField K N) u := by
  rw [← absoluteFiniteQuotientMulEquiv_mk_mk K N σ, hσ]
  exact absoluteFiniteQuotientMulEquiv_absoluteLocalArtinMonoidHom K N u

end

end Atlas.Knowledge
