import Mathlib
import Atlas.Knowledge.AbelianLocalArtinMonoidHom
import Atlas.Knowledge.AbelianLocalArtinMonoidHomRestrict
import Atlas.Knowledge.AbsoluteFiniteQuotientEquiv
import Atlas.Knowledge.AbsoluteFiniteQuotientTransition
import Atlas.Knowledge.NormQuotient

/-!
# absolute finite Artin map

The finite coordinates of the absolute local Artin map: at every open
normal subgroup `N` of the abelianized absolute Galois group of a
mixed-characteristic local field, the abelian local Artin homomorphism
of the finite abelian fixed field, read backwards through the finite
quotient identification, is a homomorphism from `Kˣ` onto the quotient
by `N` — surjective, with kernel the norm subgroup of that fixed
field, and commuting with quotient transition, so the coordinates form
a compatible family over the transition system (#104).

## Main definitions

* `absoluteFiniteArtinMap` — the finite Artin coordinate at an open
  normal subgroup `N`.

## Main statements

* `absoluteFiniteArtinMap_surjective` — every finite coordinate is
  onto; proved.
* `absoluteFiniteArtinMap_ker` — its kernel is the norm subgroup of
  the corresponding finite abelian fixed field; proved.
* `absoluteFiniteArtinMap_transition` — the coordinates commute with
  quotient transition; proved.

## Implementation notes

The continuity fork of the arc, first:
`Atlas.Knowledge.IsLocalReciprocity` has no continuity field, so the
source's continuous vocabulary stays unported and each of the four
`→ₜ*`-phrased declarations here is restated with plain monoid
homomorphisms. The coordinate composes
`Atlas.Knowledge.abelianLocalArtinMonoidHom` with the algebraic
identification `Atlas.Knowledge.absoluteFiniteQuotientMulEquiv`
inverted, where the source (its `:25`) composes its unported
continuous `abelianLocalArtinMap`
(`LocalClassFieldTheory/Finite/LocalReciprocity/NormResidue.lean:69`)
with the topological identification inverted; surjectivity and the
kernel ride the layer's `abelianLocalArtinMonoidHom_surjective` and
`abelianLocalArtinMonoidHom_ker` in place of the continuous forms
(`NormResidue.lean:89` and `:96`); and the transition square rides
`Atlas.Knowledge.abelianLocalArtinMonoidHom_restrict` and
`Atlas.Knowledge.absoluteFiniteQuotientMulEquiv_transition` in place
of the continuous `abelianLocalArtinMap_restrict`
(`LocalClassFieldTheory/Finite/LocalReciprocity/NormResidueNaturality.lean:47`)
and the source's topological square — the fork as recorded on
`Atlas.Knowledge.AbelianLocalArtinMonoidHom` and
`Atlas.Knowledge.AbsoluteFiniteQuotientTransition`. The variable block
is the local-field block of the consumed Artin homomorphism —
`[IsMixedCharLocalField K]` in place of the source's
`[IsNonarchimedeanLocalField K]`, the arc convention — and `K` stays
pinned to `Type`, that block's recorded universe seam;
`IsMixedCharLocalField` extends `CharZero`, which is what lets the
dictionary's finiteness and abelianness instances fire with no
explicit binder. In the transition proof the source's `change` is a
`simp only` unfolding of the coordinate, and the two
`DFunLike.congr_fun` bridges enter through `have` plus the same
`simp only` normalization: a definitional comparison through
`abelianLocalArtinMonoidHom` unfolds the whole reciprocity transport
past the recursion limit, so the proof keeps every comparison
syntactic. The file is the source's
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:25`–`:107`, the
finite-coordinate half only: the limit half (its `:109` on — the
inverse-limit target, the assembled absolute map, and its dense range)
is deliberately left to the next item. Everything else ports
token-for-token up to the plain-hom respelling.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- **The finite Artin coordinate at an open normal subgroup of the
abelianized absolute Galois group** ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:25`]
[Yamaguchi2026]). -/
noncomputable def absoluteFiniteArtinMap
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    Kˣ →* Field.absoluteGaloisGroupAbelianization K ⧸ N.toSubgroup :=
  (absoluteFiniteQuotientMulEquiv K N).symm.toMonoidHom.comp
    (abelianLocalArtinMonoidHom K (absoluteFiniteQuotientField K N))

/-- Every finite coordinate of the absolute Artin map is onto
([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:33`]
[Yamaguchi2026]). -/
theorem absoluteFiniteArtinMap_surjective
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    Function.Surjective (absoluteFiniteArtinMap K N) :=
  (absoluteFiniteQuotientMulEquiv K N).symm.surjective.comp
    (abelianLocalArtinMonoidHom_surjective K
      (absoluteFiniteQuotientField K N))

/-- **The kernel of a finite absolute Artin coordinate is the ordinary
norm subgroup of its corresponding finite abelian fixed field**
([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:42`]
[Yamaguchi2026]). -/
theorem absoluteFiniteArtinMap_ker
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) :
    (absoluteFiniteArtinMap K N).ker =
      localNormSubgroup K (absoluteFiniteQuotientField K N) := by
  rw [← abelianLocalArtinMonoidHom_ker K (absoluteFiniteQuotientField K N)]
  ext a
  simp only [MonoidHom.mem_ker, absoluteFiniteArtinMap]
  constructor
  · intro ha
    apply (absoluteFiniteQuotientMulEquiv K N).symm.injective
    simpa using ha
  · intro ha
    simpa using congrArg (absoluteFiniteQuotientMulEquiv K N).symm ha

/-- Finite absolute Artin coordinates commute with quotient transition
([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:57`]
[Yamaguchi2026]). -/
theorem absoluteFiniteArtinMap_transition
    {N M : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)}
    (hNM : N ≤ M) :
    (absoluteFiniteQuotientTransition K hNM).comp
        (absoluteFiniteArtinMap K N) =
      absoluteFiniteArtinMap K M := by
  apply MonoidHom.ext
  intro a
  apply (absoluteFiniteQuotientMulEquiv K M).injective
  simp only [MonoidHom.coe_comp, Function.comp_apply, absoluteFiniteArtinMap,
    MulEquiv.coe_toMonoidHom]
  calc
    _ = intermediateFieldRestrictNormalHom
          (absoluteFiniteQuotientField K M)
          (absoluteFiniteQuotientField K N)
          (absoluteFiniteQuotientField_antitone K hNM)
          (absoluteFiniteQuotientMulEquiv K N
            ((absoluteFiniteQuotientMulEquiv K N).symm
              (abelianLocalArtinMonoidHom K
                (absoluteFiniteQuotientField K N) a))) := by
        have h := DFunLike.congr_fun
          (absoluteFiniteQuotientMulEquiv_transition K hNM)
          ((absoluteFiniteQuotientMulEquiv K N).symm
            (abelianLocalArtinMonoidHom K
              (absoluteFiniteQuotientField K N) a))
        simp only [MonoidHom.coe_comp, Function.comp_apply,
          MulEquiv.coe_toMonoidHom] at h
        exact h.symm
    _ = intermediateFieldRestrictNormalHom
          (absoluteFiniteQuotientField K M)
          (absoluteFiniteQuotientField K N)
          (absoluteFiniteQuotientField_antitone K hNM)
          (abelianLocalArtinMonoidHom K
            (absoluteFiniteQuotientField K N) a) := by
        rw [(absoluteFiniteQuotientMulEquiv K N).apply_symm_apply]
    _ = abelianLocalArtinMonoidHom K (absoluteFiniteQuotientField K M) a := by
        have h := DFunLike.congr_fun
          (abelianLocalArtinMonoidHom_restrict K
            (absoluteFiniteQuotientField K M)
            (absoluteFiniteQuotientField K N)
            (absoluteFiniteQuotientField_antitone K hNM)) a
        simp only [MonoidHom.coe_comp, Function.comp_apply] at h
        exact h
    _ = _ := by
        rw [(absoluteFiniteQuotientMulEquiv K M).apply_symm_apply]

end

end Atlas.Knowledge
