import Mathlib
import Atlas.Knowledge.AbsoluteFiniteQuotientEquiv
import Atlas.Knowledge.IntermediateFieldRestrictNormalHom

/-!
# absolute finite quotient transition

Along an inclusion `N ≤ M` of open normal subgroups of the abelianized
absolute Galois group, the quotient by `N` maps canonically onto the
quotient by `M`, and under the finite quotient identifications of
`Atlas.Knowledge.AbsoluteFiniteQuotientEquiv` this transition is
exactly restriction of automorphisms from the larger fixed field to the
smaller — the compatibility that makes the finite Artin coordinates of
`Atlas.Knowledge.AbsoluteFiniteArtinMap` a compatible family (#104).

## Main definitions

* `absoluteFiniteQuotientTransition` — the canonical transition map
  between the finite quotients at `N ≤ M`.

## Main statements

* `absoluteFiniteQuotientPreimage_mono` — pullback of open normal
  subgroups to the absolute Galois group is monotone; proved.
* `absoluteFiniteQuotientField_antitone` — the corresponding fixed
  fields reverse the inclusion; proved.
* `absoluteFiniteQuotientTransition_mk` — the transition map fixes
  representatives; proved.
* `absoluteFiniteQuotientMulEquiv_transition` — under the finite
  quotient identifications, transition is restriction; proved.

## Implementation notes

The continuity fork of the arc, first:
`Atlas.Knowledge.IsLocalReciprocity` has no continuity field, so the
source's continuous vocabulary stays unported and its two `→ₜ*` forms
here are restated with plain monoid homomorphisms.
`absoluteFiniteQuotientTransition` is the bare `QuotientGroup.map`,
dropping the source's `letI` discrete-topology upgrade to a
`ContinuousMonoidHom` (its `:46`); the compatibility square composes
`Atlas.Knowledge.intermediateFieldRestrictNormalHom` with the algebraic
identification `Atlas.Knowledge.absoluteFiniteQuotientMulEquiv` where
the source (its `:73`) composes its unported
`intermediateFieldRestrictContinuous`
(`LocalClassFieldTheory/Finite/LocalReciprocity/NormResidueNaturality.lean:24`)
with the topological identification, and is renamed
`absoluteFiniteQuotientMulEquiv_transition` for its actual subject —
the fork's precedent is the continuity pair recorded on
`Atlas.Knowledge.AbelianLocalArtinMonoidHom` and
`Atlas.Knowledge.AbelianLocalArtinMonoidHomRestrict`. The ambient
conversion of the arc enters through the consumed dictionary, whose
`[CharZero K]` split this file matches: only the compatibility square,
which needs the correspondence's instances, assumes it. In the square's
proof the source's `change` and three rewrites collapse into one
`change`: the layer's identification and transition map are
definitional on representatives —
`absoluteFiniteQuotientMulEquiv_mk_mk`, recorded on the dictionary for
this file, and `absoluteFiniteQuotientTransition_mk` are `rfl` — so the
fully rewritten form is already the goal; and the closing calc becomes
a term-mode `Eq.trans` chain, since its written intermediate statements
would apply `σ` to ambient elements, which the automorphism-group seam
recorded on the dictionary — instance search does not unfold
`Field.absoluteGaloisGroup`, so no `CoeFun` fires on `σ`'s stated type
— refuses, while inside the bridging lemmas' own statements the
applications already live at the unfolded spelling. The source's
placeholder docstring on the `_mk` lemma is replaced by a statement of
content. Everything else ports token-for-token; the file is the
source's
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotientTransitions.lean`
whole.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable (K : Type*) [Field K]

/-- Pullback of open normal subgroups of the abelianization to the
absolute Galois group is monotone (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotientTransitions.lean:21`). -/
theorem absoluteFiniteQuotientPreimage_mono
    {N M : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)}
    (hNM : N ≤ M) :
    absoluteFiniteQuotientPreimage K N ≤
      absoluteFiniteQuotientPreimage K M := by
  intro σ hσ
  exact hNM hσ

/-- Inclusion of open normal subgroups reverses the corresponding
fixed fields (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotientTransitions.lean:31`). -/
theorem absoluteFiniteQuotientField_antitone
    {N M : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)}
    (hNM : N ≤ M) :
    absoluteFiniteQuotientField K M ≤
      absoluteFiniteQuotientField K N := by
  intro x hx
  change x ∈ IntermediateField.fixedField
    (absoluteFiniteQuotientPreimage K M).toSubgroup at hx
  change x ∈ IntermediateField.fixedField
    (absoluteFiniteQuotientPreimage K N).toSubgroup
  rw [IntermediateField.mem_fixedField_iff] at hx ⊢
  intro σ hσ
  exact hx σ (absoluteFiniteQuotientPreimage_mono K hNM hσ)

/-- The canonical transition map between two finite quotients along an
inclusion of open normal subgroups (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotientTransitions.lean:46`). -/
noncomputable def absoluteFiniteQuotientTransition
    {N M : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)}
    (hNM : N ≤ M) :
    Field.absoluteGaloisGroupAbelianization K ⧸ N.toSubgroup →*
      Field.absoluteGaloisGroupAbelianization K ⧸ M.toSubgroup :=
  QuotientGroup.map N.toSubgroup M.toSubgroup (MonoidHom.id _)
    (fun _ hx => hNM hx)

/-- The transition map fixes representatives: the class of `x` modulo
`N` goes to the class of `x` modulo `M` (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotientTransitions.lean:64`). -/
@[simp]
theorem absoluteFiniteQuotientTransition_mk
    {N M : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)}
    (hNM : N ≤ M) (x : Field.absoluteGaloisGroupAbelianization K) :
    absoluteFiniteQuotientTransition K hNM (QuotientGroup.mk x) =
      QuotientGroup.mk x := by
  rfl

variable [CharZero K]

/-- **Under the finite quotient identifications, quotient transition is
exactly restriction of automorphisms to the smaller fixed field**
(Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotientTransitions.lean:73`). -/
theorem absoluteFiniteQuotientMulEquiv_transition
    {N M : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)}
    (hNM : N ≤ M) :
    (intermediateFieldRestrictNormalHom
        (absoluteFiniteQuotientField K M) (absoluteFiniteQuotientField K N)
        (absoluteFiniteQuotientField_antitone K hNM)).comp
      (absoluteFiniteQuotientMulEquiv K N).toMonoidHom =
      (absoluteFiniteQuotientMulEquiv K M).toMonoidHom.comp
        (absoluteFiniteQuotientTransition K hNM) := by
  apply MonoidHom.ext
  intro x
  obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective N.toSubgroup x
  obtain ⟨σ, rfl⟩ := QuotientGroup.mk'_surjective
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure p
  change intermediateFieldRestrictNormalHom
      (absoluteFiniteQuotientField K M) (absoluteFiniteQuotientField K N)
      (absoluteFiniteQuotientField_antitone K hNM)
      (AlgEquiv.restrictNormalHom (absoluteFiniteQuotientField K N) σ) =
    AlgEquiv.restrictNormalHom (absoluteFiniteQuotientField K M) σ
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  exact (intermediateFieldRestrictNormalHom_apply_val
      (absoluteFiniteQuotientField K M) (absoluteFiniteQuotientField K N)
      (absoluteFiniteQuotientField_antitone K hNM)
      (AlgEquiv.restrictNormalHom (absoluteFiniteQuotientField K N) σ)
      y).trans
    ((AlgEquiv.restrictNormal_commutes σ (absoluteFiniteQuotientField K N)
        (IntermediateField.inclusion
          (absoluteFiniteQuotientField_antitone K hNM) y)).trans
      (AlgEquiv.restrictNormal_commutes σ
        (absoluteFiniteQuotientField K M) y).symm)

end

end Atlas.Knowledge
