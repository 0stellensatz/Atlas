import Mathlib
import Atlas.Knowledge.QuotientTotallyDisconnectedOfProfinite

/-!
# absolute abelianization equivalence

The abelianized absolute Galois group of a characteristic-zero field
is, as a topological group, the Galois group of its maximal abelian
subextension: the fixed field inside the algebraic closure of the
topological closure of the commutator subgroup is abelian Galois over
the base, and `Field.absoluteGaloisGroupAbelianization K` is carried
onto its Galois group by quotient-class-to-restriction — the
target-side dictionary through which the absolute Artin map's assembly
reads finite levels (#104).

## Main definitions

* `absoluteAbelianizationFixedField` — the fixed field of the closed
  commutator subgroup of the absolute Galois group.
* `absoluteAbelianizationMulEquiv` — the algebraic identification of
  the abelianization with the Galois group of that fixed field.
* `absoluteAbelianizationEquiv` — its topological upgrade.

## Main statements

* `absoluteAbelianizationMulEquiv_mk` — a quotient class goes to the
  restriction of any representative; proved.
* `absoluteAbelianizationMulEquiv_continuous` — the identification is
  continuous; proved.
* `absoluteGaloisGroupAbelianization_totallyDisconnectedSpace` — the
  abelianization is totally disconnected; proved.
* `absoluteGaloisGroupAbelianization_compactSpace` — the
  abelianization is compact; proved.
* `absoluteAbelianizationFixedField_isAbelianGalois` — the fixed field
  is abelian Galois over the base; proved.

## Implementation notes

The ambient conversion of the arc: the source works over its pinned
`SeparableClosure K` for an arbitrary field, the layer over
`AlgebraicClosure K` with `[CharZero K]` — the hypothesis that makes
the closure Galois, which the infinite Galois correspondence needs;
only the bare fixed-field definition is stated without it. The ported
file is a compatibility wrapper whose `local*` abbreviations delegate
to the field-generic
`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean`; the layer
states each construction once, against Mathlib's
`Field.absoluteGaloisGroup`, so the wrapper names have no separate
counterparts — each citation pairs the wrapper declaration line, whose
statement the declaration here matches one-for-one, with the underlying
declaration whose route the proof follows. Mathlib's
`Field.absoluteGaloisGroupAbelianization` is an abbrev of
`TopologicalAbelianization`, itself the literal quotient by
`(commutator (Field.absoluteGaloisGroup K)).topologicalClosure` — the
spelling `Atlas.Knowledge.IsLocalReciprocity` states its claims in — so
the source-versus-Mathlib spelling fork needs no bridge, and every
statement here elaborates against either form.

The closed subgroup the correspondence consumes is private and typed at
the automorphism-group spelling
`AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`: instance search does not
unfold the `Field.absoluteGaloisGroup` definition, so a
`ClosedSubgroup` at the derived spelling strands the `Normal` instance
argument of `InfiniteGalois.normalAutEquivQuotient`; term-mode
`inferInstanceAs` bridges carry the compactness and disconnectedness of
the Galois group across the same seam, and the public fixed field
states the commutator closure directly, keeping the definition free of
the private packaging. `absoluteAbelianizationMulEquiv_mk` is `rfl` —
Mathlib's `InfiniteGalois.normalAutEquivQuotient_apply` is definitional
— where the wrapper delegates a proved lemma. Total disconnectedness is
one application of the layer's
`Atlas.Knowledge.quotient_totallyDisconnected_of_profinite` where the
source transports along the compactness homeomorphism of the
equivalence, and abelianness is read backwards through the algebraic
equivalence — the route of the `IsAbelianGalois` instance of
`Atlas.Knowledge.MaximalAbelianExtension` — where the source transports
through the topological one. At a number field the fixed field here is
token-for-token `Atlas.Knowledge.maximalAbelianExtension`, so
`absoluteAbelianizationEquiv`, symmetrized and boxed in `Nonempty`, is
the content of that item's recorded claim
`Atlas.Knowledge.nonempty_continuousMulEquiv_absoluteGaloisGroupAbelianization`;
discharging the claim stays with its own item.

The compactness instance is the missing half of the source's
`ProfiniteGrp` bundling `localAbsoluteAbelianProfinite` (its
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:26`),
which `Atlas.Knowledge.AbsoluteFiniteQuotientEquiv` dropped unneeded
and `Atlas.Knowledge.AbsoluteFiniteArtinLimit` re-bundles for its
inverse limit: Mathlib's quotient-group instance supplies it once the
compactness of the absolute Galois group crosses the automorphism-group
seam on the same `inferInstanceAs` bridge as above, and it is recorded
here beside the total disconnectedness it completes. Hausdorffness, the
bundle's remaining leg, needs no instance of its own: search already
derives it from the recorded total disconnectedness — components are
singletons, so the group is `T1`, and a topological group is regular
unconditionally, whence `T3` and Hausdorff.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable (K : Type*) [Field K]

/-- The fixed field, inside the algebraic closure, of the topological
closure of the commutator subgroup of the absolute Galois group — in
characteristic zero the maximal abelian subextension (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteGaloisAbelianization.lean:29`,
`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean:37`). -/
def absoluteAbelianizationFixedField : IntermediateField K (AlgebraicClosure K) :=
  IntermediateField.fixedField
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure

/- The commutator closure packaged as a closed subgroup, at the
automorphism-group spelling the infinite Galois correspondence expects
(Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteGaloisAbelianization.lean:19`,
`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean:23`). -/
private def commutatorClosedSubgroup :
    ClosedSubgroup (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) where
  toSubgroup := (commutator (Field.absoluteGaloisGroup K)).topologicalClosure
  isClosed' := Subgroup.isClosed_topologicalClosure _

/- Normality of the packaged commutator closure, read off Mathlib's
instance on the raw subgroup (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteGaloisAbelianization.lean:24`,
`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean:30`). -/
private instance : (commutatorClosedSubgroup K).Normal :=
  Field.absoluteGaloisGroup.commutator_closure_isNormal K

variable [CharZero K]

/-- The maximal abelian subextension is Galois over the base field
(Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteGaloisAbelianization.lean:35`,
`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean:42`). -/
instance absoluteAbelianizationFixedField_isGalois :
    IsGalois K (absoluteAbelianizationFixedField K) := by
  apply (InfiniteGalois.normal_iff_isGalois (absoluteAbelianizationFixedField K)).1
  change (IntermediateField.fixedField
    (commutatorClosedSubgroup K).toSubgroup).fixingSubgroup.Normal
  rw [InfiniteGalois.fixingSubgroup_fixedField (commutatorClosedSubgroup K)]
  infer_instance

/-- The algebraic identification of the abelianized absolute Galois
group with the Galois group of the maximal abelian subextension
(Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteGaloisAbelianization.lean:40`,
`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean:55`). -/
def absoluteAbelianizationMulEquiv :
    Field.absoluteGaloisGroupAbelianization K ≃*
      (absoluteAbelianizationFixedField K ≃ₐ[K] absoluteAbelianizationFixedField K) :=
  InfiniteGalois.normalAutEquivQuotient (commutatorClosedSubgroup K)

/-- The identification sends a quotient class to the restriction of any
representative (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteGaloisAbelianization.lean:47`,
`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean:63`). -/
@[simp]
theorem absoluteAbelianizationMulEquiv_mk (σ : Field.absoluteGaloisGroup K) :
    absoluteAbelianizationMulEquiv K (QuotientGroup.mk σ) =
      AlgEquiv.restrictNormalHom (absoluteAbelianizationFixedField K) σ :=
  rfl

/-- The algebraic identification is continuous (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteGaloisAbelianization.lean:54`,
`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean:71`). -/
theorem absoluteAbelianizationMulEquiv_continuous :
    Continuous (absoluteAbelianizationMulEquiv K) := by
  apply (QuotientGroup.isQuotientMap_mk
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure).continuous_iff.2
  refine (InfiniteGalois.restrictNormalHom_continuous
    (absoluteAbelianizationFixedField K)).congr ?_
  intro σ
  exact (absoluteAbelianizationMulEquiv_mk K σ).symm

/-- The canonical topological identification of the abelianized
absolute Galois group with the Galois group of the maximal abelian
subextension: a continuous bijective homomorphism from a compact group
to a Hausdorff one is a homeomorphism (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteGaloisAbelianization.lean:59`,
`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean:83`). -/
def absoluteAbelianizationEquiv :
    Field.absoluteGaloisGroupAbelianization K ≃ₜ*
      (absoluteAbelianizationFixedField K ≃ₐ[K] absoluteAbelianizationFixedField K) := by
  haveI : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (CompactSpace (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  let h := Continuous.homeoOfEquivCompactToT2 (absoluteAbelianizationMulEquiv_continuous K)
  exact
    { absoluteAbelianizationMulEquiv K with
      continuous_toFun := h.continuous
      continuous_invFun := h.symm.continuous }

/-- The abelianized absolute Galois group is totally disconnected
(Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteGaloisAbelianization.lean:65`,
`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean:94`). -/
instance absoluteGaloisGroupAbelianization_totallyDisconnectedSpace :
    TotallyDisconnectedSpace (Field.absoluteGaloisGroupAbelianization K) := by
  haveI : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (CompactSpace (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  haveI : TotallyDisconnectedSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (TotallyDisconnectedSpace (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  exact quotient_totallyDisconnected_of_profinite _
    (Subgroup.isClosed_topologicalClosure _)

/-- The abelianized absolute Galois group is compact: the quotient of
the compact absolute Galois group under the continuous surjective
quotient map (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:26`). -/
instance absoluteGaloisGroupAbelianization_compactSpace :
    CompactSpace (Field.absoluteGaloisGroupAbelianization K) :=
  haveI : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (CompactSpace (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  inferInstance

/-- The maximal abelian subextension is abelian Galois: its Galois
group receives the commutative abelianization (Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteGaloisAbelianization.lean:71`,
`AlgebraicNumberTheory/Galois/AbsoluteAbelianization.lean:101`). -/
instance absoluteAbelianizationFixedField_isAbelianGalois :
    IsAbelianGalois K (absoluteAbelianizationFixedField K) where
  is_comm := ⟨fun σ τ => (absoluteAbelianizationMulEquiv K).symm.injective (by
    rw [map_mul, map_mul]
    exact mul_comm _ _)⟩

end

end Atlas.Knowledge
