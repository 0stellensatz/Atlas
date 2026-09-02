import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.GaloisExtensionQuotient
import Atlas.Knowledge.IntermediateFieldUnitsFixedSubgroup
import Atlas.Knowledge.ResidueDatumIn
import Atlas.Knowledge.SeparableEmbeddingIntoSeparableClosure

/-!
# finite Galois realization

Every finite Galois extension `L/K` is embedded into the chosen
separable closure of `K`, and its image supplies the concrete closed
subgroup used by the abstract class-field theory: the resulting
abstract fixed coefficient group is `Lˣ`, and the resulting abstract
extension quotient is the actual `L ≃ₐ[K] L`. No perfectness
hypothesis is imposed; this includes equal-characteristic local fields
such as finite extensions of `𝔽_q((t))` (#104).

## Main definitions

* `finiteGaloisClosedFixingSubgroup` — the concrete closed subgroup
  attached to `L/K`.
* `finiteGaloisUnitsEquivAbstractFixed` — the fixed coefficient group
  is canonically `Lˣ`.
* `finiteGaloisAbstractQuotientEquivGaloisGroup` — the abstract
  extension quotient is canonically the Galois group.

## Main statements

* `finiteGaloisExtensionSubgroup_index_eq_finrank` — the chosen
  realization's subgroup index is the field degree; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
and with it the source's `fixingSubgroupLeBase` third arguments to
`extensionSubgroup` vanish from every statement of this file. The
Galois groups are spelled `≃ₐ[·]` — the layer carries no `Gal(E/F)`
notation — and `closedFixingSubgroup` takes only the intermediate
field. The chosen embedding is the layer's flat
`separableEmbeddingIntoSeparableClosure`, without the source's
`AlgebraicNumberTheory` prefix. Everything else ports token-for-token;
the file is the source's
`LocalReciprocity/FiniteGaloisRealization.lean`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- The embedded copy of `L` determined by an explicit embedding into
the fixed separable closure; keeping the embedding visible is what
makes the canonicity argument in the finite local reciprocity theorem
meaningful ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:32`]
[Yamaguchi2026]). -/
def finiteGaloisFieldRangeOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    IntermediateField K (SeparableClosure K) :=
  AlgHom.fieldRange i

/-- An explicit embedding identifies `L` with its field range
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:38`]
[Yamaguchi2026]). -/
def finiteGaloisFieldRangeEquivOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    L ≃ₐ[K] finiteGaloisFieldRangeOfEmbedding K L i :=
  AlgEquiv.ofInjectiveField i

/-- The image of an embedded finite Galois extension is again Galois
over the base field ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:44`]
[Yamaguchi2026]). -/
noncomputable instance finiteGaloisFieldRangeOfEmbedding_isGalois
    (i : L →ₐ[K] SeparableClosure K) :
    IsGalois K (finiteGaloisFieldRangeOfEmbedding K L i) :=
  IsGalois.of_algEquiv (finiteGaloisFieldRangeEquivOfEmbedding K L i)

/-- The image of an embedded finite extension is finite-dimensional
over the base field ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:50`]
[Yamaguchi2026]). -/
noncomputable instance finiteGaloisFieldRangeOfEmbedding_finiteDimensional
    (i : L →ₐ[K] SeparableClosure K) :
    FiniteDimensional K (finiteGaloisFieldRangeOfEmbedding K L i) :=
  (finiteGaloisFieldRangeEquivOfEmbedding K L i).toLinearEquiv.finiteDimensional

/-- The closed fixing subgroup attached to an explicit realization of
`L/K` in the separable closure ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:57`]
[Yamaguchi2026]). -/
def finiteGaloisClosedFixingSubgroupOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    ClosedSubgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K) :=
  closedFixingSubgroup (finiteGaloisFieldRangeOfEmbedding K L i)

/-- The fixing subgroup of an embedded finite Galois extension is
normal in the absolute subgroup ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:64`]
[Yamaguchi2026]). -/
noncomputable instance finiteGaloisExtensionSubgroupOfEmbedding_normal
    (i : L →ₐ[K] SeparableClosure K) :
    ((finiteGaloisClosedFixingSubgroupOfEmbedding K L i).toSubgroup.subgroupOf
      (closedFixingSubgroup
        (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup).Normal := by
  change
    ((closedFixingSubgroup
        (finiteGaloisFieldRangeOfEmbedding K L i)).toSubgroup.subgroupOf
      (closedFixingSubgroup
        (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup).Normal
  infer_instance

/-- The fixed coefficient group attached to an explicit realization is
canonically the actual unit group `Lˣ` ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:84`]
[Yamaguchi2026]). -/
def finiteGaloisUnitsEquivAbstractFixedOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    Additive Lˣ ≃+
      ambientFixedAddSubgroup
        (galoisAmbientUnitsRep K (SeparableClosure K))
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L i) :=
  embeddedFieldUnitsEquivGaloisFixed K (SeparableClosure K) L i

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The fixed-module equivalence sends a field unit to the unit
induced by the chosen embedding ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:95`]
[Yamaguchi2026]). -/
@[simp]
theorem finiteGaloisUnitsEquivAbstractFixedOfEmbedding_coe
    (i : L →ₐ[K] SeparableClosure K) (x : Lˣ) :
    (finiteGaloisUnitsEquivAbstractFixedOfEmbedding K L i
      (Additive.ofMul x)).1 =
      Additive.ofMul (Units.map i.toRingHom.toMonoidHom x) :=
  rfl

/-- The abstract class-formation extension quotient attached to an
explicit realization of `L/K` is the actual relative Galois group
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:104`]
[Yamaguchi2026]). -/
def finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
    (i : L →ₐ[K] SeparableClosure K) :
    ((closedFixingSubgroup
        (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
      (finiteGaloisClosedFixingSubgroupOfEmbedding K L i).toSubgroup.subgroupOf
        (closedFixingSubgroup
          (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup) ≃*
      (L ≃ₐ[K] L) :=
  (baseFixingExtensionQuotientEquivGaloisGroup K (SeparableClosure K)
    (finiteGaloisFieldRangeOfEmbedding K L i)).trans
      (AlgEquiv.autCongr
        (finiteGaloisFieldRangeEquivOfEmbedding K L i)).symm

/-- The subgroup attached to an explicit finite Galois realization has
index equal to the ordinary field degree ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:122`]
[Yamaguchi2026]). -/
theorem finiteGaloisExtensionSubgroupOfEmbedding_index_eq_finrank
    (i : L →ₐ[K] SeparableClosure K) :
    ((finiteGaloisClosedFixingSubgroupOfEmbedding K L i).toSubgroup.subgroupOf
      (closedFixingSubgroup
        (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup).index =
      Module.finrank K L := by
  letI : Finite
      ((closedFixingSubgroup
          (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
        (finiteGaloisClosedFixingSubgroupOfEmbedding K L
            i).toSubgroup.subgroupOf
          (closedFixingSubgroup
            (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup) :=
    Finite.of_equiv (L ≃ₐ[K] L)
      (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
        K L i).symm.toEquiv
  calc
    _ = Nat.card
        ((closedFixingSubgroup
            (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
          (finiteGaloisClosedFixingSubgroupOfEmbedding K L
              i).toSubgroup.subgroupOf
            (closedFixingSubgroup
              (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup) :=
      Subgroup.index_eq_card _
    _ = Nat.card (L ≃ₐ[K] L) :=
      Nat.card_congr
        (finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding
          K L i).toEquiv
    _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L

/-- The embedded copy of `L` inside the fixed separable closure
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:161`]
[Yamaguchi2026]). -/
def finiteGaloisFieldRange : IntermediateField K (SeparableClosure K) :=
  finiteGaloisFieldRangeOfEmbedding K L
    (separableEmbeddingIntoSeparableClosure K L)

/-- The chosen embedding identifies `L` with its actual field range
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:166`]
[Yamaguchi2026]). -/
def finiteGaloisFieldRangeEquiv :
    L ≃ₐ[K] finiteGaloisFieldRange K L :=
  finiteGaloisFieldRangeEquivOfEmbedding K L
    (separableEmbeddingIntoSeparableClosure K L)

/-- The canonical realization of a finite Galois extension is Galois
over the base field ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:172`]
[Yamaguchi2026]). -/
instance finiteGaloisFieldRange_isGalois :
    IsGalois K (finiteGaloisFieldRange K L) :=
  finiteGaloisFieldRangeOfEmbedding_isGalois K L
    (separableEmbeddingIntoSeparableClosure K L)

/-- The canonical realization of a finite extension is
finite-dimensional over the base field ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:178`]
[Yamaguchi2026]). -/
instance finiteGaloisFieldRange_finiteDimensional :
    FiniteDimensional K (finiteGaloisFieldRange K L) :=
  finiteGaloisFieldRangeOfEmbedding_finiteDimensional K L
    (separableEmbeddingIntoSeparableClosure K L)

/-- **The concrete closed subgroup of the absolute separable Galois
group attached to `L/K`** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:185`]
[Yamaguchi2026]). -/
def finiteGaloisClosedFixingSubgroup :
    ClosedSubgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K) :=
  finiteGaloisClosedFixingSubgroupOfEmbedding K L
    (separableEmbeddingIntoSeparableClosure K L)

/-- The fixing subgroup of the canonical finite Galois realization is
normal ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:191`]
[Yamaguchi2026]). -/
instance finiteGaloisExtensionSubgroup_normal :
    ((finiteGaloisClosedFixingSubgroup K L).toSubgroup.subgroupOf
      (closedFixingSubgroup
        (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup).Normal := by
  change
    ((closedFixingSubgroup (finiteGaloisFieldRange K L)).toSubgroup.subgroupOf
      (closedFixingSubgroup
        (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup).Normal
  infer_instance

/-- **The actual coefficient group fixed by the concrete subgroup
attached to `L/K` is canonically `Lˣ`** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:210`]
[Yamaguchi2026]). -/
def finiteGaloisUnitsEquivAbstractFixed :
    Additive Lˣ ≃+
      ambientFixedAddSubgroup
        (galoisAmbientUnitsRep K (SeparableClosure K))
        (finiteGaloisClosedFixingSubgroup K L) :=
  finiteGaloisUnitsEquivAbstractFixedOfEmbedding K L
    (separableEmbeddingIntoSeparableClosure K L)

omit [FiniteDimensional K L] in
/-- The canonical fixed-module equivalence sends a unit through the
chosen embedding ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:221`]
[Yamaguchi2026]). -/
@[simp]
theorem finiteGaloisUnitsEquivAbstractFixed_coe (x : Lˣ) :
    (finiteGaloisUnitsEquivAbstractFixed K L (Additive.ofMul x)).1 =
      Additive.ofMul
        (Units.map
          (separableEmbeddingIntoSeparableClosure
            K L).toRingHom.toMonoidHom x) :=
  rfl

/-- **For the concrete realization of `L/K`, the exact quotient used
by the abstract class-formation framework is canonically the actual
Galois group** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:231`]
[Yamaguchi2026]). -/
def finiteGaloisAbstractQuotientEquivGaloisGroup :
    ((closedFixingSubgroup
        (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup ⧸
      (finiteGaloisClosedFixingSubgroup K L).toSubgroup.subgroupOf
        (closedFixingSubgroup
          (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup) ≃*
      (L ≃ₐ[K] L) :=
  finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L
    (separableEmbeddingIntoSeparableClosure K L)

/-- The chosen realization has subgroup index equal to `[L : K]`
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteGaloisRealization.lean:245`]
[Yamaguchi2026]). -/
theorem finiteGaloisExtensionSubgroup_index_eq_finrank :
    ((finiteGaloisClosedFixingSubgroup K L).toSubgroup.subgroupOf
      (closedFixingSubgroup
        (⊥ : IntermediateField K (SeparableClosure K))).toSubgroup).index =
      Module.finrank K L :=
  finiteGaloisExtensionSubgroupOfEmbedding_index_eq_finrank K L
    (separableEmbeddingIntoSeparableClosure K L)

end

end Atlas.Knowledge
