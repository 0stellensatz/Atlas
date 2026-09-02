import Mathlib
import Atlas.Knowledge.AdditiveNormSubgroup
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.GaloisExtensionQuotient
import Atlas.Knowledge.IntermediateFieldUnitsFixedSubgroup
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.NormUnits
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.ResidueDatumIn
import Atlas.Knowledge.SeparableFixedFieldNorm

/-!
# finite norm quotient equivalence

For a finite intermediate field of a Galois ambient extension,
the finite norm quotient of the abstract class formation is the actual
multiplicative field norm quotient `Kˣ/N_{E/K}(Eˣ)`, written
additively — and for an embedded finite Galois extension `L/K`, the
comparison continues through the embedding, so the abstract quotient
attached to the realization is `Kˣ/N_{L/K}(Lˣ)` itself (#104).

## Main definitions

* `finiteNormQuotientEquivNormQuotient` — the abstract finite norm
  quotient is the concrete one, at an intermediate field.
* `finiteNormQuotientEquivEmbeddedNormQuotient` — the same through a
  chosen embedding of `L/K`.

## Main statements

* `map_finiteNormSubgroup_eq_additiveNormSubgroup` — the abstract
  finite norm subgroup corresponds to the field-norm subgroup under
  the base-unit dictionary; proved.
* `localNormSubgroup_fieldRange_eq` — the norm subgroup is independent
  of the chosen realization; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling
behind the engine names, `closedFixingSubgroup` takes only the
intermediate field, and the Galois-only norm comparison the source
rewrites with becomes the layer's
`relativeNorm_intermediateFieldUnit_of_isSeparable`, whose separability
hypothesis the ambient Galois context synthesizes. The ambient carries
`[IsSepClosed Ω]` beyond the source's `[IsGalois K Ω]`: both the
layer's finiteness instance for the base fixing quotient and its
separable norm comparison carry it, where the source runs a Galois-only
route — the local instantiation's ambient is the chosen separable
closure, so nothing narrows. With the separable route the source's
`[IsGalois K E]` is dead in the whole intermediate section, so the
section sheds it with its Galois name, and two embedded-section
declarations omit an unused `[IsGalois K L]`, as the layer's linters
require. The two `AlgHom.fieldRange`-keyed instances stay
`local instance`s, as in the source. Everything else ports
token-for-token; the file is the source's
`LocalReciprocity/SeparableUnitsNorm.lean:193`–`:456`, and it closes
that source file against the layer: the file's earlier slices live in
`Atlas.Knowledge.SeparableFixedFieldNorm` and around it, and its
Galois-only finiteness instance, coset-action formula, and norm
comparison are not ported — the separable forms subsume each at every
use site.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

open scoped BigOperators

variable (K : Type) (Ω : Type) [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

section FiniteIntermediate

variable (E : IntermediateField K Ω) [FiniteDimensional K E]

/-- **Under the base-field fixed-unit equivalence, the abstract finite
norm subgroup is exactly the ordinary field-norm subgroup**
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:193`]
[Yamaguchi2026]). -/
theorem map_finiteNormSubgroup_eq_additiveNormSubgroup :
    (finiteNormSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E)).map
        (baseUnitsEquivGaloisAmbientFixed K Ω).symm.toAddMonoidHom =
      additiveNormSubgroup K E := by
  ext y
  constructor
  · rintro ⟨a, ha, rfl⟩
    rcases ha with ⟨b, rfl⟩
    let u : Eˣ := Additive.toMul
      ((intermediateFieldUnitsEquivGaloisFixed K Ω E).symm b)
    have hb :
        intermediateFieldUnitsEquivGaloisFixed K Ω E
            (Additive.ofMul u) = b := by
      change intermediateFieldUnitsEquivGaloisFixed K Ω E
          ((intermediateFieldUnitsEquivGaloisFixed K Ω E).symm b) = b
      exact (intermediateFieldUnitsEquivGaloisFixed K Ω E).apply_symm_apply b
    rw [← hb, relativeNorm_intermediateFieldUnit_of_isSeparable]
    change (baseUnitsEquivGaloisAmbientFixed K Ω).symm
      (baseUnitsEquivGaloisAmbientFixed K Ω
        (Additive.ofMul (normUnits K E u))) ∈ additiveNormSubgroup K E
    rw [(baseUnitsEquivGaloisAmbientFixed K Ω).symm_apply_apply]
    exact ⟨u, rfl⟩
  · intro hy
    change Additive.toMul y ∈ localNormSubgroup K E at hy
    rcases hy with ⟨u, hu⟩
    refine ⟨baseUnitsEquivGaloisAmbientFixed K Ω
      (Additive.ofMul (normUnits K E u)), ?_, ?_⟩
    · refine ⟨intermediateFieldUnitsEquivGaloisFixed K Ω E
        (Additive.ofMul u), ?_⟩
      exact relativeNorm_intermediateFieldUnit_of_isSeparable K Ω E u
    · change (baseUnitsEquivGaloisAmbientFixed K Ω).symm
        (baseUnitsEquivGaloisAmbientFixed K Ω
          (Additive.ofMul (normUnits K E u))) = y
      rw [(baseUnitsEquivGaloisAmbientFixed K Ω).symm_apply_apply]
      exact congrArg Additive.ofMul hu

/-- **The abstract finite norm quotient is the actual multiplicative
field norm quotient**, written additively for the abstract
class-formation API ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:233`]
[Yamaguchi2026]). -/
def finiteNormQuotientEquivNormQuotient :
    FiniteNormQuotient (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E) ≃+
      Additive (NormQuotient K E) := by
  let S := finiteNormSubgroup (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E)
  let normAdd : Additive Kˣ →+ Additive (NormQuotient K E) :=
    MonoidHom.toAdditive (normClass K E)
  let T := normAdd.ker
  let e := baseUnitsEquivGaloisAmbientFixed K Ω
  have hmap : S.map e.symm.toAddMonoidHom = T := by
    simpa [S, T, normAdd, e] using
      (map_finiteNormSubgroup_eq_additiveNormSubgroup K Ω E).trans
        (additiveNormSubgroup_eq_ker_quotient_map K E)
  have hforward : S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro x hx
    change e.symm x ∈ T
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  have hinverse : T ≤ AddSubgroup.comap e.toAddMonoidHom S := by
    intro y hy
    change e y ∈ S
    have hy' : y ∈ S.map e.symm.toAddMonoidHom := by
      rw [hmap]
      exact hy
    rcases hy' with ⟨x, hx, hxy⟩
    have heq : e y = x := by
      apply e.symm.injective
      simpa using hxy.symm
    rw [heq]
    exact hx
  let f : (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup (⊥ : IntermediateField K Ω)) ⧸ S) →+
      (Additive Kˣ ⧸ T) :=
    QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
  let g : (Additive Kˣ ⧸ T) →+
      (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω)) ⧸ S) :=
    QuotientAddGroup.map T S e.toAddMonoidHom hinverse
  let modelEquiv :
      (ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup (⊥ : IntermediateField K Ω)) ⧸ S) ≃+
        (Additive Kˣ ⧸ T) :=
    { toFun := f
      invFun := g
      left_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change ↑(e (e.symm x)) = (↑x :
          ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
            (closedFixingSubgroup (⊥ : IntermediateField K Ω)) ⧸ S)
        rw [e.apply_symm_apply]
      right_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro x
        change ↑(e.symm (e x)) = (↑x : Additive Kˣ ⧸ T)
        rw [e.symm_apply_apply]
      map_add' := f.map_add }
  let firstIso : (Additive Kˣ ⧸ T) ≃+ Additive (NormQuotient K E) :=
    QuotientAddGroup.quotientKerEquivOfSurjective normAdd
      (QuotientGroup.mk'_surjective (localNormSubgroup K E))
  exact (finiteNormQuotientConcreteEquiv (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E)).trans
      (modelEquiv.trans firstIso)

/-- The fixed-unit comparison carries the canonical finite norm class
to the canonical field norm class; the concrete quotient
representation remains private to the proof of this boundary theorem
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:307`]
[Yamaguchi2026]). -/
@[simp]
theorem finiteNormQuotientEquivNormQuotient_finiteNormClass
    (a : ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :
    finiteNormQuotientEquivNormQuotient K Ω E
        (finiteNormClass (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E) a) =
      (MonoidHom.toAdditive (normClass K E))
        ((baseUnitsEquivGaloisAmbientFixed K Ω).symm a) := by
  let S := finiteNormSubgroup (galoisAmbientUnitsRep K Ω)
    (closedFixingSubgroup (⊥ : IntermediateField K Ω))
    (closedFixingSubgroup E) (fixingSubgroupLeBase K Ω E)
  let normAdd : Additive Kˣ →+ Additive (NormQuotient K E) :=
    MonoidHom.toAdditive (normClass K E)
  let T := normAdd.ker
  let e := baseUnitsEquivGaloisAmbientFixed K Ω
  have hmap : S.map e.symm.toAddMonoidHom = T := by
    simpa [S, T, normAdd, e] using
      (map_finiteNormSubgroup_eq_additiveNormSubgroup K Ω E).trans
        (additiveNormSubgroup_eq_ker_quotient_map K E)
  have hforward : S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro x hx
    change e.symm x ∈ T
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  simp only [finiteNormQuotientEquivNormQuotient,
    finiteNormQuotientConcreteEquiv_finiteNormClass,
    AddEquiv.trans_apply,
    QuotientAddGroup.quotientKerEquivOfSurjective,
    QuotientAddGroup.quotientKerEquivOfRightInverse]
  change QuotientAddGroup.kerLift normAdd
      (QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
        (QuotientAddGroup.mk' S a)) = normAdd (e.symm a)
  rw [QuotientAddGroup.map_mk', QuotientAddGroup.kerLift_mk]
  rfl

end FiniteIntermediate

section EmbeddedFiniteGaloisExtension

variable (L : Type) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  (i : L →ₐ[K] Ω)

noncomputable local instance embeddedFieldRangeFiniteDimensional :
    FiniteDimensional K (AlgHom.fieldRange i) :=
  (AlgEquiv.ofInjectiveField i).toLinearEquiv.finiteDimensional

noncomputable local instance embeddedFieldRangeIsGalois :
    IsGalois K (AlgHom.fieldRange i) :=
  IsGalois.of_algEquiv (AlgEquiv.ofInjectiveField i)

omit [IsGalois K Ω] [IsSepClosed Ω] [FiniteDimensional K L] [IsGalois K L] in
/-- The field norm is invariant under an algebra equivalence, at unit
level ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:362`]
[Yamaguchi2026]). -/
theorem normUnits_embeddedExtensionAlgEquiv (x : Lˣ) :
    normUnits K (AlgHom.fieldRange i)
        (Units.mapEquiv (AlgEquiv.ofInjectiveField i).toMulEquiv x) =
      normUnits K L x := by
  apply Units.ext
  exact Algebra.norm_eq_of_algEquiv
    (AlgEquiv.ofInjectiveField i) (x : L)

omit [IsGalois K Ω] [IsSepClosed Ω] [FiniteDimensional K L] [IsGalois K L] in
/-- **The ordinary norm subgroups are independent of the chosen
realization of the finite extension inside the ambient Galois
extension** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:374`]
[Yamaguchi2026]). -/
theorem localNormSubgroup_fieldRange_eq :
    localNormSubgroup K (AlgHom.fieldRange i) = localNormSubgroup K L := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    let z : Lˣ := Units.mapEquiv
      (AlgEquiv.ofInjectiveField i).symm.toMulEquiv y
    refine ⟨z, ?_⟩
    have hz : Units.mapEquiv
        (AlgEquiv.ofInjectiveField i).toMulEquiv z = y := by
      exact (Units.mapEquiv
        (AlgEquiv.ofInjectiveField i).toMulEquiv).apply_symm_apply y
    rw [← hz, normUnits_embeddedExtensionAlgEquiv]
  · rintro ⟨x, rfl⟩
    refine ⟨Units.mapEquiv
      (AlgEquiv.ofInjectiveField i).toMulEquiv x, ?_⟩
    exact normUnits_embeddedExtensionAlgEquiv K Ω L i x

omit [IsGalois K L] in
/-- The abstract relative norm attached to an embedded finite Galois
extension is the actual field norm on its unit group ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:394`]
[Yamaguchi2026]). -/
theorem relativeNorm_embeddedExtensionUnit (x : Lˣ) :
    relativeNorm (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup (AlgHom.fieldRange i))
        (fixingSubgroupLeBase K Ω (AlgHom.fieldRange i))
        (embeddedFieldUnitsEquivGaloisFixed K Ω L i (Additive.ofMul x)) =
      baseUnitsEquivGaloisAmbientFixed K Ω
        (Additive.ofMul (normUnits K L x)) := by
  change relativeNorm (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup (⊥ : IntermediateField K Ω))
      (closedFixingSubgroup (AlgHom.fieldRange i))
      (fixingSubgroupLeBase K Ω (AlgHom.fieldRange i))
      (intermediateFieldUnitsEquivGaloisFixed K Ω
        (AlgHom.fieldRange i)
        (Additive.ofMul (Units.mapEquiv
          (AlgEquiv.ofInjectiveField i).toMulEquiv x))) = _
  rw [relativeNorm_intermediateFieldUnit_of_isSeparable,
    normUnits_embeddedExtensionAlgEquiv]

/-- **For an embedded finite Galois extension `L/K`, the finite norm
quotient in the abstract class formation is the actual quotient
`Kˣ/N_{L/K}(Lˣ)`** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:415`]
[Yamaguchi2026]). -/
def finiteNormQuotientEquivEmbeddedNormQuotient :
    FiniteNormQuotient (galoisAmbientUnitsRep K Ω)
        (closedFixingSubgroup (⊥ : IntermediateField K Ω))
        (closedFixingSubgroup (AlgHom.fieldRange i))
        (fixingSubgroupLeBase K Ω (AlgHom.fieldRange i)) ≃+
      Additive (NormQuotient K L) :=
  (finiteNormQuotientEquivNormQuotient K Ω (AlgHom.fieldRange i)).trans
    (MulEquiv.toAdditive
      (normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
        (localNormSubgroup_fieldRange_eq K Ω L i)))

omit [IsGalois K L] in
/-- The embedded-extension comparison carries a canonical finite norm
class to the corresponding field norm class, followed by the canonical
transport from the embedded field range to `L` ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:430`]
[Yamaguchi2026]). -/
@[simp]
theorem finiteNormQuotientEquivEmbeddedNormQuotient_finiteNormClass
    (a : ambientFixedAddSubgroup (galoisAmbientUnitsRep K Ω)
      (closedFixingSubgroup (⊥ : IntermediateField K Ω))) :
    finiteNormQuotientEquivEmbeddedNormQuotient K Ω L i
        (finiteNormClass (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup (AlgHom.fieldRange i))
          (fixingSubgroupLeBase K Ω (AlgHom.fieldRange i)) a) =
      (MulEquiv.toAdditive
        (normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
          (localNormSubgroup_fieldRange_eq K Ω L i)))
        ((MonoidHom.toAdditive (normClass K (AlgHom.fieldRange i)))
          ((baseUnitsEquivGaloisAmbientFixed K Ω).symm a)) := by
  change (MulEquiv.toAdditive
      (normQuotientEquivOfNormSubgroupEq K (AlgHom.fieldRange i) L
        (localNormSubgroup_fieldRange_eq K Ω L i)))
      (finiteNormQuotientEquivNormQuotient K Ω (AlgHom.fieldRange i)
        (finiteNormClass (galoisAmbientUnitsRep K Ω)
          (closedFixingSubgroup (⊥ : IntermediateField K Ω))
          (closedFixingSubgroup (AlgHom.fieldRange i))
          (fixingSubgroupLeBase K Ω (AlgHom.fieldRange i)) a)) = _
  rw [finiteNormQuotientEquivNormQuotient_finiteNormClass]

end EmbeddedFiniteGaloisExtension

end

end Atlas.Knowledge
