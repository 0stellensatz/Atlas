import Mathlib
import Atlas.Knowledge.AbstractExtensionUnitsRepIso
import Atlas.Knowledge.FiniteNormQuotient

/-!
# relative norm at an abstract base as the field norm

The engine's relative norm at an arbitrary finite abstract base, compared
with the field norm of the concrete relative extension: on a unit of the
upper fixed field, the coset sum over the engine's relative quotient is the
product over the concrete Galois group, which is the field norm of the
Galois extension `E/F` of fixed fields. The finite norm quotient of the
engine is therefore the multiplicative norm quotient `Fˣ / N(Eˣ)`, written
additively. This is what turns the class-field axiom's cardinality into a
statement the local norm-index theorem proves (#104).

## Main definitions

* `finiteNormQuotientEquivRelativeNormQuotient` — the engine's norm quotient
  is `Fˣ / N_{E/F}(Eˣ)`.

## Main statements

* `relativeNorm_abstractRelativeFixedFieldUnit_val` — the engine's relative
  norm of an upper unit is the field norm; proved.
* `map_finiteNormSubgroup_eq_relativeAdditiveNormSubgroup` — the norm
  subgroups correspond under the unit dictionary; proved.

## Implementation notes

The bottom-base comparison of the layer runs through embeddings; at an
arbitrary base the relative quotient is the concrete Galois group by the
relative dictionary, the coset action is the Galois action, and the product
over automorphisms is Mathlib's `Algebra.norm_eq_prod_automorphisms` — the
extension of fixed fields is Galois here, by the engine's normality witness,
where the bottom-base statement needed none. The quotient transport mirrors
the source's bottom-base `finiteNormQuotientEquivNormQuotient`, which is not
otherwise ported — at the pin its only transitive consumer is the
embedding-independence transport that the arc's fixed ambient field makes
vacuous.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable (k : Type u) (Ω : Type v) [Field k] [Field Ω] [Algebra k Ω]
  [IsGalois k Ω]
variable (K L : ClosedSubgroup (Ω ≃ₐ[k] Ω))
  (hLK : L.toSubgroup ≤ K.toSubgroup)
  (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)

include hnormal in
/-- **The engine's relative norm of an upper unit is the field norm** of the
concrete Galois extension of fixed fields ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:112`]
[Yamaguchi2026] — the bottom-base form; here at an arbitrary base through
the relative dictionary). -/
theorem relativeNorm_abstractRelativeFixedFieldUnit_val
    [Finite ((baseField (Ω ≃ₐ[k] Ω)).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup)]
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (x : (abstractRelativeFixedField k Ω hLK)ˣ) :
    ((Additive.toMul
      ((relativeNorm (galoisAmbientUnitsRep k Ω) K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK
          (Additive.ofMul x))).1 : Additive Ωˣ) : Ωˣ) : Ω) =
      algebraMap (abstractFixedField k Ω K) Ω
        (Algebra.norm (abstractFixedField k Ω K)
          (x : abstractRelativeFixedField k Ω hLK)) := by
  letI := hnormal
  let F := abstractFixedField k Ω K
  let E := abstractRelativeFixedField k Ω hLK
  let Q := K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup
  letI := Fintype.ofFinite Q
  letI : IsGalois F E :=
    abstractRelativeFixedField_isGalois k Ω K L hLK hnormal
  letI : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional k Ω K L hLK ‹_› ‹_›
  change
    ((Additive.toMul
      (relativeNormValue (galoisAmbientUnitsRep k Ω) K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK
          (Additive.ofMul x))) : Ωˣ) : Ω) = _
  rw [relativeNormValue]
  change
    (↑(Additive.toMul (∑ q : Q,
      relativeCosetAction (galoisAmbientUnitsRep k Ω) K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK
          (Additive.ofMul x)) q) : Ωˣ) : Ω) = _
  rw [toMul_sum]
  change (Units.coeHom Ω) (∏ q : Q,
    Additive.toMul
      (relativeCosetAction (galoisAmbientUnitsRep k Ω) K L hLK
        (abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK
          (Additive.ofMul x)) q)) = _
  rw [map_prod]
  change
    (∏ q : Q,
      ((Additive.toMul
        (relativeCosetAction (galoisAmbientUnitsRep k Ω) K L hLK
          (abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK
            (Additive.ofMul x)) q) : Ωˣ) : Ω)) = _
  calc
    _ = ∏ σ : (E ≃ₐ[F] E),
        (((Additive.toMul
          ((galoisAmbientUnitsRep F E).ρ σ (Additive.ofMul x)) : Eˣ) :
            E) : Ω) := by
      refine Fintype.prod_equiv
        (abstractExtensionQuotientEquivGaloisGroup
          k Ω K L hLK hnormal).toEquiv
        _ _ ?_
      intro q
      exact relativeCosetAction_abstractRelativeFixedFieldUnit_val
        k Ω K L hLK hnormal (Additive.ofMul x) q
    _ = ∏ σ : (E ≃ₐ[F] E), ((σ (x : E) : E) : Ω) := by
      refine Finset.prod_congr rfl fun σ _ => ?_
      rfl
    _ = ((∏ σ : (E ≃ₐ[F] E), σ (x : E) : E) : Ω) :=
      (map_prod E.val _ Finset.univ).symm
    _ = algebraMap F Ω (Algebra.norm F (x : E)) := by
      rw [← Algebra.norm_eq_prod_automorphisms]
      exact E.val.commutes _

include hnormal in
/-- **The engine's finite norm subgroup corresponds to the field-norm
subgroup** under the unit dictionary at the base ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:193`]
[Yamaguchi2026] — the bottom-base form; here at an arbitrary base). -/
theorem map_finiteNormSubgroup_eq_relativeAdditiveNormSubgroup
    [Finite ((baseField (Ω ≃ₐ[k] Ω)).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup)]
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    (finiteNormSubgroup (galoisAmbientUnitsRep k Ω) K L hLK).map
        (abstractFixedFieldUnitsEquivGaloisFixed k Ω K).symm.toAddMonoidHom =
      (MonoidHom.toAdditive
        (Units.map (Algebra.norm (abstractFixedField k Ω K) :
          abstractRelativeFixedField k Ω hLK →*
            abstractFixedField k Ω K))).range := by
  let F := abstractFixedField k Ω K
  let E := abstractRelativeFixedField k Ω hLK
  let eK := abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  let eL := abstractRelativeFixedFieldUnitsEquivGaloisFixed k Ω K L hLK
  have key : ∀ xE : Eˣ,
      eK.symm (relativeNorm (galoisAmbientUnitsRep k Ω) K L hLK
          (eL (Additive.ofMul xE))) =
        Additive.ofMul (Units.map (Algebra.norm F : E →* F) xE) := by
    intro xE
    rw [AddEquiv.symm_apply_eq]
    apply Subtype.ext
    apply Additive.ext
    apply Units.ext
    exact relativeNorm_abstractRelativeFixedFieldUnit_val
      k Ω K L hLK hnormal xE
  ext y
  constructor
  · rintro ⟨a, ⟨b, rfl⟩, rfl⟩
    let xE : Eˣ := Additive.toMul (eL.symm b)
    have hb : eL (Additive.ofMul xE) = b := eL.apply_symm_apply b
    refine ⟨Additive.ofMul xE, ?_⟩
    change Additive.ofMul (Units.map (Algebra.norm F : E →* F) xE) =
      eK.symm.toAddMonoidHom
        (relativeNorm (galoisAmbientUnitsRep k Ω) K L hLK b)
    rw [← hb]
    exact (key xE).symm
  · rintro ⟨a, rfl⟩
    let xE : Eˣ := Additive.toMul a
    refine ⟨relativeNorm (galoisAmbientUnitsRep k Ω) K L hLK
      (eL (Additive.ofMul xE)), ⟨eL (Additive.ofMul xE), rfl⟩, ?_⟩
    exact key xE

include hnormal in
/-- **The engine's finite norm quotient is the multiplicative norm quotient
`Fˣ / N(Eˣ)`, written additively** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:233`]
[Yamaguchi2026] — the bottom-base form; here at an arbitrary base). -/
def finiteNormQuotientEquivRelativeNormQuotient
    [Finite ((baseField (Ω ≃ₐ[k] Ω)).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup)]
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    FiniteNormQuotient (galoisAmbientUnitsRep k Ω) K L hLK ≃+
      Additive ((abstractFixedField k Ω K)ˣ ⧸
        (Units.map (Algebra.norm (abstractFixedField k Ω K) :
          abstractRelativeFixedField k Ω hLK →*
            abstractFixedField k Ω K)).range) := by
  let F := abstractFixedField k Ω K
  let E := abstractRelativeFixedField k Ω hLK
  let A := galoisAmbientUnitsRep k Ω
  let S := finiteNormSubgroup A K L hLK
  let e := abstractFixedFieldUnitsEquivGaloisFixed k Ω K
  let normAdd : Additive Fˣ →+
      Additive (Fˣ ⧸ (Units.map (Algebra.norm F : E →* F)).range) :=
    MonoidHom.toAdditive
      (QuotientGroup.mk' (Units.map (Algebra.norm F : E →* F)).range)
  let T := normAdd.ker
  have hmap : S.map e.symm.toAddMonoidHom = T := by
    rw [map_finiteNormSubgroup_eq_relativeAdditiveNormSubgroup
      k Ω K L hLK hnormal]
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      change Additive.ofMul (QuotientGroup.mk
        (Units.map (Algebra.norm F : E →* F) (Additive.toMul a))) = 0
      rw [show (0 : Additive (Fˣ ⧸
          (Units.map (Algebra.norm F : E →* F)).range)) =
        Additive.ofMul 1 from rfl]
      apply congrArg Additive.ofMul
      rw [QuotientGroup.eq_one_iff]
      exact ⟨Additive.toMul a, rfl⟩
    · intro hy
      change Additive.ofMul (QuotientGroup.mk (Additive.toMul y)) = 0 at hy
      have h1 : QuotientGroup.mk (s := (Units.map
          (Algebra.norm F : E →* F)).range) (Additive.toMul y) = 1 :=
        congrArg Additive.toMul hy
      rw [QuotientGroup.eq_one_iff] at h1
      obtain ⟨u, hu⟩ := h1
      exact ⟨Additive.ofMul u, by
        apply Additive.ext
        exact hu⟩
  have hforward : S ≤ AddSubgroup.comap e.symm.toAddMonoidHom T := by
    intro s hs
    change e.symm s ∈ T
    rw [← hmap]
    exact ⟨s, hs, rfl⟩
  have hinverse : T ≤ AddSubgroup.comap e.toAddMonoidHom S := by
    intro y hy
    change e y ∈ S
    have hy' : y ∈ S.map e.symm.toAddMonoidHom := by
      rw [hmap]
      exact hy
    rcases hy' with ⟨s, hs, hsy⟩
    have heq : e y = s := by
      apply e.symm.injective
      simpa using hsy.symm
    rw [heq]
    exact hs
  let f : (ambientFixedAddSubgroup A K ⧸ S) →+ (Additive Fˣ ⧸ T) :=
    QuotientAddGroup.map S T e.symm.toAddMonoidHom hforward
  let g : (Additive Fˣ ⧸ T) →+ (ambientFixedAddSubgroup A K ⧸ S) :=
    QuotientAddGroup.map T S e.toAddMonoidHom hinverse
  let modelEquiv :
      (ambientFixedAddSubgroup A K ⧸ S) ≃+ (Additive Fˣ ⧸ T) :=
    { toFun := f
      invFun := g
      left_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro a
        change ↑(e (e.symm a)) = (↑a : ambientFixedAddSubgroup A K ⧸ S)
        rw [e.apply_symm_apply]
      right_inv := by
        intro q
        refine QuotientAddGroup.induction_on q ?_
        intro y
        change ↑(e.symm (e y)) = (↑y : Additive Fˣ ⧸ T)
        rw [e.symm_apply_apply]
      map_add' := f.map_add }
  let firstIso : (Additive Fˣ ⧸ T) ≃+
      Additive (Fˣ ⧸ (Units.map (Algebra.norm F : E →* F)).range) :=
    QuotientAddGroup.quotientKerEquivOfSurjective normAdd (by
      intro y
      obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective
        (Units.map (Algebra.norm F : E →* F)).range (Additive.toMul y)
      exact ⟨Additive.ofMul u, by
        apply Additive.ext
        exact hu⟩)
  exact (finiteNormQuotientConcreteEquiv A K L hLK).trans
    (modelEquiv.trans firstIso)

include hnormal in
/-- The norm-quotient equivalence computes on classes: the class of `a` goes
to the class of the unit the dictionary attaches to `a` ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableUnitsNorm.lean:307`]
[Yamaguchi2026] — the bottom-base form; here at an arbitrary base). -/
@[simp]
theorem finiteNormQuotientEquivRelativeNormQuotient_finiteNormClass
    [Finite ((baseField (Ω ≃ₐ[k] Ω)).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField (Ω ≃ₐ[k] Ω)).toSubgroup)]
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup (galoisAmbientUnitsRep k Ω) K) :
    finiteNormQuotientEquivRelativeNormQuotient k Ω K L hLK hnormal
        (finiteNormClass (galoisAmbientUnitsRep k Ω) K L hLK a) =
      Additive.ofMul (QuotientGroup.mk (Additive.toMul
        ((abstractFixedFieldUnitsEquivGaloisFixed k Ω K).symm a))) :=
  rfl

end

end Atlas.Knowledge
