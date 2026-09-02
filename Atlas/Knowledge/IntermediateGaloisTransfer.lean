import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.ExtensionFixedRepresentation
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityHom
import Atlas.Knowledge.FiniteReciprocityNaturalityNorm
import Atlas.Knowledge.FiniteResidueAbstractExtension
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.TransferFrobeniusTerms
import Atlas.Knowledge.TransferNaturality
import Atlas.Knowledge.TransferNormArithmetic
import Atlas.Knowledge.TransferNormFrobeniusGeometry
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.ValuationData

/-!
# Intermediate Galois transfer

The transfer apparatus of transfer–norm naturality on the finite Galois
quotients: the inclusion `G(L|K') →* G(L|K)` with its image copy and
identification, the transfer into the intermediate abelianization,
its commutation with restriction from the infinite Frobenius quotients
and its Frobenius-product and double-coset formulas, the abelianized
reciprocity arrow, the invariant-carrier identification, and the chosen
right-coset decomposition (#104).

## Main definitions

* `transferNormNaturalityIntermediateInclusion` — the inclusion.
* `transferNormNaturalityIntermediateSubgroup` — its image copy.
* `transferNormNaturalityIntermediateQuotientEquiv` — the
  identification.
* `transferNormNaturalityTransfer` — the transfer arrow.
* `DegreeData.transferNormNaturalityAbelianizedReciprocity` — the
  abelianized reciprocity arrow.
* `transferNormNaturalityExtensionFixedEquiv` — the invariant-carrier
  identification.

## Main statements

* `transferNormNaturalityIntermediateInclusion_injective` — the
  inclusion is injective; proved.
* `DegreeData.transferNormNaturalityFrobeniusIntermediate_map_restriction`
  — restriction maps copy onto copy; proved.
* `DegreeData.transferNormNaturalityTransfer_restriction_natural` —
  transfer commutes with restriction; proved.
* `DegreeData.transferNormNaturalityTransfer_frobenius_product` — the
  Frobenius-product identity; proved.
* `transferNormNaturality_transfer_doubleCoset_formula` — the
  double-coset formula; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
with `Subgroup.mem_subgroupOf` — its explicit arguments dropped, the
layer's rule taking them implicitly — for the source's membership rule.
The group-only sections stay at `Type u` , and the invariant-carrier
section generalizes to it, nothing pinning the source's universe
device; the abelianized reciprocity section alone is `Type` , pinned by
the `Type` -pinned `finiteReciprocityHom` . The inclusion is built on
the layer's slimmed `finiteReciprocityNaturalityRestriction` , whose
two freed containments drop from the call; both
`intermediateExtension_normal` sites drop the containment #175 shed;
and the freed `hLK'` cascades off the whole inclusion family — eleven
declarations lose it, so their argument lists are one shorter than the
source's. The dead-binder sweep sheds three topological-group instances
and two Hausdorff ones, all simply unused. The three transversal
helpers, private in the source, turn public: the naturality endpoint
consumes them from the next brick, and `private` does not cross files.
The citations name this file by bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/` in the source. The
source's namespace `open` s go, while `open MulAction` stays for the
orbit vocabulary.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

open MulAction

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]


/-- **The inclusion `G(L|K') →* G(L|K)` induced by `G_K' ≤ G_K`**
([Yamaguchi 2026, `MainTransfer.lean:28`][Yamaguchi2026]). -/
def transferNormNaturalityIntermediateInclusion
    (K K' L : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) →*
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
  finiteReciprocityNaturalityRestriction K K' L L hK'K le_rfl

/-- The inclusion evaluates by `Subgroup.inclusion` on representatives
([Yamaguchi 2026, `MainTransfer.lean:44`][Yamaguchi2026]). -/
@[simp]
theorem transferNormNaturalityIntermediateInclusion_mk
    (K K' L : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    (k' : K'.toSubgroup) :
    transferNormNaturalityIntermediateInclusion K K' L hK'K
        (QuotientGroup.mk k') =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') :=
  rfl

/-- **The inclusion of finite Galois groups is injective**
([Yamaguchi 2026, `MainTransfer.lean:58`][Yamaguchi2026]). -/
theorem transferNormNaturalityIntermediateInclusion_injective
    (K K' L : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    Function.Injective
      (transferNormNaturalityIntermediateInclusion K K' L hK'K) := by
  intro x y
  refine QuotientGroup.induction_on x ?_
  intro k'
  refine QuotientGroup.induction_on y ?_
  intro l' h
  apply QuotientGroup.eq.mpr
  apply (Subgroup.mem_subgroupOf).2
  have hmem :
      (Subgroup.inclusion hK'K k')⁻¹ *
          Subgroup.inclusion hK'K l' ∈
        L.toSubgroup.subgroupOf K.toSubgroup :=
    QuotientGroup.eq.mp h
  have hG := (Subgroup.mem_subgroupOf).1 hmem
  simpa using hG

/-- **The copy of `G(L|K')` inside `G(L|K)`**
([Yamaguchi 2026, `MainTransfer.lean:84`][Yamaguchi2026]). -/
def transferNormNaturalityIntermediateSubgroup
    (K K' L : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    Subgroup (K.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.toSubgroup) :=
  (transferNormNaturalityIntermediateInclusion K K' L hK'K).range

/-- **The canonical identification of `G(L|K')` with its image**
([Yamaguchi 2026, `MainTransfer.lean:96`][Yamaguchi2026]). -/
noncomputable def transferNormNaturalityIntermediateQuotientEquiv
    (K K' L : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) ≃*
      transferNormNaturalityIntermediateSubgroup K K' L hK'K :=
  MulEquiv.ofBijective
    (transferNormNaturalityIntermediateInclusion K K' L hK'K).rangeRestrict
    ⟨fun _ _ h =>
        transferNormNaturalityIntermediateInclusion_injective K K' L hK'K
          (congrArg Subtype.val h),
      MonoidHom.rangeRestrict_surjective _⟩

/-- The identification evaluates by inclusion on representatives
([Yamaguchi 2026, `MainTransfer.lean:116`][Yamaguchi2026]). -/
@[simp]
theorem transferNormNaturalityIntermediateQuotientEquiv_mk
    (K K' L : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    (k' : K'.toSubgroup) :
    (transferNormNaturalityIntermediateQuotientEquiv K K' L hK'K
      (QuotientGroup.mk k')).1 =
      QuotientGroup.mk (Subgroup.inclusion hK'K k') :=
  rfl

namespace DegreeData

/-- **Restriction sends the Frobenius-level intermediate subgroup
exactly onto the finite intermediate Galois subgroup**
([Yamaguchi 2026, `MainTransfer.lean:132`][Yamaguchi2026]). -/
theorem transferNormNaturalityFrobeniusIntermediate_map_restriction
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal] :
    (D.transferNormNaturalityFrobeniusIntermediateSubgroup
        E L hL).map
        (D.extensionRestriction E.base.field L (hL.trans E.below)) =
      transferNormNaturalityIntermediateSubgroup
        E.base.field E.field.field L E.below := by
  have hcomm (x : E.field.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L hL) :
      transferNormNaturalityIntermediateInclusion
          E.base.field E.field.field L E.below
          (D.extensionRestriction E.field.field L hL x) =
        D.extensionRestriction E.base.field L (hL.trans E.below)
          (D.finiteReciprocityNaturalityFrobeniusTowerMap
            E.base.field E.field.field L L
            (hL.trans E.below) hL E.below le_rfl x) := by
    refine QuotientGroup.induction_on x ?_
    intro k'
    rfl
  ext q
  constructor
  · rintro ⟨h, hh, rfl⟩
    rcases hh with ⟨x, rfl⟩
    exact ⟨D.extensionRestriction E.field.field L hL x, hcomm x⟩
  · rintro ⟨x, rfl⟩
    refine QuotientGroup.induction_on x ?_
    intro k'
    refine ⟨QuotientGroup.mk (Subgroup.inclusion E.below k'), ?_, rfl⟩
    exact ⟨QuotientGroup.mk k', rfl⟩

end DegreeData

/-- **The left vertical arrow of transfer–norm naturality**: Mathlib's
actual transfer into the intermediate subgroup's abelianization,
transported along the identification with `G(L|K')`
([Yamaguchi 2026, `MainTransfer.lean:172`][Yamaguchi2026]). -/
noncomputable def transferNormNaturalityTransfer
    (K K' L : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    [Finite (K.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.toSubgroup)] :
    Abelianization (K.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.toSubgroup) →*
      Abelianization (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) := by
  let H := transferNormNaturalityIntermediateSubgroup K K' L hK'K
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  let e := transferNormNaturalityIntermediateQuotientEquiv K K' L hK'K
  exact e.symm.abelianizationCongr.toMonoidHom.comp
    (Abelianization.lift
      (MonoidHom.transfer (Abelianization.of : H →* Abelianization H)))

namespace DegreeData

/-- **Transfer commutes with restriction from the infinite Frobenius
quotients to the finite Galois quotients** — the quotient-naturality
step ([Yamaguchi 2026, `MainTransfer.lean:195`][Yamaguchi2026]). -/
theorem transferNormNaturalityTransfer_restriction_natural
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    [hLfinite : Finite
      (E.base.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf E.base.field.toSubgroup)] :
    (transferNormNaturalityTransfer
        E.base.field E.field.field L E.below).comp
        (Abelianization.map
          (D.extensionRestriction E.base.field L (hL.trans E.below))) =
      (Abelianization.map
        (D.extensionRestriction E.field.field L hL)).comp
        (D.transferNormNaturalityFrobeniusTransfer E L hL) := by
  let P := E.base.field.toSubgroup ⧸
    D.extensionInertiaWithin E.base.field L (hL.trans E.below)
  let Q := E.base.field.toSubgroup ⧸
    L.toSubgroup.subgroupOf E.base.field.toSubgroup
  let f : P →* Q :=
    D.extensionRestriction E.base.field L (hL.trans E.below)
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
    E L hL
  let H₀ := transferNormNaturalityIntermediateSubgroup
    E.base.field E.field.field L E.below
  let e := D.transferNormNaturalityFrobeniusIntermediateEquiv
    E L hL
  let e₀ := transferNormNaturalityIntermediateQuotientEquiv
    E.base.field E.field.field L E.below
  letI : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex E L hL
  have hf : Function.Surjective f :=
    D.transferNormNaturalityExtensionRestriction_surjective
      E.base.field L (hL.trans E.below)
  have hker : f.ker ≤ H :=
    D.transferNormNaturalityExtensionRestriction_ker_le_intermediate
      E L hL
  have hmap : H.map f = H₀ :=
    D.transferNormNaturalityFrobeniusIntermediate_map_restriction
      E L hL
  let c : H.map f ≃* H₀ := MulEquiv.subgroupCongr hmap
  have hnat := abelianization_transfer_natural_of_surjective
    f hf H hker
  dsimp only at hnat
  have htransferCast :
      c.abelianizationCongr.toMonoidHom.comp
          (Abelianization.lift
            (MonoidHom.transfer
              (Abelianization.of : H.map f →* Abelianization (H.map f)))) =
        Abelianization.lift
          (MonoidHom.transfer
            (Abelianization.of : H₀ →* Abelianization H₀)) := by
    exact abelianization_transfer_congr_subgroup (H.map f) H₀ hmap
  have hcomm (x : E.field.field.toSubgroup ⧸
      D.extensionInertiaWithin E.field.field L hL) :
      transferNormNaturalityIntermediateInclusion
          E.base.field E.field.field L E.below
          (D.extensionRestriction E.field.field L hL x) =
        f (D.finiteReciprocityNaturalityFrobeniusTowerMap
          E.base.field E.field.field L L
          (hL.trans E.below) hL E.below le_rfl x) := by
    refine QuotientGroup.induction_on x ?_
    intro k'
    rfl
  have htransport :
      (e₀.symm.abelianizationCongr.toMonoidHom.comp
          c.abelianizationCongr.toMonoidHom).comp
            (Abelianization.map (f.subgroupMap H)) =
        (Abelianization.map
          (D.extensionRestriction E.field.field L hL)).comp
          e.symm.abelianizationCongr.toMonoidHom := by
    apply Abelianization.hom_ext
    apply MonoidHom.ext
    intro h
    simp only [MonoidHom.comp_apply, Abelianization.map_of]
    apply congrArg Abelianization.of
    obtain ⟨x, rfl⟩ := e.surjective h
    have hex : e.symm.toMonoidHom (e x) = x := e.symm_apply_apply x
    rw [hex]
    apply e₀.injective
    calc
      e₀ (e₀.symm.toMonoidHom
          (c.toMonoidHom ((f.subgroupMap H) (e x)))) =
          c.toMonoidHom ((f.subgroupMap H) (e x)) :=
        e₀.apply_symm_apply _
      _ = e₀ (D.extensionRestriction E.field.field L hL x) := by
        apply Subtype.ext
        exact (hcomm x).symm
  unfold transferNormNaturalityTransfer DegreeData.transferNormNaturalityFrobeniusTransfer
  dsimp only
  calc
    (e₀.symm.abelianizationCongr.toMonoidHom.comp
          (Abelianization.lift
            (MonoidHom.transfer
              (Abelianization.of : H₀ →* Abelianization H₀)))).comp
        (Abelianization.map f) =
      (e₀.symm.abelianizationCongr.toMonoidHom.comp
          (c.abelianizationCongr.toMonoidHom.comp
            (Abelianization.lift
              (MonoidHom.transfer
                (Abelianization.of : H.map f →*
                  Abelianization (H.map f)))))).comp
        (Abelianization.map f) := by rw [htransferCast]
    _ = (e₀.symm.abelianizationCongr.toMonoidHom.comp
          c.abelianizationCongr.toMonoidHom).comp
        ((Abelianization.map (f.subgroupMap H)).comp
          (Abelianization.lift
            (MonoidHom.transfer
              (Abelianization.of : H →* Abelianization H)))) := by
      rw [hnat]
      simp only [MonoidHom.comp_assoc]
    _ = ((Abelianization.map
          (D.extensionRestriction E.field.field L hL)).comp
            e.symm.abelianizationCongr.toMonoidHom).comp
        (Abelianization.lift
          (MonoidHom.transfer
            (Abelianization.of : H →* Abelianization H))) := by
      rw [← MonoidHom.comp_assoc, htransport]
    _ = (Abelianization.map
          (D.extensionRestriction E.field.field L hL)).comp
        (e.symm.abelianizationCongr.toMonoidHom.comp
          (Abelianization.lift
            (MonoidHom.transfer
              (Abelianization.of : H →* Abelianization H)))) := by
      simp only [MonoidHom.comp_assoc]

/-- **Finite transfer of a positive Frobenius lift is the product of
the restrictions of the positive transfer factors** — the first
displayed transfer identity
([Yamaguchi 2026, `MainTransfer.lean:326`][Yamaguchi2026]). -/
theorem transferNormNaturalityTransfer_frobenius_product
    (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) (L : ClosedSubgroup G)
    (hL : L.toSubgroup ≤ E.field.field.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf E.base.field.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf E.field.field.toSubgroup).Normal]
    [Finite (E.base.field.toSubgroup ⧸
      L.toSubgroup.subgroupOf E.base.field.toSubgroup)]
    (σ : D.FrobeniusElements E.base L (hL.trans E.below)) :
    let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
      E L hL
    letI : H.FiniteIndex :=
      D.transferNormNaturalityFrobeniusIntermediateFiniteIndex
        E L hL
    let Ω := Quotient (orbitRel (Subgroup.zpowers σ.1)
      ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
        (hL.trans E.below)) ⧸ H))
    letI : Fintype Ω := Fintype.ofFinite _
    transferNormNaturalityTransfer E.base.field E.field.field L E.below
        (Abelianization.of
          (D.frobeniusRestriction E.base L (hL.trans E.below) σ)) =
      ∏ q : Ω, Abelianization.of
        (D.frobeniusRestriction E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q)) := by
  dsimp only
  let H := D.transferNormNaturalityFrobeniusIntermediateSubgroup
    E L hL
  letI : H.FiniteIndex :=
    D.transferNormNaturalityFrobeniusIntermediateFiniteIndex
      E L hL
  let Ω := Quotient (orbitRel (Subgroup.zpowers σ.1)
    ((E.base.field.toSubgroup ⧸ D.extensionInertiaWithin E.base.field L
      (hL.trans E.below)) ⧸ H))
  letI : Fintype Ω := Fintype.ofFinite _
  have hnat := D.transferNormNaturalityTransfer_restriction_natural
    E L hL
  have hnatσ := DFunLike.congr_fun hnat (Abelianization.of σ.1)
  have hprod := D.transferNormNaturalityFrobeniusTransfer_doubleCoset_formula
    E L hL σ.1
  calc
    transferNormNaturalityTransfer E.base.field E.field.field L E.below
        (Abelianization.of
          (D.frobeniusRestriction E.base L (hL.trans E.below) σ)) =
      Abelianization.map (D.extensionRestriction E.field.field L hL)
        (D.transferNormNaturalityFrobeniusTransfer E L hL
          (Abelianization.of σ.1)) := by
        simpa only [MonoidHom.comp_apply, Abelianization.map_of,
          DegreeData.frobeniusRestriction] using hnatσ
    _ = Abelianization.map (D.extensionRestriction E.field.field L hL)
        (∏ q : Ω, Abelianization.of
          ((D.transferNormNaturalityFrobeniusIntermediateEquiv
            E L hL).symm
              ⟨q.out.out⁻¹ * σ.1 ^ Function.minimalPeriod (σ.1 • ·) q.out *
                  q.out.out,
                QuotientGroup.out_conj_pow_minimalPeriod_mem
                  H σ.1 q.out⟩)) := by
        rw [hprod]
    _ = ∏ q : Ω, Abelianization.of
        (D.frobeniusRestriction E.field L hL
          (D.transferNormNaturalityTransferFrobeniusLift
            E L hL σ q)) := by
        rw [map_prod]
        apply Finset.prod_congr rfl
        intro q _
        rw [Abelianization.map_of]
        rfl

end DegreeData

end GroupOnly

section Representation

variable {G : Type} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The finite reciprocity homomorphism factored through the maximal
abelian quotient** — the horizontal reciprocity arrow
([Yamaguchi 2026, `MainTransfer.lean:408`][Yamaguchi2026]). -/
noncomputable def transferNormNaturalityAbelianizedReciprocity
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    Additive (Abelianization
        (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)) →+
      FiniteNormQuotient A K.field L hLK :=
  MonoidHom.toAdditiveLeft
    (Abelianization.lift
      (AddMonoidHom.toMultiplicativeRight
        (D.finiteReciprocityHom A v hAxiom K L hLK)))

/-- The abelianized reciprocity evaluates by the reciprocity
homomorphism
([Yamaguchi 2026, `MainTransfer.lean:432`][Yamaguchi2026]). -/
@[simp]
theorem transferNormNaturalityAbelianizedReciprocity_of
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (q : K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) :
    D.transferNormNaturalityAbelianizedReciprocity A v hAxiom K L hLK
        (Additive.ofMul (Abelianization.of q)) =
      D.finiteReciprocityHom A v hAxiom K L hLK (Additive.ofMul q) := by
  exact Abelianization.lift_apply_of
    (AddMonoidHom.toMultiplicativeRight
      (D.finiteReciprocityHom A v hAxiom K L hLK)) q

end DegreeData

end Representation

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The double-coset transfer formula**, indexed by
`⟨σ⟩\\G(L|K)/G(L|K')` as the orbit quotient of `zpowers σ` on the
left-coset space
([Yamaguchi 2026, `MainTransfer.lean:461`][Yamaguchi2026]). -/
theorem transferNormNaturality_transfer_doubleCoset_formula
    (K K' L : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [Finite (K.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.toSubgroup)]
    (σ : K.toSubgroup ⧸
      L.toSubgroup.subgroupOf K.toSubgroup) :
    letI : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hK'K
    let H := transferNormNaturalityIntermediateSubgroup K K' L hK'K
    letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite
    letI : Fintype (Quotient (orbitRel (Subgroup.zpowers σ)
        ((K.toSubgroup ⧸
          L.toSubgroup.subgroupOf K.toSubgroup) ⧸ H))) :=
      Fintype.ofFinite _
    transferNormNaturalityTransfer K K' L hK'K (Abelianization.of σ) =
      ∏ q : Quotient (orbitRel (Subgroup.zpowers σ)
          ((K.toSubgroup ⧸
            L.toSubgroup.subgroupOf K.toSubgroup) ⧸ H)),
        Abelianization.of
          ((transferNormNaturalityIntermediateQuotientEquiv K K' L hK'K).symm
            ⟨q.out.out⁻¹ * σ ^ Function.minimalPeriod (σ • ·) q.out *
                q.out.out,
              QuotientGroup.out_conj_pow_minimalPeriod_mem H σ q.out⟩) := by
  letI hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hK'K
  dsimp only
  let H := transferNormNaturalityIntermediateSubgroup K K' L hK'K
  letI : H.FiniteIndex := Subgroup.finiteIndex_of_finite
  letI := Fintype.ofFinite
    (Quotient (orbitRel (Subgroup.zpowers σ)
      ((K.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.toSubgroup) ⧸ H)))
  rw [transferNormNaturalityTransfer]
  simp only [MonoidHom.comp_apply, Abelianization.lift_apply_of]
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro q _
  exact abelianizationCongr_of
    (transferNormNaturalityIntermediateQuotientEquiv K K' L hK'K).symm _

end GroupOnly

section Representation

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The invariant carrier of `extensionFixedRepresentation` is
canonically the ambient fixed subgroup `A_L`**
([Yamaguchi 2026, `MainTransfer.lean:514`][Yamaguchi2026]). -/
def transferNormNaturalityExtensionFixedEquiv
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    (extensionFixedRepresentation A K L hLK hnormal).V ≃+
      ambientFixedAddSubgroup A L where
  toFun a := ⟨a.1, by
    intro l
    let s : L.toSubgroup.subgroupOf K.toSubgroup :=
      ⟨Subgroup.inclusion hLK l, l.2⟩
    exact a.2 s⟩
  invFun a := ⟨a.1, by
    rintro ⟨k, hk⟩
    exact a.2 ⟨k.1, hk⟩⟩
  left_inv _ := by rfl
  right_inv _ := by rfl
  map_add' _ _ := rfl

/-- The carrier identification is the identity on ambient values
([Yamaguchi 2026, `MainTransfer.lean:537`][Yamaguchi2026]). -/
@[simp]
theorem transferNormNaturalityExtensionFixedEquiv_apply_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) :
    ((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal a :
      ambientFixedAddSubgroup A L) : A.V) = a.1 :=
  rfl

/-- The inverse identification is the identity on ambient values
([Yamaguchi 2026, `MainTransfer.lean:551`][Yamaguchi2026]). -/
@[simp]
theorem transferNormNaturalityExtensionFixedEquiv_symm_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (a : ambientFixedAddSubgroup A L) :
    ((transferNormNaturalityExtensionFixedEquiv A K L hLK hnormal).symm a).1 =
      a.1 :=
  rfl

end Representation

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A fixed choice of right-coset representatives for the intermediate
subgroup ([Yamaguchi 2026, `MainTransfer.lean:568`][Yamaguchi2026]). -/
noncomputable def chosenTransferNormNaturalityRightTransversal
    (K K' L : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (transferNormNaturalityIntermediateSubgroup K K' L hK'K).RightTransversal :=
  ⟨Set.range Quotient.out, Subgroup.isComplement_range_right Quotient.out_eq'⟩

/-- Multiplication as the right-coset decomposition `G(L|K') × T ≃ G(L|K)`
([Yamaguchi 2026, `MainTransfer.lean:579`][Yamaguchi2026]). -/
noncomputable def transferNormNaturalityRightCosetProductEquiv
    (K K' L : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) ×
        (chosenTransferNormNaturalityRightTransversal K K' L hK'K :
          Set (K.toSubgroup ⧸
            L.toSubgroup.subgroupOf K.toSubgroup)) ≃
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
  (Equiv.prodCongr
      (transferNormNaturalityIntermediateQuotientEquiv K K' L hK'K).toEquiv
      (Equiv.refl _)).trans
    (chosenTransferNormNaturalityRightTransversal K K' L hK'K).2.equiv.symm

/-- The decomposition evaluates by inclusion and multiplication
([Yamaguchi 2026, `MainTransfer.lean:596`][Yamaguchi2026]). -/
@[simp]
theorem transferNormNaturalityRightCosetProductEquiv_apply
    (K K' L : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    (r : K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup)
    (t : (chosenTransferNormNaturalityRightTransversal K K' L hK'K :
      Set (K.toSubgroup ⧸
        L.toSubgroup.subgroupOf K.toSubgroup))) :
    transferNormNaturalityRightCosetProductEquiv K K' L hK'K (r, t) =
      transferNormNaturalityIntermediateInclusion K K' L hK'K r * t.1 :=
  rfl

end GroupOnly

end

end Atlas.Knowledge
