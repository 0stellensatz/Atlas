import Mathlib
import Atlas.Knowledge.ClassFieldAxiom
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteCyclicSubextension
import Atlas.Knowledge.FiniteExtensionTransitivity
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityHom
import Atlas.Knowledge.FiniteReciprocityNaturalityNorm
import Atlas.Knowledge.IntermediateGaloisCorrespondence
import Atlas.Knowledge.IntermediateGaloisTransfer
import Atlas.Knowledge.ReciprocityExactRows
import Atlas.Knowledge.ReductionDiagramChases
import Atlas.Knowledge.ReductionGaloisArrows
import Atlas.Knowledge.SylowReductionStep
import Atlas.Knowledge.TotallyRamifiedReciprocity
import Atlas.Knowledge.TransferNormFrobeniusGeometry
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.UnramifiedReciprocityEquiv
import Atlas.Knowledge.ValuationData

/-!
# abstract reciprocity theorem

The three reductions assembled: the reciprocity homomorphism of the
finite reciprocity equivalence is bijective for every cyclic finite
Galois extension (splitting into maximal unramified and totally
ramified parts), surjective for every finite Galois extension (the
degree induction through solvable groups and the Sylow step), injective
for every abelian one (the jointly faithful cyclic coordinates), and
its factor through the maximal abelian quotient is bijective — the
abstract reciprocity theorem (#104).

## Main statements

* `ValuationData.abstractReciprocity_cyclic_finiteReciprocityHom_bijective`
  — the third reduction's endpoint; proved.
* `ValuationData.abstractReciprocity_finiteReciprocityHom_surjective` —
  surjectivity for every finite Galois extension; proved.
* `ValuationData.abstractReciprocity_abelian_finiteReciprocityHom_injective`
  — injectivity for abelian extensions; proved.
* `ValuationData.abstractReciprocity_abelianizedReciprocity_bijective`
  — the abelianized reciprocity map is bijective; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling —
under which the source's `simpa only using L.normal` and
`simpa only using L.finite` proof-term adjustments close by the field
itself — `extensionSubgroup_over_intermediate_normal` is the layer's
`subgroupOf_over_intermediate_normal`,
`FiniteGaloisSubextension.finite_extension_trans` is the top-level
`finite_extension_trans`, `degree.property` is the layer's
`degree.pos`, and the calls to the layer's slimmed
`transferNormNaturality_intermediateExtension_normal K M L hMK` shed
the source's `hLM`. The Sylow step's eight-argument restriction call
takes the layer's six-argument form. The ambient group sits in one
`{G : Type}` scope: everything consumes the Type-pinned
`Atlas.Knowledge.DegreeData.finiteReciprocityHom`. The seven
hypothesis-bearing declarations shed the source's `[T2Space G]` (the
continuing cascade) and keep `[TotallyDisconnectedSpace G]` where the
totally ramified chain consumes it. The eight privates stay private
with the source's scopes; the solvable induction keeps the source's
`termination_by`/`decreasing_by` on the quotient's cardinality; one
rewrite pair in the abelianized bijectivity pins its arguments
explicitly where the anonymous form left a linted side goal. The file
is the source's `Reciprocity/Main.lean` through its `ValuationData`
section (`:28`–`:845`); the `abstractReciprocityEquiv` and
norm-residue-symbol tail and the naturality section are the next
bricks.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G]

/- Additive exactness of the finite Galois row attached to an
intermediate Galois field ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:28`][Yamaguchi2026]). -/
private theorem abstractReciprocity_galois_functionExact
    (K M L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hLnormal :
      (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hMnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K M L hMK
    Function.Exact
      (MonoidHom.toAdditive (abstractReciprocityInclusion K M L hLM hMK))
      (MonoidHom.toAdditive
        (abstractReciprocityRestriction K M L hLM hMK)) := by
  letI : (L.toSubgroup.subgroupOf M.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K M L hMK
  intro q
  constructor
  · intro hq
    have hmul : abstractReciprocityRestriction K M L hLM hMK q.toMul = 1 := by
      exact Additive.ofMul.injective (by simpa using hq)
    have hmem : q.toMul ∈
        (abstractReciprocityRestriction K M L hLM hMK).ker := hmul
    rw [abstractReciprocity_galois_exact K M L hLM hMK] at hmem
    obtain ⟨x, hx⟩ := hmem
    refine ⟨Additive.ofMul x, ?_⟩
    exact Additive.toMul.injective hx
  · rintro ⟨x, rfl⟩
    have hmem : abstractReciprocityInclusion K M L hLM hMK x.toMul ∈
        (abstractReciprocityInclusion K M L hLM hMK).range :=
      ⟨x.toMul, rfl⟩
    rw [← abstractReciprocity_galois_exact K M L hLM hMK] at hmem
    exact Additive.ofMul.injective (by simpa using hmem)

/- A proper subgroup of a finite group has strictly smaller cardinality
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:61`][Yamaguchi2026]). -/
private theorem abstractReciprocity_subgroup_card_lt_of_ne_top
    {Q : Type*} [Group Q] [Finite Q] (S : Subgroup Q) (hS : S ≠ ⊤) :
    Nat.card S < Nat.card Q := by
  letI := Fintype.ofFinite Q
  letI := Fintype.ofFinite S
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_lt_of_injective_not_surjective
      S.subtype S.subtype_injective (by
        intro hsurj
        apply hS
        rw [eq_top_iff]
        intro q _
        obtain ⟨s, hs⟩ := hsurj q
        rw [← hs]
        exact s.property))

/- Quotienting a finite group by a nontrivial normal subgroup strictly
decreases its cardinality ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:79`][Yamaguchi2026]). -/
private theorem abstractReciprocity_quotient_card_lt_of_ne_bot
    {Q : Type*} [Group Q] [Finite Q] (S : Subgroup Q) [S.Normal]
    (hS : S ≠ ⊥) :
    Nat.card (Q ⧸ S) < Nat.card Q := by
  letI := Fintype.ofFinite Q
  letI := Fintype.ofFinite (Q ⧸ S)
  simpa only [Nat.card_eq_fintype_card] using
    (Fintype.card_lt_of_surjective_not_injective
      (QuotientGroup.mk' S) (QuotientGroup.mk'_surjective S) (by
        intro hinj
        apply hS
        rw [← QuotientGroup.ker_mk' S]
        exact (MonoidHom.ker_eq_bot_iff (QuotientGroup.mk' S)).2 hinj))

/- A subgroup of a finite commutative group which contains every Sylow
subgroup is the whole group ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:95`][Yamaguchi2026]). -/
private theorem abstractReciprocity_subgroup_eq_top_of_sylow_le
    {B : Type*} [CommGroup B] [Finite B]
    (H : Subgroup B)
    (hSylow : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p B),
      (P : Subgroup B) ≤ H) :
    H = ⊤ := by
  classical
  apply (Subgroup.index_eq_one (H := H)).1
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpdvd
  letI : Fact p.Prime := ⟨hp⟩
  letI : H.Normal := H.normal_of_isMulCommutative
  let quotientMap : B →* B ⧸ H := QuotientGroup.mk' H
  have hquotientMap : Function.Surjective quotientMap :=
    QuotientGroup.mk'_surjective H
  let Q : Sylow p (B ⧸ H) := default
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective
    hquotientMap p Q
  have hmapBot : (P : Subgroup B).map quotientMap = ⊥ := by
    exact (Subgroup.map_eq_bot_iff (P : Subgroup B)).2 (by
      simpa [quotientMap, QuotientGroup.ker_mk'] using hSylow P)
  have hQBot : (Q : Subgroup (B ⧸ H)) = ⊥ := by
    have hco := congrArg (fun S : Sylow p (B ⧸ H) =>
      (S : Subgroup (B ⧸ H))) hP
    simpa [hmapBot] using hco.symm
  exact (Q.ne_bot_of_dvd_card hpdvd) hQBot

/- If a commutative group has finite exponent and an additive subgroup
contains every Sylow subgroup, then it is the whole group; only the
finite cyclic subgroup generated by the element under consideration is
made finite — no finiteness of the ambient group is assumed
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:126`][Yamaguchi2026]). -/
private theorem abstractReciprocity_addSubgroup_eq_top_of_exponent_and_sylow_le
    {B : Type*} [AddCommGroup B]
    (d : ℕ) (hd : 0 < d) (hexponent : ∀ b : B, d • b = 0)
    (H : AddSubgroup B)
    (hSylow : ∀ {p : ℕ} [Fact p.Prime]
      (P : Sylow p (Multiplicative B)),
      Subgroup.toAddSubgroup'
        (P : Subgroup (Multiplicative B)) ≤ H) :
    H = ⊤ := by
  apply AddSubgroup.toSubgroup.injective
  apply top_unique
  intro g _
  let b : B := g.toAdd
  have hgfinite : IsOfFinOrder g :=
    isOfFinOrder_iff_pow_eq_one.2 ⟨d, hd, by
      apply Multiplicative.toAdd.injective
      simpa [b] using hexponent b⟩
  let C := Subgroup.zpowers g
  letI : Fintype C :=
    Fintype.ofEquiv (Fin (orderOf g)) (finEquivZPowers hgfinite)
  let J : Subgroup C := H.toSubgroup.comap C.subtype
  have hJ : J = ⊤ := by
    apply abstractReciprocity_subgroup_eq_top_of_sylow_le J
    intro p _ Q x hx
    have hQp : IsPGroup p ((Q : Subgroup C).map C.subtype) :=
      Q.isPGroup'.map C.subtype
    obtain ⟨P, hQP⟩ := hQp.exists_le_sylow
    have hxmap : (x : Multiplicative B) ∈
        (Q : Subgroup C).map C.subtype :=
      ⟨x, hx, rfl⟩
    exact hSylow P (hQP hxmap)
  let x : C := ⟨g, Subgroup.mem_zpowers g⟩
  have hxJ : x ∈ J := by rw [hJ]; exact Subgroup.mem_top x
  exact hxJ

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/- The common reciprocity square used by the cyclic and
intermediate-field reductions ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:167`][Yamaguchi2026]). -/
private theorem abstractReciprocity_finiteReciprocityHom_diagram
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K M : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLM : L.toSubgroup ≤ M.field.toSubgroup)
    (hMK : M.field.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    [hMnormal : (M.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hMfinite : Finite
      (K.field.toSubgroup ⧸
        M.field.toSubgroup.subgroupOf K.field.toSubgroup)]
    [hLMnormal : (L.toSubgroup.subgroupOf M.field.toSubgroup).Normal]
    [hLMfinite : Finite
      (M.field.toSubgroup ⧸
        L.toSubgroup.subgroupOf M.field.toSubgroup)] :
    let r₀ := D.finiteReciprocityHom A v hAxiom M L hLM
    let r := D.finiteReciprocityHom A v hAxiom K L (hLM.trans hMK)
    let r₁ := D.finiteReciprocityHom A v hAxiom K M.field hMK
    let i := MonoidHom.toAdditive
      (abstractReciprocityInclusion K.field M.field L hLM hMK)
    let q := MonoidHom.toAdditive
      (abstractReciprocityRestriction K.field M.field L hLM hMK)
    let n := abstractReciprocityNormMap A K.field M.field L hLM hMK
    let p := abstractReciprocityNormProjection A K.field M.field L hLM hMK
    Function.Surjective q ∧
      (∀ x, r (i x) = n (r₀ x)) ∧
      (∀ x, p (r x) = r₁ (q x)) := by
  dsimp only
  let EMK : FiniteAbstractFieldExtension G :=
    { field := M
      base := K
      below := hMK
      finiteQuotient := hMfinite }
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  let r₀ := D.finiteReciprocityHom A v hAxiom M L hLM
  let r := D.finiteReciprocityHom A v hAxiom K L (hLM.trans hMK)
  let r₁ := D.finiteReciprocityHom A v hAxiom K M.field hMK
  let i := MonoidHom.toAdditive
    (abstractReciprocityInclusion K.field M.field L hLM hMK)
  let q := MonoidHom.toAdditive
    (abstractReciprocityRestriction K.field M.field L hLM hMK)
  let n := abstractReciprocityNormMap A K.field M.field L hLM hMK
  let p := abstractReciprocityNormProjection A K.field M.field L hLM hMK
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨x, hx⟩ := abstractReciprocityRestriction_surjective
      K.field M.field L hLM hMK y.toMul
    refine ⟨Additive.ofMul x, ?_⟩
    exact Additive.toMul.injective hx
  have hleft : ∀ x, r (i x) = n (r₀ x) := by
    intro x
    have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EMK L L (hLM.trans hMK) hLM le_rfl
    simpa only [r, r₀, n, i, abstractReciprocityNormMap,
      abstractReciprocityInclusion,
      transferNormNaturalityIntermediateInclusion,
      AddMonoidHom.comp_apply] using
        (congrArg (fun f => f x) hcomm).symm
  have hright : ∀ x, p (r x) = r₁ (q x) := by
    intro x
    have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EKK M.field L hMK (hLM.trans hMK) hLM
    rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection,
      finiteReciprocityNaturalityRestriction_sameBase_eq_restriction]
      at hcomm
    simpa only [r, r₁, p, q, AddMonoidHom.comp_apply] using
      congrArg (fun f => f x) hcomm
  exact ⟨hq, hleft, hright⟩

/-- **The third reduction: the reciprocity homomorphism is bijective for
every cyclic finite Galois extension**, by splitting it into its maximal
unramified and totally ramified parts ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:243`][Yamaguchi2026]). -/
theorem abstractReciprocity_cyclic_finiteReciprocityHom_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    [hCyclic : IsCyclic L.extensionQuotient] :
    letI : Finite
        (K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
    Function.Bijective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
  let S := L.inertiaImage D
  let M := L.maximalUnramifiedSubextension D
  let hLM : L.field.toSubgroup ≤ M.toSubgroup :=
    L.field_le_intermediateField S
  let hMK : M.toSubgroup ≤ K.field.toSubgroup :=
    L.intermediateField_le_base S
  letI hLnormal :
      (L.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    L.normal
  letI hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    L.finite
  letI hMnormal : (M.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    L.intermediateField_normal S inferInstance
  letI hMfinite : Finite
      (K.field.toSubgroup ⧸ M.toSubgroup.subgroupOf K.field.toSubgroup) :=
    L.intermediateField_finite S
  letI hLMnormal : (L.field.toSubgroup.subgroupOf M.toSubgroup).Normal :=
    L.subgroupOf_over_intermediate_normal S
  letI hLMfinite : Finite
      (M.toSubgroup ⧸ L.field.toSubgroup.subgroupOf M.toSubgroup) :=
    L.extension_over_intermediate_finite S
  letI hMabsolute : Finite ((baseField G).toSubgroup ⧸
      M.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    finite_extension_trans hMK (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
  letI hLowerCyclic : IsCyclic
      (M.toSubgroup ⧸ L.field.toSubgroup.subgroupOf M.toSubgroup) :=
    L.lowerQuotient_isCyclic S
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator
    (α := M.toSubgroup ⧸ L.field.toSubgroup.subgroupOf M.toSubgroup)
  let Ecyc : FiniteCyclicSubextension MF :=
    { field := L.field
      below := hLM
      normal := hLMnormal
      finite := hLMfinite
      generator := g
      generates := hg }
  let r₀ := D.finiteReciprocityHom A v hAxiom MF L.field hLM
  let r := D.finiteReciprocityHom A v hAxiom K L.field (hLM.trans hMK)
  let r₁ := D.finiteReciprocityHom A v hAxiom K M hMK
  have hr₀ : Function.Bijective r₀ :=
    v.abstractReciprocity_cyclicTotallyRamified_finiteReciprocityHom_bijective
      hcf hAxiom MF Ecyc
        (L.maximalUnramifiedSubextension_isTotallyRamified D)
  have hr₁ : Function.Bijective r₁ :=
    (v.unramifiedReciprocityEquiv hAxiom K M hMK
      (L.maximalUnramifiedSubextension_isUnramified D)).bijective
  obtain ⟨hpQ, hleft, hright⟩ :=
    abstractReciprocity_finiteReciprocityHom_diagram
      v hAxiom K MF L.field hLM hMK
  exact abstractReciprocity_bijective_of_exact_diagram
    (MonoidHom.toAdditive
      (abstractReciprocityInclusion K.field M L.field hLM hMK))
    (MonoidHom.toAdditive
      (abstractReciprocityRestriction K.field M L.field hLM hMK))
    (abstractReciprocityNormMap A K.field M L.field hLM hMK)
    (abstractReciprocityNormProjection A K.field M L.field hLM hMK)
    r₀ r r₁
    (abstractReciprocity_galois_functionExact K.field M L.field hLM hMK)
    (abstractReciprocity_normQuotient_exact A K.field M L.field hLM hMK)
    hpQ (L.maximalUnramified_normMap_injective A hcf D)
    hleft hright hr₀ hr₁

/- Surjectivity ascends through a normal intermediate field — the
diagram chase used in the degree induction of the first reduction
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:325`][Yamaguchi2026]). -/
private theorem abstractReciprocity_finiteReciprocityHom_surjective_of_intermediate
    (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    (S : Subgroup L.extensionQuotient) [hSnormal : S.Normal] :
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    let hMK := L.intermediateField_le_base S
    letI : (M.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
      L.intermediateField_normal S hSnormal
    letI : Finite
        (K.field.toSubgroup ⧸
          M.toSubgroup.subgroupOf K.field.toSubgroup) :=
      L.intermediateField_finite S
    letI : (L.field.toSubgroup.subgroupOf M.toSubgroup).Normal :=
      L.subgroupOf_over_intermediate_normal S
    letI : Finite
        (M.toSubgroup ⧸ L.field.toSubgroup.subgroupOf M.toSubgroup) :=
      L.extension_over_intermediate_finite S
    letI : Finite ((baseField G).toSubgroup ⧸
        M.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
      finite_extension_trans hMK (le_baseField K.field)
    let MF : FiniteAbstractField G := ⟨M, inferInstance⟩
    Function.Surjective
        (D.finiteReciprocityHom A v hAxiom MF L.field hLM) →
      Function.Surjective
        (D.finiteReciprocityHom A v hAxiom K M hMK) →
      letI : Finite
          (K.field.toSubgroup ⧸
            L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
      Function.Surjective
        (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  dsimp only
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  letI hLnormal :
      (L.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    L.normal
  letI hLfinite : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) :=
    L.finite
  letI hMnormal : (M.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    L.intermediateField_normal S hSnormal
  letI hMfinite : Finite
      (K.field.toSubgroup ⧸ M.toSubgroup.subgroupOf K.field.toSubgroup) :=
    L.intermediateField_finite S
  letI hLMnormal : (L.field.toSubgroup.subgroupOf M.toSubgroup).Normal :=
    L.subgroupOf_over_intermediate_normal S
  letI hLMfinite : Finite
      (M.toSubgroup ⧸ L.field.toSubgroup.subgroupOf M.toSubgroup) :=
    L.extension_over_intermediate_finite S
  letI hMabsolute : Finite ((baseField G).toSubgroup ⧸
      M.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    finite_extension_trans hMK (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
  intro hr₀ hr₁
  let r₀ := D.finiteReciprocityHom A v hAxiom MF L.field hLM
  let r := D.finiteReciprocityHom A v hAxiom K L.field (hLM.trans hMK)
  let r₁ := D.finiteReciprocityHom A v hAxiom K M hMK
  obtain ⟨hpQ, hleft, hright⟩ :=
    abstractReciprocity_finiteReciprocityHom_diagram
      v hAxiom K MF L.field hLM hMK
  exact abstractReciprocity_surjective_of_exact_diagram
    (MonoidHom.toAdditive
      (abstractReciprocityInclusion K.field M L.field hLM hMK))
    (MonoidHom.toAdditive
      (abstractReciprocityRestriction K.field M L.field hLM hMK))
    (abstractReciprocityNormMap A K.field M L.field hLM hMK)
    (abstractReciprocityNormProjection A K.field M L.field hLM hMK)
    r₀ r r₁
    (abstractReciprocity_normQuotient_exact A K.field M L.field hLM hMK)
    hpQ hleft hright hr₀ hr₁

/- The degree induction in the first reduction for solvable Galois
groups: in the abelian noncyclic case one cuts out one of the faithful
cyclic coordinates, in the nonabelian case the commutator subgroup
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:408`][Yamaguchi2026]). -/
private theorem abstractReciprocity_solvable_finiteReciprocityHom_surjective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    [hsolvable : IsSolvable L.extensionQuotient] :
    letI : Finite
        (K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
    Function.Surjective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  classical
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
  let Q := L.extensionQuotient
  by_cases hcyclic : IsCyclic Q
  · letI : IsCyclic Q := hcyclic
    exact (v.abstractReciprocity_cyclic_finiteReciprocityHom_bijective
      hcf hAxiom K L).2
  have hQnotSubsingleton : ¬ Subsingleton Q := by
    intro hQ
    letI : Subsingleton Q := hQ
    exact hcyclic inferInstance
  letI hQnontrivial : Nontrivial Q :=
    not_subsingleton_iff_nontrivial.mp hQnotSubsingleton
  by_cases hcommutative : IsMulCommutative Q
  · letI : IsMulCommutative Q := hcommutative
    obtain ⟨I, hIfinite, _, _, f, _, hfaithful, hfactorCyclic,
        _⟩ := L.exists_cyclicIntermediateFields
    letI : Fintype I := hIfinite
    obtain ⟨q, hq⟩ := exists_ne (1 : Q)
    have hnotAll : ¬ ∀ i, f i q = 1 := by
      intro hall
      have hmem : q ∈ ⨅ i, MonoidHom.ker (f i) := by
        rw [Subgroup.mem_iInf]
        intro i
        exact (MonoidHom.mem_ker).2 (hall i)
      rw [hfaithful, Subgroup.mem_bot] at hmem
      exact hq hmem
    push Not at hnotAll
    obtain ⟨i, hi⟩ := hnotAll
    let S := MonoidHom.ker (f i)
    letI hSnormal : S.Normal := inferInstance
    have hSneTop : S ≠ ⊤ := by
      intro htop
      have hmem : q ∈ S := by rw [htop]; trivial
      exact hi ((MonoidHom.mem_ker).1 hmem)
    let M := L.intermediateField S
    let N := L.lowerFiniteGalois S
    let U := L.intermediateFiniteGalois S hSnormal
    letI hMabsolute : Finite ((baseField G).toSubgroup ⧸
        M.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
      finite_extension_trans
        (L.intermediateField_le_base S) (le_baseField K.field)
    let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
    letI hNsolvable : IsSolvable N.extensionQuotient :=
      solvable_of_solvable_injective
        (f := (L.lowerQuotientEquiv S).toMonoidHom)
        (L.lowerQuotientEquiv S).injective
    letI hUcyclic : IsCyclic U.extensionQuotient := hfactorCyclic i
    letI : Finite
        (MF.field.toSubgroup ⧸
          N.field.toSubgroup.subgroupOf MF.field.toSubgroup) := N.finite
    letI : Finite
        (K.field.toSubgroup ⧸
          U.field.toSubgroup.subgroupOf K.field.toSubgroup) := U.finite
    have hNcard : Nat.card N.extensionQuotient < Nat.card Q := by
      calc
        Nat.card N.extensionQuotient = Nat.card S :=
          Nat.card_congr (L.lowerQuotientEquiv S).toEquiv
        _ < Nat.card Q :=
          abstractReciprocity_subgroup_card_lt_of_ne_top S hSneTop
    have hrN : Function.Surjective
        (D.finiteReciprocityHom A v hAxiom MF N.field N.below) :=
      abstractReciprocity_solvable_finiteReciprocityHom_surjective
        v hcf hAxiom MF N
    have hrU : Function.Surjective
        (D.finiteReciprocityHom A v hAxiom K U.field U.below) :=
      (v.abstractReciprocity_cyclic_finiteReciprocityHom_bijective
        hcf hAxiom K U).2
    exact abstractReciprocity_finiteReciprocityHom_surjective_of_intermediate
      v hAxiom K L S hrN hrU
  · let S := commutator Q
    letI hSnormal : S.Normal := inferInstance
    have hSneBot : S ≠ ⊥ := by
      intro hbot
      apply hcommutative
      have hcenter : Subgroup.center Q = ⊤ :=
        (commutator_eq_bot_iff_center_eq_top Q).1 hbot
      let hcommGroup : CommGroup Q :=
        Group.commGroupOfCenterEqTop hcenter
      exact ⟨⟨fun x y => hcommGroup.mul_comm x y⟩⟩
    have hSlt : S < ⊤ :=
      IsSolvable.commutator_lt_top_of_nontrivial Q
    let M := L.intermediateField S
    let N := L.lowerFiniteGalois S
    let U := L.intermediateFiniteGalois S hSnormal
    letI hMfinite : Finite
        (K.field.toSubgroup ⧸ M.toSubgroup.subgroupOf K.field.toSubgroup) :=
      L.intermediateField_finite S
    letI hMabsolute : Finite ((baseField G).toSubgroup ⧸
        M.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
      finite_extension_trans
        (L.intermediateField_le_base S) (le_baseField K.field)
    let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
    letI hNsolvable : IsSolvable N.extensionQuotient :=
      solvable_of_solvable_injective
        (f := (L.lowerQuotientEquiv S).toMonoidHom)
        (L.lowerQuotientEquiv S).injective
    letI hUpperSolvable : IsSolvable (L.upperQuotient S) := by
      change IsSolvable (Q ⧸ S)
      infer_instance
    letI hUsolvable : IsSolvable U.extensionQuotient :=
      solvable_of_solvable_injective
        (f := (L.upperQuotientEquiv S).symm.toMonoidHom)
        (L.upperQuotientEquiv S).symm.injective
    letI : Finite
        (MF.field.toSubgroup ⧸
          N.field.toSubgroup.subgroupOf MF.field.toSubgroup) := N.finite
    letI : Finite
        (K.field.toSubgroup ⧸
          U.field.toSubgroup.subgroupOf K.field.toSubgroup) := U.finite
    have hNcard : Nat.card N.extensionQuotient < Nat.card Q := by
      calc
        Nat.card N.extensionQuotient = Nat.card S :=
          Nat.card_congr (L.lowerQuotientEquiv S).toEquiv
        _ < Nat.card Q :=
          abstractReciprocity_subgroup_card_lt_of_ne_top S hSlt.ne
    have hUcard : Nat.card U.extensionQuotient < Nat.card Q := by
      calc
        Nat.card U.extensionQuotient = Nat.card (Q ⧸ S) :=
          Nat.card_congr (L.upperQuotientEquiv S).symm.toEquiv
        _ < Nat.card Q :=
          abstractReciprocity_quotient_card_lt_of_ne_bot S hSneBot
    have hrN : Function.Surjective
        (D.finiteReciprocityHom A v hAxiom MF N.field N.below) :=
      abstractReciprocity_solvable_finiteReciprocityHom_surjective
        v hcf hAxiom MF N
    have hrU : Function.Surjective
        (D.finiteReciprocityHom A v hAxiom K U.field U.below) :=
      abstractReciprocity_solvable_finiteReciprocityHom_surjective
        v hcf hAxiom K U
    exact abstractReciprocity_finiteReciprocityHom_surjective_of_intermediate
      v hAxiom K L S hrN hrU
termination_by Nat.card L.extensionQuotient
decreasing_by all_goals assumption

/-- **The Sylow step in the first reduction: the reciprocity
homomorphism is surjective for every finite Galois extension.** The
norm quotient need not be known finite here: the unramified cohomology
consequence kills every element by the extension degree, so the Sylow
argument is performed inside the finite cyclic subgroup generated by
that element ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:562`][Yamaguchi2026]). -/
theorem abstractReciprocity_finiteReciprocityHom_surjective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
    Function.Surjective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  classical
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
  let r := D.finiteReciprocityHom A v hAxiom K L.field L.below
  apply (AddMonoidHom.range_eq_top (f := r)).1
  have hdegreePos : 0 < (L.toFiniteAbstractExtension.degree : ℕ) :=
    L.toFiniteAbstractExtension.degree.pos
  apply abstractReciprocity_addSubgroup_eq_top_of_exponent_and_sylow_le
    (L.toFiniteAbstractExtension.degree : ℕ) hdegreePos
    (finiteNormQuotient_degree_nsmul_eq_zero
      A L.toFiniteAbstractExtension) r.range
  intro p _ Ptarget x hx
  let Psource : Sylow p L.extensionQuotient := default
  let S : Subgroup L.extensionQuotient :=
    (Psource : Subgroup L.extensionQuotient)
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  let N := L.lowerFiniteGalois S
  letI hMfinite : Finite
      (K.field.toSubgroup ⧸ M.toSubgroup.subgroupOf K.field.toSubgroup) :=
    L.intermediateField_finite S
  letI hLMnormal : (L.field.toSubgroup.subgroupOf M.toSubgroup).Normal :=
    L.subgroupOf_over_intermediate_normal S
  letI hLMfinite : Finite
      (M.toSubgroup ⧸ L.field.toSubgroup.subgroupOf M.toSubgroup) :=
    L.extension_over_intermediate_finite S
  letI hMabsolute : Finite ((baseField G).toSubgroup ⧸
      M.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
    finite_extension_trans hMK (le_baseField K.field)
  let MF : FiniteAbstractField G := ⟨M, hMabsolute⟩
  let EMK : FiniteAbstractFieldExtension G :=
    { field := MF
      base := K
      below := hMK
      finiteQuotient := hMfinite }
  letI hNsolvable : IsSolvable N.extensionQuotient :=
    L.abstractReciprocity_sylow_lowerQuotient_isSolvable Psource
  let rLower := D.finiteReciprocityHom A v hAxiom MF L.field hLM
  have hrLower : Function.Surjective rLower :=
    abstractReciprocity_solvable_finiteReciprocityHom_surjective
      v hcf hAxiom MF N
  have hxNsmul :=
    L.abstractReciprocity_sylowAddSubgroup_le_intermediateDegree_nsmul_range
      Psource Ptarget hx
  obtain ⟨y, hy⟩ := hxNsmul
  obtain ⟨g, hg⟩ := hrLower
    (L.intermediateNormQuotientInclusion A S y)
  refine ⟨MonoidHom.toAdditive
    (finiteReciprocityNaturalityRestriction K.field M L.field L.field
      hMK le_rfl) g, ?_⟩
  have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
    A v hAxiom EMK L.field L.field
      L.below hLM le_rfl
  calc
    r (MonoidHom.toAdditive
        (finiteReciprocityNaturalityRestriction K.field M L.field L.field
          hMK le_rfl) g) =
        finiteReciprocityNaturalityNormMap A K.field M L.field L.field
          L.below hLM hMK le_rfl (rLower g) := by
            simpa only [r, rLower, AddMonoidHom.comp_apply] using
              (congrArg (fun f => f g) hcomm).symm
    _ = L.intermediateNormMap A S (rLower g) := rfl
    _ = L.intermediateNormMap A S
          (L.intermediateNormQuotientInclusion A S y) := by rw [hg]
    _ = ((L.intermediateFiniteAbstractExtension S).degree : ℕ) • y :=
      L.intermediateNormMap_comp_inclusion A S y
    _ = x := hy

/-- **The second reduction: for an abelian Galois group, the cyclic
quotient coordinates are jointly faithful, hence the reciprocity
homomorphism is injective** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:646`][Yamaguchi2026]). -/
theorem abstractReciprocity_abelian_finiteReciprocityHom_injective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field)
    [hcommutative : IsMulCommutative L.extensionQuotient] :
    letI : Finite
        (K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
    Function.Injective
      (D.finiteReciprocityHom A v hAxiom K L.field L.below) := by
  classical
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  obtain ⟨I, hIfinite, _, _, f, _, hfaithful, hfactorCyclic,
      _⟩ := L.exists_cyclicIntermediateFields
  letI : Fintype I := hIfinite
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hrestriction (i : I) :
      L.upperRestrictionHom (MonoidHom.ker (f i)) q.toMul = 1 := by
    let S := MonoidHom.ker (f i)
    letI hSnormal : S.Normal := inferInstance
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    let hMK := L.intermediateField_le_base S
    let U := L.intermediateFiniteGalois S hSnormal
    letI hMnormal : (M.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
      L.intermediateField_normal S hSnormal
    letI hMfinite : Finite
        (K.field.toSubgroup ⧸ M.toSubgroup.subgroupOf K.field.toSubgroup) :=
      L.intermediateField_finite S
    letI hUcyclic : IsCyclic U.extensionQuotient := hfactorCyclic i
    let rFactor := D.finiteReciprocityHom A v hAxiom K M hMK
    have hrFactor : Function.Injective rFactor :=
      (v.abstractReciprocity_cyclic_finiteReciprocityHom_bijective
        hcf hAxiom K U).1
    have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EKK M L.field hMK L.below hLM
    rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection,
      finiteReciprocityNaturalityRestriction_sameBase_eq_restriction]
      at hcomm
    have hzero : rFactor (MonoidHom.toAdditive
        (abstractReciprocityRestriction K.field M L.field hLM hMK) q) =
        0 := by
      calc
        rFactor (MonoidHom.toAdditive
            (abstractReciprocityRestriction K.field M L.field hLM hMK)
              q) =
            abstractReciprocityNormProjection A K.field M L.field hLM hMK
              (D.finiteReciprocityHom A v hAxiom
                K L.field L.below q) := by
                  simpa only [rFactor, AddMonoidHom.comp_apply] using
                    (congrArg (fun h => h q) hcomm).symm
        _ = 0 := by rw [hq, map_zero]
    have hadd : MonoidHom.toAdditive
        (abstractReciprocityRestriction K.field M L.field hLM hMK) q =
        0 := by
      apply hrFactor
      simpa only [map_zero] using hzero
    have hbridge (z : L.extensionQuotient) :
        L.upperRestrictionHom S z =
          abstractReciprocityRestriction K.field M L.field hLM hMK z := by
      refine QuotientGroup.induction_on z ?_
      intro k
      rw [L.upperRestrictionHom_mk,
        abstractReciprocityRestriction_mk]
    rw [hbridge]
    exact Additive.ofMul.injective (by simpa using hadd)
  have hqone : q.toMul = 1 :=
    (L.upperRestrictionHom_jointlyFaithful f hfaithful q.toMul).1
      hrestriction
  exact Additive.toMul.injective (by simpa using hqone)

/-- **The first reduction: the factor of the finite reciprocity
equivalence through the maximal abelian quotient is bijective**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:725`][Yamaguchi2026]). -/
theorem abstractReciprocity_abelianizedReciprocity_bijective
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : FiniteGaloisSubextension K.field) :
    letI : Finite
        (K.field.toSubgroup ⧸
          L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
    Function.Bijective
      (D.transferNormNaturalityAbelianizedReciprocity
        A v hAxiom K L.field L.below) := by
  classical
  letI : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup) := L.finite
  let Q := L.extensionQuotient
  let S := commutator Q
  letI hSnormal : S.Normal := inferInstance
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  let U := L.intermediateFiniteGalois S hSnormal
  letI hMnormal : (M.toSubgroup.subgroupOf K.field.toSubgroup).Normal :=
    L.intermediateField_normal S hSnormal
  letI hMfinite : Finite
      (K.field.toSubgroup ⧸ M.toSubgroup.subgroupOf K.field.toSubgroup) :=
    L.intermediateField_finite S
  let EKK : FiniteAbstractFieldExtension G :=
    { field := K
      base := K
      below := le_rfl
      finiteQuotient := (FiniteGaloisSubextension.refl K.field).finite }
  let upperEquiv := L.upperQuotientEquiv S
  letI hUpperCommutative : IsMulCommutative (Q ⧸ S) := by
    dsimp only [S]
    exact
      (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 le_rfl
  letI hUcommutative : IsMulCommutative U.extensionQuotient :=
    ⟨⟨fun x y => by
      obtain ⟨x', rfl⟩ := upperEquiv.surjective x
      obtain ⟨y', rfl⟩ := upperEquiv.surjective y
      calc
        upperEquiv x' * upperEquiv y' =
            upperEquiv (x' * y') := (map_mul upperEquiv x' y').symm
        _ = upperEquiv (y' * x') := congrArg upperEquiv
          (Std.Commutative.comm
            (op := fun a b : Q ⧸ S => a * b) x' y')
        _ = upperEquiv y' * upperEquiv x' := map_mul upperEquiv y' x'⟩⟩
  let factor := D.transferNormNaturalityAbelianizedReciprocity
    A v hAxiom K L.field L.below
  let r := D.finiteReciprocityHom A v hAxiom K L.field L.below
  let p := abstractReciprocityNormProjection A K.field M L.field hLM hMK
  let rAb := D.finiteReciprocityHom A v hAxiom K M hMK
  have hrAb : Function.Injective rAb :=
    v.abstractReciprocity_abelian_finiteReciprocityHom_injective
      hcf hAxiom K U
  have hrestrictionEq (q : Q) :
      abstractReciprocityRestriction K.field M L.field hLM hMK q =
        L.abelianRestrictionHom q := by
    refine QuotientGroup.induction_on q ?_
    intro k
    rw [abstractReciprocityRestriction_mk]
    rfl
  have hright (q : Q) :
      p (r (Additive.ofMul q)) =
        rAb (Additive.ofMul (L.abelianRestrictionHom q)) := by
    have hcomm := D.finiteReciprocityNaturality_restriction_norm_commutes
      A v hAxiom EKK M L.field hMK L.below hLM
    rw [finiteReciprocityNaturalityNormMap_sameBase_eq_normProjection
        A K.field M L.field hLM hMK,
      finiteReciprocityNaturalityRestriction_sameBase_eq_restriction
        K.field M L.field hLM hMK]
      at hcomm
    have hq := congrArg (fun h => h (Additive.ofMul q)) hcomm
    calc
      p (r (Additive.ofMul q)) =
          rAb (Additive.ofMul
            (abstractReciprocityRestriction K.field M L.field hLM hMK
              q)) := by
        change
          p (r (Additive.ofMul q)) =
            rAb (Additive.ofMul
              (abstractReciprocityRestriction K.field M L.field hLM hMK
                q)) at hq
        exact hq
      _ = rAb (Additive.ofMul (L.abelianRestrictionHom q)) := by
        rw [hrestrictionEq]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro z hz
    change factor (Additive.ofMul z.toMul) = 0 at hz
    change Additive.ofMul z.toMul = 0
    revert hz
    refine QuotientGroup.induction_on z.toMul ?_
    intro q hz
    have hrq : r (Additive.ofMul q) = 0 := by
      calc
        r (Additive.ofMul q) =
            factor (Additive.ofMul (Abelianization.of q)) :=
          (D.transferNormNaturalityAbelianizedReciprocity_of
            A v hAxiom K L.field L.below q).symm
        _ = 0 := by
          change factor (Additive.ofMul (Abelianization.of q)) = 0 at hz
          exact hz
    have hcommutator : q ∈ commutator Q :=
      (abstractReciprocity_abelianReduction_kernel
        L p r rAb hright hrAb q).1 hrq
    have hof : Abelianization.of q = 1 :=
      (QuotientGroup.eq_one_iff q).2 hcommutator
    change Additive.ofMul (Abelianization.of q) = Additive.ofMul 1
    exact congrArg Additive.ofMul hof
  · intro b
    obtain ⟨q, hq⟩ :=
      v.abstractReciprocity_finiteReciprocityHom_surjective
        hcf hAxiom K L b
    refine ⟨Additive.ofMul (Abelianization.of q.toMul), ?_⟩
    calc
      factor (Additive.ofMul (Abelianization.of q.toMul)) =
          r (Additive.ofMul q.toMul) :=
        D.transferNormNaturalityAbelianizedReciprocity_of
          A v hAxiom K L.field L.below q.toMul
      _ = r q := by rw [ofMul_toMul]
      _ = b := hq

end ValuationData

end

end Atlas.Knowledge
