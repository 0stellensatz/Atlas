import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityNaturalityNorm
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.IntermediateGaloisTransfer
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.RelativeNormConjugation
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.TransferNormFrobeniusGeometry
import Atlas.Knowledge.TransferNormNaturality

/-!
# norm-residue naturality arrows

Reciprocity naturality states three diagrams for the norm-residue
symbol, and before inverting reciprocity their vertical arrows are
exactly the maps already constructed in norm–conjugation and
transfer–norm naturality: restriction with the relative norm,
conjugation on both sides, and transfer with inclusion of fixed
elements. This item applies abelianization to the Galois arrows and
combines each pair of vertical arrows into one additive homomorphism
between the products, with the formulas on quotient representatives
proved from the actual maps (#104).

## Main definitions

* `normResidueNaturalityAbelianizedRestriction` — the abelianized
  restriction arrow of the norm/restriction diagram.
* `normResidueNaturalityAbelianizedConjugation` — the abelianized
  conjugation arrow of the conjugation diagram.
* `normResidueNaturalityNormRestrictionPairMap` — the assembled
  vertical arrows of the norm/restriction diagram.
* `normResidueNaturalityConjugationPairMap` — the assembled vertical
  arrows of the conjugation diagram.
* `normResidueNaturalityTransferInclusionPairMap` — the assembled
  upward arrows of the inclusion/transfer diagram.

## Implementation notes

The relative subgroups are the layer's `Subgroup.subgroupOf` spelling,
and the `≤`-hypotheses the source binds only to spell its
`extensionSubgroup` arguments disappear with that spelling — the
abelianized restriction drops the source's `hLK` and `hL'K'`, and the
conjugation arrows drop `hLK`, each matching the layer signature of the
map it wraps. One `{G : Type u}` scope holds everything since the #104
hoist, which merged the layer's former two scopes (the pair maps'
`Rep ℤ G` argument never pinned the acting group — Mathlib's `Rep` is
universe-polymorphic; it was the homological layer behind the shadowing
`variable {G : Type}` line that did) — and the four abelianized arrows
still precede the six pair-map declarations rather than interleaving
with them as in the source. Everything else ports token-for-token; the
file is the source's `Reciprocity/Main.lean:1009`–`:1328`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Restriction in the first diagram of reciprocity naturality, after
applying abelianization (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:1013`). -/
def normResidueNaturalityAbelianizedRestriction
    (K K' L L' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal] :
    Abelianization
        (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup) →*
      Abelianization
        (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
  Abelianization.map
    (finiteReciprocityNaturalityRestriction K K' L L' hK'K hL'L)

/-- The abelianized restriction sends a represented class to the
included representative's class (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:1034`). -/
@[simp]
theorem normResidueNaturalityAbelianizedRestriction_of_mk
    (K K' L L' : ClosedSubgroup G)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    (k' : K'.toSubgroup) :
    normResidueNaturalityAbelianizedRestriction K K' L L' hK'K hL'L
        (Abelianization.of (QuotientGroup.mk k')) =
      Abelianization.of
        (QuotientGroup.mk (Subgroup.inclusion hK'K k')) := by
  change
    (Abelianization.lift
      (Abelianization.of.comp
        (finiteReciprocityNaturalityRestriction K K' L L' hK'K hL'L)))
        (Abelianization.of (QuotientGroup.mk k')) = _
  rw [Abelianization.lift_apply_of]
  rfl

/-- The right vertical isomorphism `σ*` in the second diagram of
reciprocity naturality, obtained by abelianizing the actual conjugation
isomorphism from norm–conjugation naturality (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:1129`). -/
noncomputable def normResidueNaturalityAbelianizedConjugation
    [ContinuousMul G]
    (K L : ClosedSubgroup G) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    Abelianization
        (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) ≃*
      Abelianization
        ((conjugateClosedSubgroup K s).toSubgroup ⧸
          (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
            (conjugateClosedSubgroup K s).toSubgroup) :=
  (finiteReciprocityNaturalityConjugation K L s).abelianizationCongr

/-- The abelianized conjugation isomorphism computes on representatives
by the conjugation equivalence (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:1147`). -/
@[simp]
theorem normResidueNaturalityAbelianizedConjugation_of_mk
    [ContinuousMul G]
    (K L : ClosedSubgroup G) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup) :
    normResidueNaturalityAbelianizedConjugation K L s
        (Abelianization.of (QuotientGroup.mk k)) =
      Abelianization.of
        (QuotientGroup.mk (conjugateSubgroupEquiv K s k)) := by
  calc
    normResidueNaturalityAbelianizedConjugation K L s
        (Abelianization.of (QuotientGroup.mk k)) =
      Abelianization.of
        (finiteReciprocityNaturalityConjugation K L s (QuotientGroup.mk k)) :=
      abelianizationCongr_of (finiteReciprocityNaturalityConjugation K L s)
        (QuotientGroup.mk k)
    _ = Abelianization.of
        (QuotientGroup.mk (conjugateSubgroupEquiv K s k)) := by
      rw [finiteReciprocityNaturalityConjugation_mk]

/-- **The two vertical arrows of the norm/restriction diagram of
reciprocity naturality, assembled into one additive homomorphism**; its
second component is the relative norm `N_{K'/K}` on finite norm
quotients from norm–conjugation naturality (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:1061`). -/
def normResidueNaturalityNormRestrictionPairMap
    (A : Rep ℤ G)
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    [hLKfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    [hL'K'finite : Finite
      (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup)]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ K'.toSubgroup.subgroupOf K.toSubgroup)] :
    Additive (Abelianization
        (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup)) ×
        FiniteNormQuotient A K' L' hL'K' →+
      Additive (Abelianization
        (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)) ×
        FiniteNormQuotient A K L hLK :=
  AddMonoidHom.prodMap
    (MonoidHom.toAdditive
      (normResidueNaturalityAbelianizedRestriction K K' L L'
        hK'K hL'L))
    (finiteReciprocityNaturalityNormMap A K K' L L'
      hLK hL'K' hK'K hL'L)

/-- On representatives, norm-restriction naturality applies subgroup
inclusion to the Galois class and the relative norm to the field
element (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:1094`). -/
@[simp]
theorem normResidueNaturalityNormRestrictionPairMap_on_representatives
    (A : Rep ℤ G)
    (K K' L L' : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hL'K' : L'.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    (hL'L : L'.toSubgroup ≤ L.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hL'normal : (L'.toSubgroup.subgroupOf K'.toSubgroup).Normal]
    [hLKfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    [hL'K'finite : Finite
      (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup)]
    [hK'Kfinite : Finite
      (K.toSubgroup ⧸ K'.toSubgroup.subgroupOf K.toSubgroup)]
    (k' : K'.toSubgroup) (a : ambientFixedAddSubgroup A K') :
    normResidueNaturalityNormRestrictionPairMap A K K' L L'
        hLK hL'K' hK'K hL'L
        (Additive.ofMul (Abelianization.of (QuotientGroup.mk k')),
          finiteNormClass A K' L' hL'K' a) =
      (Additive.ofMul
          (Abelianization.of
            (QuotientGroup.mk (Subgroup.inclusion hK'K k'))),
        finiteNormClass A K L hLK (relativeNorm A K K' hK'K a)) := by
  ext
  · exact normResidueNaturalityAbelianizedRestriction_of_mk
      K K' L L' hK'K hL'L k'
  · exact finiteReciprocityNaturalityNormMap_finiteNormClass A K K' L L'
      hLK hL'K' hK'K hL'L a

/-- **The two vertical conjugation arrows of reciprocity naturality,
assembled into one additive homomorphism**; the second component is the
actual descended map `a ↦ a^s` from norm–conjugation naturality
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:1171`). -/
def normResidueNaturalityConjugationPairMap
    [ContinuousMul G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    let hConjLK := conjugateClosedSubgroup_mono hLK s
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
          (conjugateClosedSubgroup K s).toSubgroup) :=
      finite_conjugateExtension K L s
    Additive (Abelianization
        (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)) ×
        FiniteNormQuotient A K L hLK →+
      Additive (Abelianization
        ((conjugateClosedSubgroup K s).toSubgroup ⧸
          (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
            (conjugateClosedSubgroup K s).toSubgroup)) ×
        FiniteNormQuotient A (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConjLK := by
  dsimp only
  letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
        (conjugateClosedSubgroup K s).toSubgroup) :=
    finite_conjugateExtension K L s
  exact AddMonoidHom.prodMap
    (MonoidHom.toAdditive
      (normResidueNaturalityAbelianizedConjugation K L s).toMonoidHom)
    (finiteReciprocityNaturalityConjugationNormMap A K L hLK s)

/-- On representatives, the conjugation pair map conjugates both the
Galois class and the fixed-field element (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:1208`). -/
@[simp]
theorem normResidueNaturalityConjugationPairMap_on_representatives
    [ContinuousMul G]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A K) :
    let hConjLK := conjugateClosedSubgroup_mono hLK s
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
          (conjugateClosedSubgroup K s).toSubgroup) :=
      finite_conjugateExtension K L s
    normResidueNaturalityConjugationPairMap A K L hLK s
        (Additive.ofMul (Abelianization.of (QuotientGroup.mk k)),
          finiteNormClass A K L hLK a) =
      (Additive.ofMul
          (Abelianization.of
            (QuotientGroup.mk (conjugateSubgroupEquiv K s k))),
        finiteNormClass A (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s) hConjLK
          (conjugateFixedElement A K s a)) := by
  dsimp only
  letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
        (conjugateClosedSubgroup K s).toSubgroup) :=
    finite_conjugateExtension K L s
  ext
  · exact normResidueNaturalityAbelianizedConjugation_of_mk K L s k
  · exact finiteReciprocityNaturalityConjugationNormMap_finiteNormClass
      A K L hLK s a

/-- **The two upward arrows of the inclusion/transfer diagram of
reciprocity naturality, assembled into one additive homomorphism**: the
first component is Mathlib's actual transfer, transported to
`G(L/K')ᵃᵇ` in transfer–norm naturality, and the second is inclusion
`A_K → A_{K'}` descended to finite norm quotients (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:1247`). -/
def normResidueNaturalityTransferInclusionPairMap
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    letI : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hK'K
    letI : Finite
        (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hK'K)
    Additive (Abelianization
        (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)) ×
        FiniteNormQuotient A K L (hLK'.trans hK'K) →+
      Additive (Abelianization
        (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup)) ×
        FiniteNormQuotient A K' L hLK' := by
  letI : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hK'K
  letI : Finite
      (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hK'K)
  exact AddMonoidHom.prodMap
    (MonoidHom.toAdditive
      (transferNormNaturalityTransfer K K' L hK'K))
    (transferNormNaturalityNormQuotientInclusion A K K' L hLK' hK'K)

/-- On representatives, the transfer-inclusion pair map applies
transfer to the Galois class and fixed-field inclusion to the norm
class (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Main.lean:1289`). -/
@[simp]
theorem normResidueNaturalityTransferInclusionPairMap_on_representatives
    (A : Rep ℤ G) (K K' L : ClosedSubgroup G)
    (hLK' : L.toSubgroup ≤ K'.toSubgroup)
    (hK'K : K'.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (σ : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (a : ambientFixedAddSubgroup A K) :
    letI : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
      transferNormNaturality_intermediateExtension_normal K K' L hK'K
    letI : Finite
        (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
      Finite.of_injective
        (transferNormNaturalityIntermediateInclusion K K' L hK'K)
        (transferNormNaturalityIntermediateInclusion_injective
          K K' L hK'K)
    normResidueNaturalityTransferInclusionPairMap A K K' L hLK' hK'K
        (Additive.ofMul (Abelianization.of σ),
          finiteNormClass A K L (hLK'.trans hK'K) a) =
      (Additive.ofMul
          (transferNormNaturalityTransfer K K' L hK'K
            (Abelianization.of σ)),
        finiteNormClass A K' L hLK'
          (fixedFieldInclusion A K K' hK'K a)) := by
  letI : (L.toSubgroup.subgroupOf K'.toSubgroup).Normal :=
    transferNormNaturality_intermediateExtension_normal K K' L hK'K
  letI : Finite
      (K'.toSubgroup ⧸ L.toSubgroup.subgroupOf K'.toSubgroup) :=
    Finite.of_injective
      (transferNormNaturalityIntermediateInclusion K K' L hK'K)
      (transferNormNaturalityIntermediateInclusion_injective
        K K' L hK'K)
  ext
  · rfl
  · exact transferNormNaturality_normQuotientInclusion_finiteNormClass
      A K K' L hLK' hK'K a

end

end Atlas.Knowledge
