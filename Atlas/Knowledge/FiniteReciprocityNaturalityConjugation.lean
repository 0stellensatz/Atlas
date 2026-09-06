import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityCandidate
import Atlas.Knowledge.FiniteReciprocityHom
import Atlas.Knowledge.FiniteReciprocityNaturalityNorm
import Atlas.Knowledge.FiniteResidueAbstractField
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusFixedField
import Atlas.Knowledge.NormalizedDegree
import Atlas.Knowledge.NormalizedValuationLaws
import Atlas.Knowledge.PrimeElement
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.ReciprocityMap
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.RelativeNormConjugation
import Atlas.Knowledge.RelativeNormLaws
import Atlas.Knowledge.TopologicalGeneration
import Atlas.Knowledge.UnitCohomologyAxiom
import Atlas.Knowledge.ValuationData

/-!
# Finite reciprocity naturality conjugation

The conjugation half of norm–conjugation naturality: degree and
normalized degree are conjugation-invariant, conjugation carries
inertia to inertia and induces a continuous equivalence of the infinite
Frobenius quotients, Frobenius lifts transport with their exponents and
fixed fields, and the conjugation diagram commutes — conjugation of
finite Galois groups corresponds under the finite reciprocity
homomorphism to conjugation of finite norm classes (#104).

## Main definitions

* `DegreeData.finiteReciprocityNaturalityFrobeniusConjugationEquiv` —
  the continuous conjugation equivalence.
* `DegreeData.finiteReciprocityNaturalityFrobeniusConjugationLift` —
  the transported Frobenius lift.

## Main statements

* `DegreeData.finiteReciprocityNaturalityDegree_conjugateSubgroupEquiv`
  — degree invariance; proved.
* `DegreeData.finiteReciprocityNaturalityNormalizedDegree_conjugateSubgroupEquiv`
  — normalized-degree invariance; proved.
* `DegreeData.finiteReciprocityNaturalityMap_extensionInertiaWithin_conjugate`
  — inertia maps to inertia; proved.
* `DegreeData.finiteReciprocityNaturalityFiniteResidueConjugate_normal`
  — transported normality as an instance; proved.
* `DegreeData.finiteReciprocityNaturalityFrobeniusConjugationEquiv_degree`
  — the equivalence preserves normalized degree; proved.
* `DegreeData.finiteReciprocityNaturalityFrobeniusConjugationLift_exponent`
  — the lift preserves the exponent; proved.
* `DegreeData.finiteReciprocityNaturalityFrobeniusConjugationEquiv_mem_closure_iff`
  — closed cyclic subgroups correspond; proved.
* `DegreeData.finiteReciprocityNaturalityConjugation_frobeniusRestriction`
  — conjugation commutes with restriction; proved.
* `DegreeData.finiteReciprocityNaturalityFrobeniusFixedField_conjugate`
  — the conjugated lift's fixed field is the conjugate; proved.
* `DegreeData.finiteReciprocityNaturalityFiniteAbstractConjugate_normal`
  — the finite-field form of transported normality; proved.
* `DegreeData.finiteReciprocityNaturality_conjugation_commutes` — the
  conjugation diagram commutes; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling.
Both sections sit at the source's `Type u`, the representation section
since the #104 hoist unpinned the quotient-action chain it follows. The
profinite integers are the layer's `ProfiniteInteger`, with
`ProfiniteInteger.ofAdd_one_pow_injective` and
`ProfiniteInteger.nsmul_left_injective` for the source's injectivity
devices, the conjugate bundle is the layer's top-level
`FiniteResidueAbstractField.conjugate`, and all
`finite_conjugateExtension` occurrences drop the containment argument,
the layer's form being containment-free. The two normality instances
drop the source's orphaned containment binder, no longer mentioned once
the relative subgroup loses the abbrev; the conjugation diagram's
enrichment `simpa` re-anchors become plain defeq terms; the
map-of-inertia and quotient-conjugation call sites drop containments,
the layer's forms being containment-free; and the commuting square
sheds the source's `[T2Space G]`, Hausdorff being instance-derivable
from the binders it keeps. The citations name this file by bare
basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/` in the source. The
source's `open`s go — the layer keeps everything in one namespace.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

section GroupOnly

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The global degree is invariant under conjugation**
(Yamaguchi 2026, `MainNaturality.lean:825`). -/
theorem finiteReciprocityNaturalityDegree_conjugateSubgroupEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : ClosedSubgroup G) (s : G) (k : K.toSubgroup) :
    D.degree (conjugateSubgroupEquiv K s k).1 = D.degree k.1 := by
  rw [conjugateSubgroupEquiv_apply_coe, map_mul, map_mul, map_inv]
  simp [mul_comm]

/-- **The normalized degree is invariant under the conjugation
equivalence of field subgroups** (Yamaguchi 2026,
`MainNaturality.lean:834`). -/
theorem finiteReciprocityNaturalityNormalizedDegree_conjugateSubgroupEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (s : G)
    (k : K.field.toSubgroup) :
    D.normalizedDegree (K.conjugate s : FiniteResidueAbstractField D)
        (conjugateSubgroupEquiv K.field s k) =
      D.normalizedDegree K k := by
  apply Multiplicative.ext
  apply ProfiniteInteger.nsmul_left_injective K.residueDegree.property.ne'
  change (K.residueDegree : ℕ) •
      (D.normalizedDegree (K.conjugate s : FiniteResidueAbstractField D)
        (conjugateSubgroupEquiv K.field s k)).toAdd =
    (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd
  rw [D.residueDegree_nsmul_normalizedDegree K k]
  rw [← K.residueDegree_conjugate s]
  rw [D.residueDegree_nsmul_normalizedDegree
    (K.conjugate s : FiniteResidueAbstractField D)]
  exact congrArg Multiplicative.toAdd
    (D.finiteReciprocityNaturalityDegree_conjugateSubgroupEquiv K.field s k)

/-- **Conjugation carries `I_L` inside `G_K` exactly to the inertia
subgroup for `Lˢ | Kˢ`** (Yamaguchi 2026,
`MainNaturality.lean:856`). -/
theorem finiteReciprocityNaturalityMap_extensionInertiaWithin_conjugate
    (D : DegreeData G) [IsTopologicalGroup G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G) :
    (D.extensionInertiaWithin K L hLK).map
        (conjugateSubgroupEquiv K s).toMonoidHom =
      D.extensionInertiaWithin (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) := by
  ext x
  constructor
  · rintro ⟨k, ⟨hkL, hkI⟩, rfl⟩
    constructor
    · rw [← map_extensionSubgroup_conjugate K L s]
      exact ⟨k, hkL, rfl⟩
    · change conjugateSubgroupEquiv K s k ∈
        D.fieldInertiaWithin (conjugateClosedSubgroup K s)
      rw [D.mem_fieldInertiaWithin_iff,
        D.finiteReciprocityNaturalityDegree_conjugateSubgroupEquiv K s,
        ← D.mem_fieldInertiaWithin_iff]
      exact hkI
  · intro hx
    let k := (conjugateSubgroupEquiv K s).symm x
    refine ⟨k, ?_, (conjugateSubgroupEquiv K s).apply_symm_apply x⟩
    constructor
    · have hxL : x ∈ (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
          (conjugateClosedSubgroup K s).toSubgroup := hx.1
      rw [← map_extensionSubgroup_conjugate K L s] at hxL
      rcases hxL with ⟨k', hk'L, hk'eq⟩
      have : k' = k := by
        apply (conjugateSubgroupEquiv K s).injective
        exact hk'eq.trans
          ((conjugateSubgroupEquiv K s).apply_symm_apply x).symm
      simpa [this] using hk'L
    · change k ∈ D.fieldInertiaWithin K
      rw [D.mem_fieldInertiaWithin_iff]
      rw [← D.finiteReciprocityNaturalityDegree_conjugateSubgroupEquiv K s k]
      rw [(conjugateSubgroupEquiv K s).apply_symm_apply x]
      exact (D.mem_fieldInertiaWithin_iff _ _).mp hx.2

/-- **Conjugation as a continuous multiplicative equivalence on the
infinite Frobenius quotients** (Yamaguchi 2026,
`MainNaturality.lean:899`). -/
noncomputable def finiteReciprocityNaturalityFrobeniusConjugationEquiv
    (D : DegreeData G) [IsTopologicalGroup G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) ≃ₜ*
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        D.extensionInertiaWithin (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) := by
  let e : (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) ≃*
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        D.extensionInertiaWithin (conjugateClosedSubgroup K s)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)) :=
    QuotientGroup.congr
      (D.extensionInertiaWithin K L hLK)
      (D.extensionInertiaWithin (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s))
      (conjugateSubgroupEquiv K s)
      (D.finiteReciprocityNaturalityMap_extensionInertiaWithin_conjugate K L hLK s)
  refine { e with
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    change Continuous (fun k : K.toSubgroup =>
      QuotientGroup.mk (conjugateSubgroupEquiv K s k))
    apply QuotientGroup.continuous_mk.comp
    change Continuous (fun k : K.toSubgroup =>
      (⟨s⁻¹ * k.1 * s, by
        change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup K s
        rw [conjugateClosedSubgroup_mem]
        simp [mul_assoc]⟩ :
          (conjugateClosedSubgroup K s).toSubgroup))
    exact ((continuous_const.mul continuous_subtype_val).mul
      continuous_const).subtype_mk _
  · rw [← QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff]
    change Continuous (fun x : (conjugateClosedSubgroup K s).toSubgroup =>
      QuotientGroup.mk ((conjugateSubgroupEquiv K s).symm x))
    apply QuotientGroup.continuous_mk.comp
    change Continuous (fun x : (conjugateClosedSubgroup K s).toSubgroup =>
      (⟨s * x.1 * s⁻¹,
        (conjugateClosedSubgroup_mem K s x.1).mp x.2⟩ : K.toSubgroup))
    exact ((continuous_const.mul continuous_subtype_val).mul
      continuous_const).subtype_mk _

/-- The conjugation equivalence evaluates on representatives by the
subgroup equivalence (Yamaguchi 2026, `MainNaturality.lean:948`). -/
@[simp]
theorem finiteReciprocityNaturalityFrobeniusConjugationEquiv_mk
    (D : DegreeData G) [IsTopologicalGroup G]
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [(L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup) :
    D.finiteReciprocityNaturalityFrobeniusConjugationEquiv K L hLK s
        (QuotientGroup.mk k) =
      QuotientGroup.mk (conjugateSubgroupEquiv K s k) := by
  simp [finiteReciprocityNaturalityFrobeniusConjugationEquiv]

/-- **Normality transported by conjugation at the residue-finite field
boundary** — an instance, so clients never unfold the bundled conjugate
to recover it (Yamaguchi 2026, `MainNaturality.lean:963`). -/
instance finiteReciprocityNaturalityFiniteResidueConjugate_normal
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    ((conjugateClosedSubgroup L s).toSubgroup.subgroupOf
      (K.conjugate s).field.toSubgroup).Normal := by
  change
    ((conjugateClosedSubgroup L s).toSubgroup.subgroupOf
      (conjugateClosedSubgroup K.field s).toSubgroup).Normal
  infer_instance

/-- **The conjugation equivalence preserves normalized degree**
(Yamaguchi 2026, `MainNaturality.lean:978`). -/
theorem finiteReciprocityNaturalityFrobeniusConjugationEquiv_degree
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) :
    D.extensionNormalizedDegree
        (K.conjugate s : FiniteResidueAbstractField D)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (D.finiteReciprocityNaturalityFrobeniusConjugationEquiv K.field L hLK s q) =
      D.extensionNormalizedDegree K L hLK q := by
  refine Quotient.inductionOn' q ?_
  intro k
  change D.normalizedDegree (K.conjugate s)
      (conjugateSubgroupEquiv K.field s k) =
    D.normalizedDegree K k
  exact D.finiteReciprocityNaturalityNormalizedDegree_conjugateSubgroupEquiv
    K s k

/-- **Conjugation transports positive Frobenius lifts without changing
their exponent** (Yamaguchi 2026, `MainNaturality.lean:1000`). -/
def finiteReciprocityNaturalityFrobeniusConjugationLift
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.FrobeniusElements (K.conjugate s : FiniteResidueAbstractField D)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s) := by
  let n := D.frobeniusExponent K L hLK σ
  refine ⟨D.finiteReciprocityNaturalityFrobeniusConjugationEquiv K.field L hLK s σ.1,
    n, D.frobeniusExponent_pos K L hLK σ, ?_⟩
  rw [D.finiteReciprocityNaturalityFrobeniusConjugationEquiv_degree]
  exact D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ

/-- The conjugation lift coerces to the equivalence's value
(Yamaguchi 2026, `MainNaturality.lean:1017`). -/
@[simp]
theorem finiteReciprocityNaturalityFrobeniusConjugationLift_coe
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ).1 =
      D.finiteReciprocityNaturalityFrobeniusConjugationEquiv K.field L hLK s σ.1 := by
  rfl

/-- **The conjugation lift preserves the exponent**
(Yamaguchi 2026, `MainNaturality.lean:1029`). -/
@[simp]
theorem finiteReciprocityNaturalityFrobeniusConjugationLift_exponent
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    D.frobeniusExponent (K.conjugate s : FiniteResidueAbstractField D)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ) =
      D.frobeniusExponent K L hLK σ := by
  apply ProfiniteInteger.ofAdd_one_pow_injective
  calc
    (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
        D.frobeniusExponent
          (K.conjugate s : FiniteResidueAbstractField D)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)
          (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ) =
      D.extensionNormalizedDegree
        (K.conjugate s : FiniteResidueAbstractField D)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ).1 :=
      (D.extensionNormalizedDegree_frobenius_eq_pow
        (K.conjugate s : FiniteResidueAbstractField D)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        _).symm
    _ = D.extensionNormalizedDegree K L hLK σ.1 := by
      rw [D.finiteReciprocityNaturalityFrobeniusConjugationLift_coe,
        D.finiteReciprocityNaturalityFrobeniusConjugationEquiv_degree]
    _ = (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
        D.frobeniusExponent K L hLK σ :=
      D.extensionNormalizedDegree_frobenius_eq_pow K L hLK σ

/-- **The conjugation equivalence identifies the two closed cyclic
subgroups generated by corresponding Frobenius lifts**
(Yamaguchi 2026, `MainNaturality.lean:1067`). -/
theorem finiteReciprocityNaturalityFrobeniusConjugationEquiv_mem_closure_iff
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) :
    q ∈ (D.frobeniusClosure K L hLK σ).toSubgroup ↔
      D.finiteReciprocityNaturalityFrobeniusConjugationEquiv K.field L hLK s q ∈
        (D.frobeniusClosure
          (K.conjugate s : FiniteResidueAbstractField D)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)
          (D.finiteReciprocityNaturalityFrobeniusConjugationLift
            K L hLK s σ)).toSubgroup := by
  let e := D.finiteReciprocityNaturalityFrobeniusConjugationEquiv K.field L hLK s
  constructor
  · intro hq
    have hmap := map_mem_closedSubgroupGenerated_singleton
      (ContinuousMonoidHom.toContinuousMonoidHom e) σ.1 (by
        simpa [DegreeData.frobeniusClosure] using hq)
    unfold DegreeData.frobeniusClosure
    unfold FiniteResidueAbstractField.conjugate
    rw [D.finiteReciprocityNaturalityFrobeniusConjugationLift_coe]
    simpa [e] using hmap
  · intro hq
    have hq' : e q ∈ closedSubgroupGenerated {e σ.1} := by
      unfold DegreeData.frobeniusClosure at hq
      unfold FiniteResidueAbstractField.conjugate at hq
      rw [D.finiteReciprocityNaturalityFrobeniusConjugationLift_coe] at hq
      change e q ∈ (closedSubgroupGenerated {e σ.1}).toSubgroup
      simpa [e] using hq
    have hmap := map_mem_closedSubgroupGenerated_singleton
      (ContinuousMonoidHom.toContinuousMonoidHom e.symm)
      (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ).1
      (by
        rw [D.finiteReciprocityNaturalityFrobeniusConjugationLift_coe]
        exact hq')
    simpa [DegreeData.frobeniusClosure,
      D.finiteReciprocityNaturalityFrobeniusConjugationLift_coe, e] using hmap

/-- **Conjugation of a Frobenius lift commutes with restriction to the
finite Galois quotient** (Yamaguchi 2026, `MainNaturality.lean:1110`). -/
theorem finiteReciprocityNaturalityConjugation_frobeniusRestriction
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    finiteReciprocityNaturalityConjugation K.field L s
        (D.frobeniusRestriction K L hLK σ) =
      D.frobeniusRestriction
        (K.conjugate s : FiniteResidueAbstractField D)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ) := by
  change finiteReciprocityNaturalityConjugation K.field L s
      (D.extensionRestriction K.field L hLK σ.1) =
    D.extensionRestriction
      (K.conjugate s : FiniteResidueAbstractField D).field
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)
      (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ).1
  rw [D.finiteReciprocityNaturalityFrobeniusConjugationLift_coe]
  refine Quotient.inductionOn' σ.1 ?_
  intro k
  rfl

/-- **The fixed field of the conjugated Frobenius lift is the conjugate
of the original fixed field** (Yamaguchi 2026,
`MainNaturality.lean:1137`). -/
theorem finiteReciprocityNaturalityFrobeniusFixedField_conjugate
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK) :
    conjugateClosedSubgroup (D.frobeniusFixedField K L hLK σ) s =
      D.frobeniusFixedField
        (K.conjugate s : FiniteResidueAbstractField D)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ) := by
  ext g
  change (g ∈ conjugateClosedSubgroup
      (D.frobeniusFixedField K L hLK σ) s) ↔
    g ∈ D.frobeniusFixedField
      (K.conjugate s : FiniteResidueAbstractField D)
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)
      (D.finiteReciprocityNaturalityFrobeniusConjugationLift K L hLK s σ)
  rw [conjugateClosedSubgroup_mem]
  constructor
  · rintro ⟨k, hk, hkg⟩
    let ks : (K.conjugate s : FiniteResidueAbstractField D).field.toSubgroup :=
      conjugateSubgroupEquiv K.field s k
    have hksg : ks.1 = g := by
      dsimp [ks]
      change (k : G) = s * g * s⁻¹ at hkg
      rw [hkg]
      simp [mul_assoc]
    have hkClosure : QuotientGroup.mk k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup :=
      (D.mem_frobeniusFixedSubgroupWithin_iff K L hLK σ k).1 hk
    have hksClosure : QuotientGroup.mk ks ∈
        (D.frobeniusClosure
          (K.conjugate s : FiniteResidueAbstractField D)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)
          (D.finiteReciprocityNaturalityFrobeniusConjugationLift
            K L hLK s σ)).toSubgroup := by
      have hmap :=
        (D.finiteReciprocityNaturalityFrobeniusConjugationEquiv_mem_closure_iff
          K L hLK s σ (QuotientGroup.mk k)).1 hkClosure
      have hmk :
          D.finiteReciprocityNaturalityFrobeniusConjugationEquiv
              K.field L hLK s (QuotientGroup.mk k) =
            QuotientGroup.mk ks := by
        apply QuotientGroup.eq_iff_div_mem.mpr
        simp [ks]
      rw [hmk] at hmap
      exact hmap
    refine ⟨ks, ?_, hksg⟩
    exact (D.mem_frobeniusFixedSubgroupWithin_iff
      (K.conjugate s : FiniteResidueAbstractField D)
      (conjugateClosedSubgroup L s) (conjugateClosedSubgroup_mono hLK s)
      (D.finiteReciprocityNaturalityFrobeniusConjugationLift
        K L hLK s σ) ks).2 hksClosure
  · rintro ⟨ks, hks, hksg⟩
    let k : K.field.toSubgroup :=
      (conjugateSubgroupEquiv K.field s).symm ks
    have hkValue : k.1 = s * g * s⁻¹ := by
      dsimp [k]
      change (ks : G) = g at hksg
      change s * (ks : G) * s⁻¹ = s * g * s⁻¹
      rw [hksg]
    have hksClosure : QuotientGroup.mk ks ∈
        (D.frobeniusClosure
          (K.conjugate s : FiniteResidueAbstractField D)
          (conjugateClosedSubgroup L s)
          (conjugateClosedSubgroup_mono hLK s)
          (D.finiteReciprocityNaturalityFrobeniusConjugationLift
            K L hLK s σ)).toSubgroup :=
      (D.mem_frobeniusFixedSubgroupWithin_iff
        (K.conjugate s : FiniteResidueAbstractField D)
        (conjugateClosedSubgroup L s) (conjugateClosedSubgroup_mono hLK s)
        (D.finiteReciprocityNaturalityFrobeniusConjugationLift
          K L hLK s σ) ks).1 hks
    have hkClosure : QuotientGroup.mk k ∈
        (D.frobeniusClosure K L hLK σ).toSubgroup := by
      apply (D.finiteReciprocityNaturalityFrobeniusConjugationEquiv_mem_closure_iff
        K L hLK s σ (QuotientGroup.mk k)).2
      have hmk :
          D.finiteReciprocityNaturalityFrobeniusConjugationEquiv
              K.field L hLK s (QuotientGroup.mk k) =
            QuotientGroup.mk ks := by
        apply QuotientGroup.eq_iff_div_mem.mpr
        simp [k]
      rw [hmk]
      exact hksClosure
    refine ⟨k, ?_, hkValue⟩
    exact (D.mem_frobeniusFixedSubgroupWithin_iff K L hLK σ k).2 hkClosure

end DegreeData

end GroupOnly

section Representation

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **Normality of a conjugated finite abstract field without unfolding
the bundle** (Yamaguchi 2026, `MainNaturality.lean:1242`). -/
instance finiteReciprocityNaturalityFiniteAbstractConjugate_normal
    [IsTopologicalGroup G]
    (K : FiniteAbstractField G) (L : ClosedSubgroup G) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    ((conjugateClosedSubgroup L s).toSubgroup.subgroupOf
      (K.conjugate s).field.toSubgroup).Normal := by
  change
    ((conjugateClosedSubgroup L s).toSubgroup.subgroupOf
      (conjugateClosedSubgroup K.field s).toSubgroup).Normal
  infer_instance

/- Prime-element transport along an equality of fields
(Yamaguchi 2026, `MainNaturality.lean:1256`). -/
private theorem finiteReciprocityNaturality_isPrimeElement_transport
    (D : DegreeData G) {A : Rep ℤ G} (v : ValuationData D A)
    (S T : FiniteAbstractField G) (hST : S.field = T.field)
    (π : ambientFixedAddSubgroup A S.field) (hπ : v.IsPrimeElement S π) :
    v.IsPrimeElement T (hST ▸ π) := by
  cases S
  cases T
  cases hST
  simpa only using hπ

/- Relative-norm transport along an equality of upper fields
(Yamaguchi 2026, `MainNaturality.lean:1266`). -/
private theorem finiteReciprocityNaturality_relativeNorm_right_transport
    (A : Rep ℤ G) (K S T : ClosedSubgroup G) (hST : S = T)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (hTK : T.toSubgroup ≤ K.toSubgroup)
    [hKSfinite : Finite
      (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)]
    [hKTfinite : Finite
      (K.toSubgroup ⧸ T.toSubgroup.subgroupOf K.toSubgroup)]
    (π : ambientFixedAddSubgroup A S) :
    relativeNorm A K S hSK π =
      relativeNorm A K T hTK (hST ▸ π) := by
  subst T
  rfl

/-- **The conjugation diagram commutes**: conjugation of finite Galois
groups corresponds under the finite reciprocity homomorphism to
conjugation of finite norm classes (Yamaguchi 2026,
`MainNaturality.lean:1283`). -/
theorem finiteReciprocityNaturality_conjugation_commutes
    (D : DegreeData G) (A : Rep ℤ G) (v : ValuationData D A)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (hAxiom : v.SatisfiesUnramifiedUnitCohomology D)
    (K : FiniteAbstractField G) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    let Ks : FiniteAbstractField G := K.conjugate s
    let Ls := conjugateClosedSubgroup L s
    let hLsKs := conjugateClosedSubgroup_mono hLK s
    letI : Finite
        (Ks.field.toSubgroup ⧸ Ls.toSubgroup.subgroupOf Ks.field.toSubgroup) :=
      finite_conjugateExtension K.field L s
    (finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s).comp
        (D.finiteReciprocityHom A v hAxiom K L hLK) =
      (D.finiteReciprocityHom A v hAxiom Ks Ls hLsKs).comp
        (finiteReciprocityNaturalityConjugation K.field L s).toMonoidHom.toAdditive := by
  dsimp only
  letI hLsfinite : Finite
      ((conjugateClosedSubgroup K.field s).toSubgroup ⧸
        (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
          (conjugateClosedSubgroup K.field s).toSubgroup) :=
    finite_conjugateExtension K.field L s
  let KR : FiniteResidueAbstractField D :=
    K.toFiniteResidueAbstractField D
  let Ks : FiniteAbstractField G := K.conjugate s
  let KRs : FiniteResidueAbstractField D :=
    Ks.toFiniteResidueAbstractField D
  have hKRs_conjugate : KR.conjugate s = KRs := by
    dsimp [KRs, Ks, KR]
    unfold FiniteAbstractField.toFiniteResidueAbstractField
    unfold FiniteAbstractField.conjugate
    unfold FiniteResidueAbstractField.conjugate
    rfl
  letI hLsfiniteKs : Finite
      (Ks.field.toSubgroup ⧸
        (conjugateClosedSubgroup L s).toSubgroup.subgroupOf Ks.field.toSubgroup) := by
    change Finite
      ((conjugateClosedSubgroup K.field s).toSubgroup ⧸
        (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
          (conjugateClosedSubgroup K.field s).toSubgroup)
    exact hLsfinite
  letI hLsfiniteKRs : Finite
      (KRs.field.toSubgroup ⧸
        (conjugateClosedSubgroup L s).toSubgroup.subgroupOf KRs.field.toSubgroup) := hLsfiniteKs
  letI hLnormalKR : (L.toSubgroup.subgroupOf KR.field.toSubgroup).Normal := hLnormal
  letI hLsnormalKs :
      ((conjugateClosedSubgroup L s).toSubgroup.subgroupOf Ks.field.toSubgroup).Normal := by
    change
      ((conjugateClosedSubgroup L s).toSubgroup.subgroupOf
        (conjugateClosedSubgroup K.field s).toSubgroup).Normal
    infer_instance
  letI hLsnormalKRs :
      ((conjugateClosedSubgroup L s).toSubgroup.subgroupOf
        KRs.field.toSubgroup).Normal := hLsnormalKs
  apply AddMonoidHom.ext
  intro q
  let σ := D.chosenFiniteReciprocityFrobeniusLift KR L hLK q.toMul
  let σs : D.FrobeniusElements KRs
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s) := by
    subst KRs
    exact D.finiteReciprocityNaturalityFrobeniusConjugationLift
      KR L hLK s σ
  have hσ : D.frobeniusRestriction KR L hLK σ = q.toMul :=
    D.frobeniusRestriction_chosenFiniteReciprocityFrobeniusLift
      KR L hLK q.toMul
  have hσs : D.frobeniusRestriction KRs
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s) σs =
      ((finiteReciprocityNaturalityConjugation
        K.field L s).toMonoidHom.toAdditive q).toMul := by
    change D.frobeniusRestriction KRs
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) σs =
      finiteReciprocityNaturalityConjugation K.field L s q.toMul
    rw [← hσ]
    symm
    change finiteReciprocityNaturalityConjugation K.field L s
        (D.extensionRestriction KR.field L hLK σ.1) =
      D.extensionRestriction KRs.field
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) σs.1
    unfold σs
    cases hKRs_conjugate
    dsimp only [id]
    rw [D.finiteReciprocityNaturalityFrobeniusConjugationLift_coe]
    refine Quotient.inductionOn' σ.1 ?_
    intro k
    rfl
  let S := D.frobeniusFixedField KR L hLK σ
  let Ss := D.frobeniusFixedField KRs
    (conjugateClosedSubgroup L s)
    (conjugateClosedSubgroup_mono hLK s) σs
  let hSK := D.frobeniusFixedField_le KR L hLK σ
  let hSsKs := D.frobeniusFixedField_le KRs
    (conjugateClosedSubgroup L s)
    (conjugateClosedSubgroup_mono hLK s) σs
  have hConjS : conjugateClosedSubgroup S s = Ss := by
    exact D.finiteReciprocityNaturalityFrobeniusFixedField_conjugate
      KR L hLK s σ
  letI hSKfinite : Finite
      (K.field.toSubgroup ⧸ S.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite KR L hLK σ
  letI hConjSKfinite : Finite
      (Ks.field.toSubgroup ⧸
        (conjugateClosedSubgroup S s).toSubgroup.subgroupOf Ks.field.toSubgroup) :=
    by
      change Finite
        ((conjugateClosedSubgroup K.field s).toSubgroup ⧸
          (conjugateClosedSubgroup S s).toSubgroup.subgroupOf
            (conjugateClosedSubgroup K.field s).toSubgroup)
      exact finite_conjugateExtension K.field S s
  letI hSsKsfinite : Finite
      (Ks.field.toSubgroup ⧸ Ss.toSubgroup.subgroupOf Ks.field.toSubgroup) :=
    D.frobeniusFixedField_finite KRs
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s) σs
  let Sfinite : FiniteAbstractField G :=
    { field := S
      finite := D.frobeniusFixedField_absoluteFinite K L hLK σ }
  let Ssfinite : FiniteAbstractField G :=
    { field := Ss
      finite := D.frobeniusFixedField_absoluteFinite Ks
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s) σs }
  let π : ambientFixedAddSubgroup A S := v.chosenPrimeElement Sfinite
  have hπ : v.IsPrimeElement Sfinite π := v.chosenPrimeElement_isPrime Sfinite
  let πs0 : ambientFixedAddSubgroup A (conjugateClosedSubgroup S s) :=
    conjugateFixedElement A S s π
  have hπs0 : v.IsPrimeElement (Sfinite.conjugate s) πs0 := by
    rw [ValuationData.IsPrimeElement]
    rw [show v.valuationAt (Sfinite.conjugate s) πs0 =
        v.valuationAt Sfinite π by
      simpa [Sfinite, πs0] using
        v.normalizedValuation_conjugate Sfinite s π]
    exact hπ
  let πs : ambientFixedAddSubgroup A Ss := hConjS ▸ πs0
  have hπs : v.IsPrimeElement Ssfinite πs := by
    have htransport :=
      D.finiteReciprocityNaturality_isPrimeElement_transport v
        (Sfinite.conjugate s) Ssfinite (by exact hConjS) πs0 hπs0
    unfold πs
    exact htransport
  change finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s
      (D.finiteReciprocityHom A v hAxiom K L hLK q) =
    D.finiteReciprocityHom A v hAxiom Ks
      (conjugateClosedSubgroup L s)
      (conjugateClosedSubgroup_mono hLK s)
      ((finiteReciprocityNaturalityConjugation
        K.field L s).toMonoidHom.toAdditive q)
  calc
    finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s
        (D.finiteReciprocityHom A v hAxiom K L hLK q) =
      finiteReciprocityNaturalityConjugationNormMap A K.field L hLK s
        (finiteNormClass A K.field L hLK
          (relativeNorm A K.field S hSK π)) := by
      rw [D.finiteReciprocityHom_apply_eq_primeNormClass
        A v hAxiom K L hLK q σ hσ π hπ]
    _ = finiteNormClass A Ks.field
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (relativeNorm A Ks.field
          (conjugateClosedSubgroup S s)
          (conjugateClosedSubgroup_mono hSK s) πs0) := by
      exact finiteReciprocityNaturality_conjugation_norm_class
        A K.field L S hLK hSK s π
    _ = finiteNormClass A Ks.field
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (relativeNorm A Ks.field Ss hSsKs πs) := by
      apply congrArg (finiteNormClass A Ks.field
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s))
      have htransport :=
        finiteReciprocityNaturality_relativeNorm_right_transport A
          Ks.field (conjugateClosedSubgroup S s) Ss
          hConjS (conjugateClosedSubgroup_mono hSK s) hSsKs πs0
      simpa [πs] using htransport
    _ = D.finiteReciprocityHom A v hAxiom Ks
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        ((finiteReciprocityNaturalityConjugation
          K.field L s).toMonoidHom.toAdditive q) := by
      rw [D.finiteReciprocityHom_apply_eq_primeNormClass
        A v hAxiom Ks
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        _ σs hσs πs hπs]

end DegreeData

end Representation

end

end Atlas.Knowledge
