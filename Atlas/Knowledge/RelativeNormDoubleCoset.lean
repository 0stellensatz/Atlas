import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.RelativeNorm

/-!
# Relative norm double coset

The double-coset decomposition of a relative norm: Mathlib's
class-formula equivalence partitions the left cosets for `S | K` by the
orbits of an intermediate subgroup, and the norm reindexes along it —
first by orbits, then by stabilizer cosets — the additive form of the
decomposition behind transfer–norm naturality (#104).

## Main definitions

* `relativeNormDoubleCosetEquiv` — the class-formula decomposition.

## Main statements

* `relativeNorm_eq_sum_doubleCoset` — the reindexed norm; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling —
freeing the containments the decomposition side bound only for it, which
go, and thinning both norm formulas by the second containment — the
source's `@[implicit_reducible]` markers stay on the three private
`Fintype` suppliers (class-type definitions demand them, unlike the
layer's dropped precedents), the ambient group of the norm half is
`Type` after the representation chain, and the source's universe-device
import and no-op opens go.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

open MulAction

section doubleCosetEquivalences

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Membership in the stabilizer of a left coset is the literal
conjugate-intersection condition — for the representative `t⁻¹` it reads
`k' ∈ K' ∩ t⁻¹ S t`, the subgroup of the classical double-coset norm
calculation ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/RelativeNormDoubleCoset.lean:34`]
[Yamaguchi2026]). -/
theorem mem_relativeNormDoubleCoset_stabilizer_iff
    (K K' S : ClosedSubgroup G) (t : K.toSubgroup)
    (k' : K'.toSubgroup.subgroupOf K.toSubgroup) :
    k' ∈ MulAction.stabilizer (K'.toSubgroup.subgroupOf K.toSubgroup)
        (QuotientGroup.mk t :
          K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup) ↔
      t.1⁻¹ * k'.1.1 * t.1 ∈ S.toSubgroup := by
  rw [mem_stabilizer_iff]
  change QuotientGroup.mk (k'.1 * t) = QuotientGroup.mk t ↔ _
  rw [QuotientGroup.eq]
  change (k'.1 * t).1⁻¹ * t.1 ∈ S.toSubgroup ↔ _
  constructor
  · intro h
    have hi := S.toSubgroup.inv_mem h
    simpa [mul_assoc] using hi
  · intro h
    have hi := S.toSubgroup.inv_mem h
    simpa [mul_assoc] using hi

/-- **The class-formula decomposition of the left cosets for `S | K`
into orbits under the subgroup belonging to `K' | K` and the
corresponding stabilizer cosets** — the double cosets ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/RelativeNormDoubleCoset.lean:59`]
[Yamaguchi2026]). -/
noncomputable def relativeNormDoubleCosetEquiv
    (K K' S : ClosedSubgroup G) :
    (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup) ≃
      Σ q : Quotient (orbitRel (K'.toSubgroup.subgroupOf K.toSubgroup)
        (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)),
        (K'.toSubgroup.subgroupOf K.toSubgroup) ⧸
          MulAction.stabilizer (K'.toSubgroup.subgroupOf K.toSubgroup) q.out :=
  MulAction.selfEquivSigmaOrbitsQuotientStabilizer
    (K'.toSubgroup.subgroupOf K.toSubgroup)
    (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)

/-- The inverse class-formula map is left multiplication of the selected
orbit representative by the selected stabilizer-coset representative
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/RelativeNormDoubleCoset.lean:75`]
[Yamaguchi2026]). -/
@[simp]
theorem relativeNormDoubleCosetEquiv_symm_apply
    (K K' S : ClosedSubgroup G)
    (q : Quotient (orbitRel (K'.toSubgroup.subgroupOf K.toSubgroup)
      (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)))
    (r : (K'.toSubgroup.subgroupOf K.toSubgroup) ⧸
      MulAction.stabilizer (K'.toSubgroup.subgroupOf K.toSubgroup) q.out) :
    (relativeNormDoubleCosetEquiv K K' S).symm ⟨q, r⟩ =
      r.out • q.out := by
  change (((MulAction.orbitEquivQuotientStabilizer
    (K'.toSubgroup.subgroupOf K.toSubgroup) q.out).symm r :
      MulAction.orbit (K'.toSubgroup.subgroupOf K.toSubgroup) q.out) :
        K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup) = _
  refine Quotient.inductionOn' r ?_
  intro s
  calc
    (((MulAction.orbitEquivQuotientStabilizer
        (K'.toSubgroup.subgroupOf K.toSubgroup) q.out).symm
          (QuotientGroup.mk s) :
        MulAction.orbit (K'.toSubgroup.subgroupOf K.toSubgroup) q.out) :
          K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup) = s • q.out :=
      MulAction.orbitEquivQuotientStabilizer_symm_apply
        (K'.toSubgroup.subgroupOf K.toSubgroup) q.out s
    _ = (QuotientGroup.mk s).out • q.out := by
      symm
      simpa only [MulAction.ofQuotientStabilizer_mk] using
        congrArg
          (MulAction.ofQuotientStabilizer
            (K'.toSubgroup.subgroupOf K.toSubgroup) q.out)
          (QuotientGroup.out_eq' (QuotientGroup.mk s))

end doubleCosetEquivalences

/-- The class-formula inverse for an arbitrary chosen representative of
each orbit — the form transfer–norm naturality uses to choose the norm
representative `t⁻¹` attached to a transfer representative `t`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/RelativeNormDoubleCoset.lean:113`]
[Yamaguchi2026]). -/
@[simp]
theorem chosenOrbitClassEquiv_symm_apply
    {M : Type*} {X : Type*} [Group M] [MulAction M X]
    {φ : Quotient (orbitRel M X) → X}
    (hφ : Function.LeftInverse Quotient.mk'' φ)
    (q : Quotient (orbitRel M X))
    (r : M ⧸ stabilizer M (φ q)) :
    (MulAction.selfEquivSigmaOrbitsQuotientStabilizer' M X hφ).symm
        ⟨q, r⟩ = r.out • φ q := by
  change (((MulAction.orbitEquivQuotientStabilizer M (φ q)).symm r :
      orbit M (φ q)) : X) = _
  refine Quotient.inductionOn' r ?_
  intro m
  calc
    (((MulAction.orbitEquivQuotientStabilizer M (φ q)).symm
        (QuotientGroup.mk m) : orbit M (φ q)) : X) = m • φ q :=
      MulAction.orbitEquivQuotientStabilizer_symm_apply M (φ q) m
    _ = (QuotientGroup.mk m).out • φ q := by
      symm
      simpa only [MulAction.ofQuotientStabilizer_mk] using
        congrArg (MulAction.ofQuotientStabilizer M (φ q))
          (QuotientGroup.out_eq' (QuotientGroup.mk m))

section relativeNormFormulas

variable {G : Type} [Group G] [TopologicalSpace G]

/-- The relative norm reindexed by arbitrary chosen representatives of
the intermediate-subgroup orbits ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/RelativeNormDoubleCoset.lean:142`]
[Yamaguchi2026]). -/
theorem relativeNorm_eq_sum_chosenOrbit_of_fintype
    (A : Rep ℤ G) (K S : ClosedSubgroup G)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    (M : Subgroup K.toSubgroup)
    [Finite (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)]
    {φ : Quotient (orbitRel M
      (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)) →
        (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)}
    (hφ : Function.LeftInverse Quotient.mk'' φ)
    [Fintype (Quotient (orbitRel M
      (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)))]
    [(q : Quotient (orbitRel M
      (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup))) →
      Fintype (M ⧸ stabilizer M (φ q))]
    (a : ambientFixedAddSubgroup A S) :
    ((relativeNorm A K S hSK a : ambientFixedAddSubgroup A K) : A.V) =
      ∑ q, ∑ r, relativeCosetAction A K S hSK a
        ((MulAction.selfEquivSigmaOrbitsQuotientStabilizer'
          M (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup) hφ).symm ⟨q, r⟩) := by
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)
  rw [relativeNorm_apply_coe, relativeNormValue]
  let e := MulAction.selfEquivSigmaOrbitsQuotientStabilizer'
    M (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup) hφ
  calc
    ∑ q, relativeCosetAction A K S hSK a q =
        ∑ p, relativeCosetAction A K S hSK a (e.symm p) :=
      (e.symm.sum_comp (relativeCosetAction A K S hSK a)).symm
    _ = _ := Fintype.sum_sigma _

/- The sigma type of the decomposition is finite ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/RelativeNormDoubleCoset.lean:173`]
[Yamaguchi2026]). -/
@[implicit_reducible]
private noncomputable def relativeNormDoubleCosetSigmaFintype
    (K K' S : ClosedSubgroup G)
    [Finite (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)] :
    Fintype (Σ q : Quotient (orbitRel
      (K'.toSubgroup.subgroupOf K.toSubgroup)
      (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)),
      (K'.toSubgroup.subgroupOf K.toSubgroup) ⧸
        MulAction.stabilizer (K'.toSubgroup.subgroupOf K.toSubgroup) q.out) := by
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)
  exact Fintype.ofEquiv
    (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)
    (relativeNormDoubleCosetEquiv K K' S)

/- The orbit set is finite ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/RelativeNormDoubleCoset.lean:190`]
[Yamaguchi2026]). -/
@[implicit_reducible]
private noncomputable def relativeNormDoubleCosetOrbitFintype
    (K K' S : ClosedSubgroup G)
    [Finite (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)] :
    Fintype (Quotient (orbitRel (K'.toSubgroup.subgroupOf K.toSubgroup)
      (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup))) := by
  letI := relativeNormDoubleCosetSigmaFintype K K' S
  exact Fintype.ofInjective
    (fun q => (⟨q, QuotientGroup.mk 1⟩ :
      Σ q : Quotient (orbitRel (K'.toSubgroup.subgroupOf K.toSubgroup)
        (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)),
        (K'.toSubgroup.subgroupOf K.toSubgroup) ⧸
          MulAction.stabilizer (K'.toSubgroup.subgroupOf K.toSubgroup) q.out)) (by
      intro q q' h
      exact congrArg Sigma.fst h)

/- Each stabilizer-coset space is finite ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/RelativeNormDoubleCoset.lean:208`]
[Yamaguchi2026]). -/
@[implicit_reducible]
private noncomputable def relativeNormDoubleCosetStabilizerFintype
    (K K' S : ClosedSubgroup G)
    [Finite (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)]
    (q : Quotient (orbitRel (K'.toSubgroup.subgroupOf K.toSubgroup)
      (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup))) :
    Fintype ((K'.toSubgroup.subgroupOf K.toSubgroup) ⧸
      MulAction.stabilizer (K'.toSubgroup.subgroupOf K.toSubgroup) q.out) := by
  letI := relativeNormDoubleCosetSigmaFintype K K' S
  exact Fintype.ofInjective
    (fun r => (⟨q, r⟩ :
      Σ q : Quotient (orbitRel (K'.toSubgroup.subgroupOf K.toSubgroup)
        (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)),
        (K'.toSubgroup.subgroupOf K.toSubgroup) ⧸
          MulAction.stabilizer (K'.toSubgroup.subgroupOf K.toSubgroup) q.out)) (by
      intro r r' h
      exact eq_of_heq (Sigma.mk.inj_iff.mp h).2)

/-- The double-coset norm formula with caller-supplied finite
enumerations of the orbit set and the stabilizer cosets — independent of
their ordering ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/RelativeNormDoubleCoset.lean:231`]
[Yamaguchi2026]). -/
theorem relativeNorm_eq_sum_doubleCoset_of_fintype
    (A : Rep ℤ G) (K K' S : ClosedSubgroup G)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)]
    [Fintype (Quotient (orbitRel (K'.toSubgroup.subgroupOf K.toSubgroup)
      (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)))]
    [(q : Quotient (orbitRel (K'.toSubgroup.subgroupOf K.toSubgroup)
      (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup))) →
      Fintype ((K'.toSubgroup.subgroupOf K.toSubgroup) ⧸
        MulAction.stabilizer (K'.toSubgroup.subgroupOf K.toSubgroup) q.out)]
    (a : ambientFixedAddSubgroup A S) :
    ((relativeNorm A K S hSK a : ambientFixedAddSubgroup A K) : A.V) =
      ∑ q, ∑ r, relativeCosetAction A K S hSK a
        ((relativeNormDoubleCosetEquiv K K' S).symm ⟨q, r⟩) := by
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)
  rw [relativeNorm_apply_coe, relativeNormValue]
  calc
    ∑ q, relativeCosetAction A K S hSK a q =
        ∑ p, relativeCosetAction A K S hSK a
          ((relativeNormDoubleCosetEquiv K K' S).symm p) :=
      ((relativeNormDoubleCosetEquiv K K' S).symm.sum_comp
        (relativeCosetAction A K S hSK a)).symm
    _ = ∑ q, ∑ r, relativeCosetAction A K S hSK a
        ((relativeNormDoubleCosetEquiv K K' S).symm ⟨q, r⟩) :=
      Fintype.sum_sigma _

/-- **The norm `N_{S/K}` reindexed first by intermediate-subgroup
orbits and then by stabilizer cosets** — the additive form of the
double-coset product decomposition behind transfer–norm naturality
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/RelativeNormDoubleCoset.lean:262`]
[Yamaguchi2026]). -/
theorem relativeNorm_eq_sum_doubleCoset
    (A : Rep ℤ G) (K K' S : ClosedSubgroup G)
    (hSK : S.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A S) :
    let Ω := Quotient (orbitRel (K'.toSubgroup.subgroupOf K.toSubgroup)
      (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup))
    letI : Fintype Ω :=
      relativeNormDoubleCosetOrbitFintype K K' S
    letI (q : Ω) : Fintype ((K'.toSubgroup.subgroupOf K.toSubgroup) ⧸
        MulAction.stabilizer (K'.toSubgroup.subgroupOf K.toSubgroup) q.out) :=
      relativeNormDoubleCosetStabilizerFintype K K' S q
    ((relativeNorm A K S hSK a : ambientFixedAddSubgroup A K) : A.V) =
      ∑ q, ∑ r, relativeCosetAction A K S hSK a
        ((relativeNormDoubleCosetEquiv K K' S).symm ⟨q, r⟩) := by
  dsimp only
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup)
  letI : Fintype (Quotient (orbitRel
      (K'.toSubgroup.subgroupOf K.toSubgroup)
      (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup))) :=
    relativeNormDoubleCosetOrbitFintype K K' S
  letI (q : Quotient (orbitRel (K'.toSubgroup.subgroupOf K.toSubgroup)
      (K.toSubgroup ⧸ S.toSubgroup.subgroupOf K.toSubgroup))) :
      Fintype ((K'.toSubgroup.subgroupOf K.toSubgroup) ⧸
        MulAction.stabilizer (K'.toSubgroup.subgroupOf K.toSubgroup) q.out) :=
    relativeNormDoubleCosetStabilizerFintype K K' S q
  exact relativeNorm_eq_sum_doubleCoset_of_fintype
    A K K' S hSK a

end relativeNormFormulas
end

end Atlas.Knowledge
