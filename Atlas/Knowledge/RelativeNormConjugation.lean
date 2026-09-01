import Mathlib
import Atlas.Knowledge.RelativeNormLaws

/-!
# conjugation of relative norms

The relative-base conjugation laws: conjugation preserves inclusions of
abstract fields, identifies a field's subgroup with its conjugate's by
`k ↦ s⁻¹ks`, carries the relative subgroup of `L | K` to that of
`L^s | K^s`, and so identifies the relative coset spaces — multiplicatively
when the extension is Galois, where it is the left vertical of the
norm–conjugation naturality diagram. On coefficients, relative norms
commute with conjugation: `N_{L^s|K^s}(a^s) = N_{L|K}(a)^s` (#104).

## Main definitions

* `conjugateSubgroupEquiv` — `G_K ≃* G_{K^s}` by `k ↦ s⁻¹ks`.
* `relativeConjugateCosetEquiv` /
  `finiteReciprocityNaturalityConjugation` — the coset-space
  identification, plain and multiplicative.

## Main statements

* `map_extensionSubgroup_conjugate` — the relative subgroup maps onto the
  conjugate's; proved.
* `conjugateExtension_normal` / `finite_conjugateExtension` — a conjugate
  of a Galois extension is Galois, of a finite one finite; proved.
* `relativeNorm_conjugate_apply` — `N_{L^s|K^s}(a^s) = N_{L|K}(a)^s`;
  proved.

## Implementation notes

The relative subgroup is the `subgroupOf` spelling, as across the arc, and
seven of the source's statements carry their containment `L ≤ K` only
inside the source's `extensionSubgroup` spelling, so the hypothesis drops
out of them here; the conjugate extension's normality stays an instance,
its head fully determined without it. The layer's `QuotientGroup.congr`
and `congr_mk'` take the subgroups explicitly and are called accordingly.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Conjugation preserves inclusions of abstract fields ([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormConjugation.lean:28`]
[Yamaguchi2026]). -/
theorem conjugateClosedSubgroup_mono [ContinuousMul G]
    {K L : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (s : G) :
    (conjugateClosedSubgroup L s).toSubgroup ≤
      (conjugateClosedSubgroup K s).toSubgroup := by
  intro x hx
  change x ∈ conjugateClosedSubgroup L s at hx
  change x ∈ conjugateClosedSubgroup K s
  rw [conjugateClosedSubgroup_mem] at hx ⊢
  exact hLK hx

/-- **Conjugation identifies a field's subgroup with its right conjugate's**
by `k ↦ s⁻¹ks` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormConjugation.lean:41`]
[Yamaguchi2026]). -/
def conjugateSubgroupEquiv [ContinuousMul G]
    (K : ClosedSubgroup G) (s : G) :
    K.toSubgroup ≃* (conjugateClosedSubgroup K s).toSubgroup where
  toFun k := ⟨s⁻¹ * k.1 * s, by
    change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup K s
    rw [conjugateClosedSubgroup_mem]
    convert k.2 using 1
    simp [mul_assoc]⟩
  invFun x := ⟨s * x.1 * s⁻¹,
    (conjugateClosedSubgroup_mem K s x.1).mp x.2⟩
  left_inv k := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

/-- The conjugating equivalence reads as `k ↦ s⁻¹ks`. -/
@[simp]
theorem conjugateSubgroupEquiv_apply_coe [ContinuousMul G]
    (K : ClosedSubgroup G) (s : G) (k : K.toSubgroup) :
    (conjugateSubgroupEquiv K s k).1 = s⁻¹ * k.1 * s :=
  rfl

/-- **The relative subgroup of `L | K` maps onto that of `L^s | K^s`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormConjugation.lean:70`]
[Yamaguchi2026]). -/
theorem map_extensionSubgroup_conjugate [ContinuousMul G]
    (K L : ClosedSubgroup G) (s : G) :
    (L.toSubgroup.subgroupOf K.toSubgroup).map
        (conjugateSubgroupEquiv K s).toMonoidHom =
      (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
        (conjugateClosedSubgroup K s).toSubgroup := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    change s⁻¹ * k.1 * s ∈ conjugateClosedSubgroup L s
    rw [conjugateClosedSubgroup_mem]
    have hk' : (k : G) ∈ L := Subgroup.mem_subgroupOf.1 hk
    simpa [mul_assoc] using hk'
  · intro hx
    refine ⟨(conjugateSubgroupEquiv K s).symm x, ?_, ?_⟩
    · change s * x.1 * s⁻¹ ∈ L.toSubgroup
      exact (conjugateClosedSubgroup_mem L s x.1).mp hx
    · exact (conjugateSubgroupEquiv K s).apply_symm_apply x

/-- **Conjugation identifies the relative coset spaces**, Galois or not
([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormConjugation.lean:92`]
[Yamaguchi2026]). -/
noncomputable def relativeConjugateCosetEquiv [ContinuousMul G]
    (K L : ClosedSubgroup G) (s : G) :
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) ≃
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
          (conjugateClosedSubgroup K s).toSubgroup) :=
  Quotient.congr (conjugateSubgroupEquiv K s).toEquiv (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply]
    let e := conjugateSubgroupEquiv K s
    let H := L.toSubgroup.subgroupOf K.toSubgroup
    let Hs := (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
      (conjugateClosedSubgroup K s).toSubgroup
    have hmap : H.map e.toMonoidHom = Hs :=
      map_extensionSubgroup_conjugate K L s
    change x⁻¹ * y ∈ H ↔ (e x)⁻¹ * e y ∈ Hs
    rw [← hmap]
    constructor
    · intro hxy
      refine ⟨x⁻¹ * y, hxy, ?_⟩
      simp
    · rintro ⟨z, hz, hez⟩
      have heq : z = x⁻¹ * y := by
        apply e.injective
        simpa using hez
      simpa [heq] using hz)

/-- The coset identification computes on representatives. -/
@[simp]
theorem relativeConjugateCosetEquiv_mk [ContinuousMul G]
    (K L : ClosedSubgroup G) (s : G)
    (k : K.toSubgroup) :
    relativeConjugateCosetEquiv K L s (QuotientGroup.mk k) =
      QuotientGroup.mk (conjugateSubgroupEquiv K s k) :=
  rfl

/-- **A conjugate of a Galois extension is Galois** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormConjugation.lean:136`]
[Yamaguchi2026]). -/
instance conjugateExtension_normal [ContinuousMul G]
    (K L : ClosedSubgroup G) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    ((conjugateClosedSubgroup L s).toSubgroup.subgroupOf
      (conjugateClosedSubgroup K s).toSubgroup).Normal := by
  rw [← map_extensionSubgroup_conjugate K L s]
  exact Subgroup.Normal.map hLnormal
    (conjugateSubgroupEquiv K s).toMonoidHom
    (conjugateSubgroupEquiv K s).surjective

/-- **The left vertical of the norm–conjugation naturality diagram**:
`τ ↦ s⁻¹τs` on the Galois quotients ([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormConjugation.lean:150`]
[Yamaguchi2026]). -/
noncomputable def finiteReciprocityNaturalityConjugation
    [ContinuousMul G] (K L : ClosedSubgroup G) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) ≃*
      ((conjugateClosedSubgroup K s).toSubgroup ⧸
        (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
          (conjugateClosedSubgroup K s).toSubgroup) :=
  QuotientGroup.congr _ _
    (conjugateSubgroupEquiv K s)
    (map_extensionSubgroup_conjugate K L s)

/-- The multiplicative identification computes on representatives. -/
@[simp]
theorem finiteReciprocityNaturalityConjugation_mk [ContinuousMul G]
    (K L : ClosedSubgroup G) (s : G)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup) :
    finiteReciprocityNaturalityConjugation K L s
        (QuotientGroup.mk k) =
      QuotientGroup.mk (conjugateSubgroupEquiv K s k) :=
  rfl

/-- **A conjugate of a finite extension is finite** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormConjugation.lean:182`]
[Yamaguchi2026]). -/
theorem finite_conjugateExtension [ContinuousMul G]
    (K L : ClosedSubgroup G) (s : G)
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
        (conjugateClosedSubgroup K s).toSubgroup) :=
  Finite.of_equiv
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (relativeConjugateCosetEquiv K L s)

/- Conjugation intertwines the two relative coset actions
([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormConjugation.lean:203`]
[Yamaguchi2026]). -/
private theorem relativeCosetAction_conjugate
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    (a : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :
    relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A L s a)
        (relativeConjugateCosetEquiv K L s q) =
      A.ρ s⁻¹ (relativeCosetAction A K L hLK a q) := by
  refine Quotient.inductionOn' q ?_
  intro k
  rw [relativeConjugateCosetEquiv_mk, relativeCosetAction_mk,
    relativeCosetAction_mk, conjugateFixedElement_coe]
  calc
    A.ρ (s⁻¹ * k.1 * s) (A.ρ s⁻¹ a.1) =
        A.ρ ((s⁻¹ * k.1 * s) * s⁻¹) a.1 := by
      have hm := congrArg (fun φ => φ a.1)
        (map_mul A.ρ (s⁻¹ * k.1 * s) s⁻¹)
      exact hm.symm
    _ = A.ρ (s⁻¹ * k.1) a.1 := by
      congr 2
      simp [mul_assoc]
    _ = A.ρ s⁻¹ (A.ρ k.1 a.1) := by
      exact congrArg (fun φ => φ a.1) (map_mul A.ρ s⁻¹ k.1)

/-- **Relative norms commute with conjugation**:
`N_{L^s|K^s}(a^s) = N_{L|K}(a)^s` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormConjugation.lean:234`]
[Yamaguchi2026]). -/
theorem relativeNorm_conjugate_apply
    [ContinuousMul G] (A : Rep ℤ G)
    (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) (s : G)
    [hLfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A L) :
    letI : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
        (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
          (conjugateClosedSubgroup K s).toSubgroup) :=
      finite_conjugateExtension K L s
    relativeNorm A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s)
        (conjugateClosedSubgroup_mono hLK s)
        (conjugateFixedElement A L s a) =
      conjugateFixedElement A K s (relativeNorm A K L hLK a) := by
  let hConj := conjugateClosedSubgroup_mono hLK s
  letI hConjFinite : Finite ((conjugateClosedSubgroup K s).toSubgroup ⧸
      (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
        (conjugateClosedSubgroup K s).toSubgroup) :=
    finite_conjugateExtension K L s
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
  letI := Fintype.ofFinite
    ((conjugateClosedSubgroup K s).toSubgroup ⧸
      (conjugateClosedSubgroup L s).toSubgroup.subgroupOf
        (conjugateClosedSubgroup K s).toSubgroup)
  let e := relativeConjugateCosetEquiv K L s
  apply Subtype.ext
  simp only [relativeNorm_apply_coe, relativeNormValue,
    conjugateFixedElement_coe]
  calc
    ∑ q, relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConj
        (conjugateFixedElement A L s a) q =
      ∑ q, relativeCosetAction A (conjugateClosedSubgroup K s)
        (conjugateClosedSubgroup L s) hConj
        (conjugateFixedElement A L s a) (e q) := by
          exact (e.sum_comp fun q =>
            relativeCosetAction A (conjugateClosedSubgroup K s)
              (conjugateClosedSubgroup L s) hConj
              (conjugateFixedElement A L s a) q).symm
    _ = ∑ q, A.ρ s⁻¹ (relativeCosetAction A K L hLK a q) := by
      apply Finset.sum_congr rfl
      intro q _
      exact relativeCosetAction_conjugate A K L hLK s a q
    _ = A.ρ s⁻¹ (∑ q, relativeCosetAction A K L hLK a q) := by
      rw [map_sum]

end

end Atlas.Knowledge
