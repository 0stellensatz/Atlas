import Mathlib
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteResidueAbstractExtension

/-!
# normalized degree and the Frobenius

For a field of finite residue degree, the normalized degree `d_K = (1/f_K)·d`:
division happens only after the identification `d(G_K) = f_K·ℤ̂`, which the
classification of finite-index subgroups of `ℤ̂` supplies. The normalized degree
is surjective with kernel exactly the field's inertia, so it descends to the
isomorphism `G(K̃|K) ≃ ℤ̂`, and the Frobenius over `K` is the unique class of
normalized degree one. Restriction along a finite extension raises the Frobenius
to the relative residue degree: `φ_L|_K̃ = φ_K^{f_{L|K}}`.

## Main definitions

* `DegreeData.normalizedDegree` — `d_K = (1/f_K)·d`, continuous.
* `DegreeData.maximalUnramifiedDegreeEquiv` — `G_K/I_K ≃* ℤ̂`.
* `DegreeData.frobenius` — the class with `d_K(φ_K) = 1`.
* `DegreeData.maximalUnramifiedRestriction` — restriction of maximal-unramified
  Galois groups along an extension.

## Main statements

* `DegreeData.normalizedDegree_surjective` /
  `DegreeData.normalizedDegree_ker` — image everything, kernel the inertia;
  proved.
* `DegreeData.eq_frobenius_iff` — the uniqueness clause; proved.
* `FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree` —
  `f_{L|K} · f_K = f_L`; proved.
* `DegreeData.frobenius_restriction_eq_power` — `φ_L|_K̃ = φ_K^{f_{L|K}}`;
  proved.

## Implementation notes

The raw degree of a field element is first placed in `f_K·ℤ̂` through
`Atlas.Knowledge.ProfiniteInteger.spanAddSubgroup` and the classification of
finite-index subgroups, and `Atlas.Knowledge.ProfiniteInteger.divide` performs
the normalization; the defining identity `f_K·d_K = d` is the inverse law of the
division. The source's `zHatMulNat` bundling is read as `nsmul`/`natCast`
multiplication throughout, as in the `ℤ̂` item.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The degree image, written additively** in `ℤ̂`
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Frobenius.lean:20`][Yamaguchi2026]). -/
def fieldImageAdd (D : DegreeData G) (K : ClosedSubgroup G) :
    AddSubgroup ProfiniteInteger :=
  Subgroup.toAddSubgroup' (D.fieldImage K)

/-- The additive degree image has index the positive residue degree. -/
@[simp]
theorem fieldImageAdd_index (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    (D.fieldImageAdd K.field).index = (K.residueDegree : ℕ) := by
  change (D.fieldImage K.field).index = (K.residueDegree : ℕ)
  rw [← Subgroup.relIndex_top_right]
  change Nat.card (D.residueQuotient K.field) = (K.residueDegree : ℕ)
  exact K.residueDegree_coe.symm

/-- **Finite residue degree identifies `d(G_K)` with `f_K·ℤ̂`** — the
classification of finite-index subgroups of `ℤ̂` read at the degree image
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Frobenius.lean:34`][Yamaguchi2026]). -/
theorem fieldImageAdd_eq_spanAddSubgroup (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    D.fieldImageAdd K.field =
      ProfiniteInteger.spanAddSubgroup (K.residueDegree : ℕ) := by
  have h := ProfiniteInteger.addSubgroup_eq_spanAddSubgroup_of_index_ne_zero
    (D.fieldImageAdd K.field)
    (by rw [D.fieldImageAdd_index K]; exact K.residueDegree.pos.ne')
  rwa [D.fieldImageAdd_index K] at h

/-- The raw value `d(k)` as an element of `f_K·ℤ̂`. -/
def restrictedDegreeInSpan (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    ProfiniteInteger.spanAddSubgroup (K.residueDegree : ℕ) := by
  refine ⟨(D.degree k.1).toAdd, ?_⟩
  rw [← D.fieldImageAdd_eq_spanAddSubgroup K]
  change D.degree k.1 ∈ D.fieldImage K.field
  exact ⟨k, rfl⟩

/-- The placed value has the original additive coordinate. -/
@[simp]
theorem restrictedDegreeInSpan_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.toSubgroup) :
    (D.restrictedDegreeInSpan K k).1 = (D.degree k.1).toAdd :=
  rfl

/-- **The normalized degree** `d_K = (1/f_K)·d`
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Frobenius.lean:59`][Yamaguchi2026]). -/
def normalizedDegree (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    K.field.toSubgroup →ₜ* ProfiniteIntegerMul where
  toFun k := Multiplicative.ofAdd
    (ProfiniteInteger.divide (K.residueDegree : ℕ)
      (D.restrictedDegreeInSpan K k))
  map_one' := by
    apply Multiplicative.ext
    change ProfiniteInteger.divide (K.residueDegree : ℕ)
      (D.restrictedDegreeInSpan K 1) = 0
    rw [show D.restrictedDegreeInSpan K 1 = 0 by
      apply Subtype.ext
      simp]
    exact map_zero (ProfiniteInteger.divide (K.residueDegree : ℕ))
  map_mul' x y := by
    apply Multiplicative.ext
    change ProfiniteInteger.divide (K.residueDegree : ℕ)
        (D.restrictedDegreeInSpan K (x * y)) =
      ProfiniteInteger.divide (K.residueDegree : ℕ)
          (D.restrictedDegreeInSpan K x) +
        ProfiniteInteger.divide (K.residueDegree : ℕ)
          (D.restrictedDegreeInSpan K y)
    rw [show D.restrictedDegreeInSpan K (x * y) =
        D.restrictedDegreeInSpan K x + D.restrictedDegreeInSpan K y by
      apply Subtype.ext
      exact congrArg Multiplicative.toAdd (map_mul D.degree x.1 y.1)]
    exact map_add (ProfiniteInteger.divide (K.residueDegree : ℕ)) _ _
  continuous_toFun := by
    apply (map_continuous
      (ProfiniteInteger.divide (K.residueDegree : ℕ))).comp
    exact Continuous.subtype_mk
      (D.restrictedDegree K.field).continuous_toFun
      (fun k => (D.restrictedDegreeInSpan K k).2)

/-- The additive coordinate of the normalized degree is the divided value. -/
@[simp]
theorem normalizedDegree_apply_toAdd (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    (D.normalizedDegree K k).toAdd =
      ProfiniteInteger.divide (K.residueDegree : ℕ)
        (D.restrictedDegreeInSpan K k) :=
  rfl

/-- **The defining identity** `f_K·d_K = d`. -/
theorem residueDegree_nsmul_normalizedDegree (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd =
      (D.degree k.1).toAdd := by
  rw [normalizedDegree_apply_toAdd, nsmul_eq_mul]
  exact ProfiniteInteger.mul_divide (K.residueDegree : ℕ)
    (D.restrictedDegreeInSpan K k)

/-- **The normalized degree is surjective**
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Frobenius.lean:112`][Yamaguchi2026]). -/
theorem normalizedDegree_surjective (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    Function.Surjective (D.normalizedDegree K) := by
  intro z
  have hzImageAdd : (K.residueDegree : ℕ) • z.toAdd ∈
      D.fieldImageAdd K.field := by
    rw [D.fieldImageAdd_eq_spanAddSubgroup K]
    refine (ProfiniteInteger.mem_spanAddSubgroup_iff _).mpr ⟨z.toAdd, ?_⟩
    rw [nsmul_eq_mul]
  have hzImage : Multiplicative.ofAdd ((K.residueDegree : ℕ) • z.toAdd) ∈
      D.fieldImage K.field := hzImageAdd
  obtain ⟨k, hk⟩ := hzImage
  refine ⟨k, ?_⟩
  apply Multiplicative.ext
  apply ProfiniteInteger.nsmul_left_injective K.residueDegree.pos.ne'
  change (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd =
    (K.residueDegree : ℕ) • z.toAdd
  rw [D.residueDegree_nsmul_normalizedDegree K k]
  exact congrArg Multiplicative.toAdd hk

/-- **The kernel of the normalized degree is the inertia**
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Frobenius.lean:132`][Yamaguchi2026]). -/
theorem normalizedDegree_ker (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    (D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field := by
  ext k
  constructor
  · intro hk
    change D.degree k.1 = 1
    apply Multiplicative.ext
    rw [← D.residueDegree_nsmul_normalizedDegree K k]
    change (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd = 0
    rw [show D.normalizedDegree K k = 1 from hk]
    simp
  · intro hk
    apply Multiplicative.ext
    apply ProfiniteInteger.nsmul_left_injective K.residueDegree.pos.ne'
    change (K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd =
      (K.residueDegree : ℕ) • (1 : ProfiniteIntegerMul).toAdd
    rw [D.residueDegree_nsmul_normalizedDegree K k]
    rw [show D.degree k.1 = 1 from hk]
    simp

private theorem fieldInertiaWithin_le_normalizedDegree_ker
    (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    D.fieldInertiaWithin K.field ≤ (D.normalizedDegree K).toMonoidHom.ker := by
  rw [D.normalizedDegree_ker K]

/-- **The isomorphism** `d_K : G(K̃|K) ≃ ℤ̂`
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Frobenius.lean:159`][Yamaguchi2026]). -/
def maximalUnramifiedDegreeEquiv (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) ≃* ProfiniteIntegerMul := by
  let dquot : (K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) →*
      ProfiniteIntegerMul :=
    QuotientGroup.lift (D.fieldInertiaWithin K.field)
      (D.normalizedDegree K).toMonoidHom
      (D.fieldInertiaWithin_le_normalizedDegree_ker K)
  apply MulEquiv.ofBijective dquot
  constructor
  · intro x y hxy
    refine Quotient.inductionOn₂' x y ?_ hxy
    intro a b hab
    apply QuotientGroup.eq.mpr
    change a⁻¹ * b ∈ D.fieldInertiaWithin K.field
    rw [← D.normalizedDegree_ker K]
    change D.normalizedDegree K (a⁻¹ * b) = 1
    rw [map_mul, map_inv]
    have hab' : D.normalizedDegree K a = D.normalizedDegree K b := by
      simpa [dquot] using hab
    rw [hab', inv_mul_cancel]
  · exact QuotientGroup.lift_surjective_of_surjective
      (D.fieldInertiaWithin K.field)
      (D.normalizedDegree K).toMonoidHom
      (D.normalizedDegree_surjective K)
      (D.fieldInertiaWithin_le_normalizedDegree_ker K)

/-- The equivalence computes on representatives as the normalized degree. -/
@[simp]
theorem maximalUnramifiedDegreeEquiv_mk (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) :
    D.maximalUnramifiedDegreeEquiv K (QuotientGroup.mk k) =
      D.normalizedDegree K k :=
  rfl

/-- **The Frobenius over `K`**: the unique class with `d_K(φ_K) = 1`
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Frobenius.lean:195`][Yamaguchi2026]). -/
def frobenius (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field :=
  (D.maximalUnramifiedDegreeEquiv K).symm
    (Multiplicative.ofAdd (1 : ProfiniteInteger))

/-- The equivalence sends the Frobenius to the generator. -/
@[simp]
theorem maximalUnramifiedDegreeEquiv_frobenius (D : DegreeData G)
    (K : FiniteResidueAbstractField D) :
    D.maximalUnramifiedDegreeEquiv K (D.frobenius K) =
      Multiplicative.ofAdd (1 : ProfiniteInteger) :=
  (D.maximalUnramifiedDegreeEquiv K).apply_symm_apply _

/-- **The uniqueness clause of the Frobenius**
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Frobenius.lean:209`][Yamaguchi2026]). -/
theorem eq_frobenius_iff (D : DegreeData G)
    (K : FiniteResidueAbstractField D)
    (σ : K.field.toSubgroup ⧸ D.fieldInertiaWithin K.field) :
    σ = D.frobenius K ↔
      D.maximalUnramifiedDegreeEquiv K σ =
        Multiplicative.ofAdd (1 : ProfiniteInteger) := by
  constructor
  · rintro rfl
    exact D.maximalUnramifiedDegreeEquiv_frobenius K
  · intro h
    exact (D.maximalUnramifiedDegreeEquiv K).injective
      (h.trans (D.maximalUnramifiedDegreeEquiv_frobenius K).symm)

end DegreeData

/-- **Residue degrees multiply to the absolute one**: `f_{L|K} · f_K = f_L`
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Frobenius.lean:224`][Yamaguchi2026]). -/
theorem FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree
    (D : DegreeData G) (E : FiniteResidueAbstractExtension D) :
    (E.residueDegree : ℕ) * (E.base.residueDegree : ℕ) =
      (E.field.residueDegree : ℕ) := by
  have h :=
    AbstractExtension.relativeResidueDegreeCardinal_mul_residueDegreeCardinal
      E.toFiniteAbstractExtension.toAbstractExtension D
  rw [E.toFiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe D] at h
  change ((E.residueDegree : ℕ) : Cardinal) *
      D.residueDegreeCardinal E.base.field =
    D.residueDegreeCardinal E.field.field at h
  rw [E.base.residueDegreeCardinal_eq_coe,
    E.field.residueDegreeCardinal_eq_coe] at h
  exact_mod_cast h

namespace DegreeData

/-- The relative residue degree is the quotient of the absolute ones. -/
theorem frobeniusRestrictionNaturality_residueDegree (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) :
    (E.residueDegree : ℕ) =
      (E.field.residueDegree : ℕ) / (E.base.residueDegree : ℕ) := by
  rw [← E.residueDegree_mul_absoluteResidueDegree D]
  rw [Nat.mul_comm (E.residueDegree : ℕ) (E.base.residueDegree : ℕ)]
  exact (Nat.mul_div_cancel_left _ E.base.residueDegree.property).symm

/-- **The commutative square on `G_L`**: `d_K = f_{L|K}·d_L`
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Frobenius.lean:251`][Yamaguchi2026]). -/
theorem frobeniusRestrictionNaturality_normalizedDegree (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D)
    (l : E.field.field.toSubgroup) :
    (D.normalizedDegree E.base (Subgroup.inclusion E.below l)).toAdd =
      (E.residueDegree : ℕ) • (D.normalizedDegree E.field l).toAdd := by
  apply ProfiniteInteger.nsmul_left_injective E.base.residueDegree.pos.ne'
  change (E.base.residueDegree : ℕ) •
      (D.normalizedDegree E.base (Subgroup.inclusion E.below l)).toAdd =
    (E.base.residueDegree : ℕ) •
      ((E.residueDegree : ℕ) • (D.normalizedDegree E.field l).toAdd)
  rw [D.residueDegree_nsmul_normalizedDegree E.base]
  change (D.degree l.1).toAdd = _
  rw [smul_smul, Nat.mul_comm (E.base.residueDegree : ℕ),
    E.residueDegree_mul_absoluteResidueDegree D,
    D.residueDegree_nsmul_normalizedDegree E.field]

private theorem fieldInertiaWithin_le_comap_inclusion
    (D : DegreeData G) {L K : ClosedSubgroup G}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    D.fieldInertiaWithin L ≤
      (D.fieldInertiaWithin K).comap (Subgroup.inclusion hLK) := by
  intro l hl
  exact hl

/-- **Restriction** `G(L̃|L) → G(K̃|K)` for `L | K`
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Frobenius.lean:278`][Yamaguchi2026]). -/
def maximalUnramifiedRestriction (D : DegreeData G) {L K : ClosedSubgroup G}
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    (L.toSubgroup ⧸ D.fieldInertiaWithin L) →*
      (K.toSubgroup ⧸ D.fieldInertiaWithin K) :=
  QuotientGroup.map (D.fieldInertiaWithin L) (D.fieldInertiaWithin K)
    (Subgroup.inclusion hLK) (D.fieldInertiaWithin_le_comap_inclusion hLK)

/-- Restriction computes on representatives. -/
@[simp]
theorem maximalUnramifiedRestriction_mk (D : DegreeData G)
    {L K : ClosedSubgroup G} (hLK : L.toSubgroup ≤ K.toSubgroup)
    (l : L.toSubgroup) :
    D.maximalUnramifiedRestriction hLK (QuotientGroup.mk l) =
      QuotientGroup.mk (Subgroup.inclusion hLK l) :=
  rfl

/-- The quotient form of the commutative square. -/
theorem frobeniusRestrictionNaturality_quotient_square (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D)
    (σ : E.field.field.toSubgroup ⧸ D.fieldInertiaWithin E.field.field) :
    (D.maximalUnramifiedDegreeEquiv E.base
      (D.maximalUnramifiedRestriction E.below σ)).toAdd =
      (E.residueDegree : ℕ) •
        (D.maximalUnramifiedDegreeEquiv E.field σ).toAdd := by
  refine Quotient.inductionOn' σ ?_
  intro l
  simpa using D.frobeniusRestrictionNaturality_normalizedDegree E l

/-- **Frobenius restriction is a power**: `φ_L|_K̃ = φ_K^{f_{L|K}}`
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Frobenius.lean:309`][Yamaguchi2026]). -/
theorem frobenius_restriction_eq_power (D : DegreeData G)
    (E : FiniteResidueAbstractExtension D) :
    D.maximalUnramifiedRestriction E.below (D.frobenius E.field) =
      (D.frobenius E.base) ^ (E.residueDegree : ℕ) := by
  apply (D.maximalUnramifiedDegreeEquiv E.base).injective
  apply Multiplicative.ext
  rw [map_pow]
  change (D.maximalUnramifiedDegreeEquiv E.base
      (D.maximalUnramifiedRestriction E.below
        (D.frobenius E.field))).toAdd =
    (E.residueDegree : ℕ) •
      (D.maximalUnramifiedDegreeEquiv E.base
        (D.frobenius E.base)).toAdd
  rw [D.frobeniusRestrictionNaturality_quotient_square E,
    D.maximalUnramifiedDegreeEquiv_frobenius,
    D.maximalUnramifiedDegreeEquiv_frobenius]

end DegreeData

end

end Atlas.Knowledge
