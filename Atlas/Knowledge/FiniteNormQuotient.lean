import Mathlib
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.InfiniteNormSubgroup
import Atlas.Knowledge.MaximalUnramifiedField

/-!
# finite norm quotient of an abstract extension

The target of the finite reciprocity equivalence: for a finite abstract
extension `L | K`, the quotient `A_K / N_{L|K} A_L` of the base fixed
coefficients by the image of the relative norm — a stable public type rather
than an abbreviation, with its class map, elimination and lifting principles,
and the torsion bound: every class is killed by the degree, because the norm
of an already-fixed element is its degree-fold sum — together with the
comparison from the maximal-unramified norm quotient, which carries the
maximal-unramified class to its finite-level class (#104).

## Main definitions

* `finiteNormSubgroup` / `FiniteNormQuotient` — the norm image and the
  quotient by it.
* `finiteNormClass` / `finiteNormQuotientLift` — the class map and descent.
* `DegreeData.fieldAsMaximalUnramifiedIntermediate` — `L` itself as a finite
  intermediate field of `L̃ | K`.
* `DegreeData.maximalUnramifiedToFiniteNormQuotient` — the canonical
  quotient map.

## Main statements

* `finiteNormClass_eq_zero_iff` — a class vanishes exactly on the norm
  subgroup; proved.
* `finiteNormQuotient_degree_nsmul_eq_zero` — the degree kills every class;
  proved.
* `DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormSubgroup` — the
  defining intersection is contained in the finite norm image; proved.
* `DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass`
  — the comparison carries class to class; proved.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The finite norm subgroup** `N_{L|K} A_L` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:28`). -/
def finiteNormSubgroup (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    AddSubgroup (ambientFixedAddSubgroup A K) :=
  (relativeNorm A K L hLK).range

/-- **The finite norm quotient** — a stable public object rather than an
abbreviation, so downstream APIs do not acquire a reducibility dependency on
the concrete quotient representation (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:39`). -/
def FiniteNormQuotient (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :=
  ambientFixedAddSubgroup A K ⧸ finiteNormSubgroup A K L hLK

/-- The additive group structure of the finite norm quotient, exported so
typeclass search does not unfold the stable type synonym (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:47`). -/
instance finiteNormQuotientAddCommGroup
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    AddCommGroup (FiniteNormQuotient A K L hLK) := by
  unfold FiniteNormQuotient
  infer_instance

/-- The canonical equivalence with the concrete quotient implementation
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:58`). -/
def finiteNormQuotientConcreteEquiv
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    FiniteNormQuotient A K L hLK ≃+
      ambientFixedAddSubgroup A K ⧸ finiteNormSubgroup A K L hLK := by
  unfold FiniteNormQuotient
  exact AddEquiv.refl _

/-- The canonical class map into the finite norm quotient (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:68`). -/
def finiteNormClassHom
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    ambientFixedAddSubgroup A K →+ FiniteNormQuotient A K L hLK := by
  unfold FiniteNormQuotient
  exact QuotientAddGroup.mk' (finiteNormSubgroup A K L hLK)

/-- The class of an element modulo the finite norm subgroup
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:77`). -/
def finiteNormClass
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A K) :
    FiniteNormQuotient A K L hLK :=
  finiteNormClassHom A K L hLK a

/-- The class map sends zero to zero (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:87`). -/
@[simp]
theorem finiteNormClass_zero
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    finiteNormClass A K L hLK 0 = 0 := by
  exact map_zero (finiteNormClassHom A K L hLK)

/-- Classes preserve addition of representatives (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:96`). -/
@[simp]
theorem finiteNormClass_add
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a b : ambientFixedAddSubgroup A K) :
    finiteNormClass A K L hLK (a + b) =
      finiteNormClass A K L hLK a + finiteNormClass A K L hLK b := by
  exact map_add (finiteNormClassHom A K L hLK) a b

/-- Classes preserve subtraction of representatives (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:107`). -/
@[simp]
theorem finiteNormClass_sub
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a b : ambientFixedAddSubgroup A K) :
    finiteNormClass A K L hLK (a - b) =
      finiteNormClass A K L hLK a - finiteNormClass A K L hLK b := by
  exact map_sub (finiteNormClassHom A K L hLK) a b

/-- Classes commute with natural scalars (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:118`). -/
@[simp]
theorem finiteNormClass_nsmul
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (n : ℕ) (a : ambientFixedAddSubgroup A K) :
    finiteNormClass A K L hLK (n • a) =
      n • finiteNormClass A K L hLK a := by
  exact map_nsmul (finiteNormClassHom A K L hLK) n a

/-- The concrete equivalence sends a class to its coset (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:129`). -/
@[simp]
theorem finiteNormQuotientConcreteEquiv_finiteNormClass
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A K) :
    finiteNormQuotientConcreteEquiv A K L hLK
        (finiteNormClass A K L hLK a) =
      QuotientAddGroup.mk' (finiteNormSubgroup A K L hLK) a := by
  rfl

/-- **A class vanishes exactly on the norm subgroup** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:141`). -/
@[simp]
theorem finiteNormClass_eq_zero_iff
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A K) :
    finiteNormClass A K L hLK a = 0 ↔
      a ∈ finiteNormSubgroup A K L hLK := by
  unfold finiteNormClass finiteNormClassHom FiniteNormQuotient
  exact QuotientAddGroup.eq_zero_iff _

/-- Every class has an ambient representative (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:152`). -/
theorem finiteNormClass_surjective
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    Function.Surjective (finiteNormClass A K L hLK) := by
  intro q
  change ambientFixedAddSubgroup A K ⧸
    finiteNormSubgroup A K L hLK at q
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
    (finiteNormSubgroup A K L hLK) q
  exact ⟨a, rfl⟩

/-- Eliminate a class through an ambient representative (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:166`). -/
@[elab_as_elim]
theorem FiniteNormQuotient.induction_on
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    {motive : FiniteNormQuotient A K L hLK → Prop}
    (q : FiniteNormQuotient A K L hLK)
    (h : ∀ a, motive (finiteNormClass A K L hLK a)) : motive q := by
  obtain ⟨a, rfl⟩ := finiteNormClass_surjective A K L hLK q
  exact h a

/-- Descend a homomorphism killing the norm subgroup (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:177`). -/
def finiteNormQuotientLift
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : finiteNormSubgroup A K L hLK ≤ f.ker) :
    FiniteNormQuotient A K L hLK →+ B := by
  unfold FiniteNormQuotient
  exact QuotientAddGroup.lift (finiteNormSubgroup A K L hLK) f hf

/-- The lift evaluates by the representative (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:190`). -/
@[simp]
theorem finiteNormQuotientLift_finiteNormClass
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : finiteNormSubgroup A K L hLK ≤ f.ker)
    (a : ambientFixedAddSubgroup A K) :
    finiteNormQuotientLift A K L hLK f hf
        (finiteNormClass A K L hLK a) = f a := by
  rfl

/-- **The degree kills every class**: the norm of an already-fixed element is
its degree-fold sum (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:205`). -/
theorem finiteNormQuotient_degree_nsmul_eq_zero
    (A : Rep ℤ G) (E : FiniteAbstractExtension G)
    (q : FiniteNormQuotient A E.base E.field E.below) :
    (E.degree : ℕ) • q = 0 := by
  refine FiniteNormQuotient.induction_on A E.base E.field E.below q ?_
  intro a
  unfold finiteNormClass
  rw [← map_nsmul]
  apply (finiteNormClass_eq_zero_iff A E.base E.field E.below _).2
  refine ⟨fixedFieldInclusion A E.base E.field E.below a, ?_⟩
  exact relativeNorm_fixedFieldInclusion A E a

/-- **`L` itself as a finite intermediate field of `L̃ | K`**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:226`). -/
def DegreeData.fieldAsMaximalUnramifiedIntermediate (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    FiniteIntermediateField (D.maximalUnramifiedField L) K where
  field := L
  above := D.maximalUnramifiedField_le L
  below := hLK
  finite := hfinite

/-- **The defining intersection for the infinite norm subgroup is
contained in the norm image from the particular finite field `L`**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:248`). -/
theorem DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormSubgroup
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    D.maximalUnramifiedNormSubgroup A K L ≤
      finiteNormSubgroup A K L hLK := by
  rw [D.maximalUnramifiedNormSubgroup_eq_infiniteNormSubgroup]
  rw [infiniteNormSubgroup]
  refine iInf_le_of_le (D.fieldAsMaximalUnramifiedIntermediate K L hLK) ?_
  rfl

/- The infinite norm subgroup lies in the kernel of the finite class map
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:259`). -/
private theorem
    DegreeData.maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    D.maximalUnramifiedNormSubgroup A K L ≤
      (finiteNormClassHom A K L hLK).ker := by
  intro a ha
  exact (finiteNormClass_eq_zero_iff A K L hLK a).2
    (D.maximalUnramifiedNormSubgroup_le_finiteNormSubgroup A K L hLK ha)

/-- **The canonical quotient map**
`A_K / N_{L̃|K} A_{L̃} →+ A_K / N_{L|K} A_L`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:271`). -/
def DegreeData.maximalUnramifiedToFiniteNormQuotient
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    D.MaximalUnramifiedNormQuotient A K L →+
      FiniteNormQuotient A K L hLK :=
  D.maximalUnramifiedNormQuotientLift A K L
    (finiteNormClassHom A K L hLK)
    (D.maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker A K L hLK)

/-- **The comparison to a finite norm quotient carries the
maximal-unramified class to its finite-level class** (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean:284`). -/
@[simp]
theorem
    DegreeData.maximalUnramifiedToFiniteNormQuotient_maximalUnramifiedNormClass
    (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A K) :
    D.maximalUnramifiedToFiniteNormQuotient A K L hLK
        (D.maximalUnramifiedNormClass A K L a) =
      finiteNormClass A K L hLK a := by
  exact D.maximalUnramifiedNormQuotientLift_maximalUnramifiedNormClass
    A K L (finiteNormClassHom A K L hLK)
    (D.maximalUnramifiedNormSubgroup_le_finiteNormClassHom_ker A K L hLK) a

end

end Atlas.Knowledge
