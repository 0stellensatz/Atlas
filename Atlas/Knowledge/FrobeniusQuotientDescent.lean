import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusQuotientAction
import Atlas.Knowledge.InertiaQuotientDegreeKernel
import Atlas.Knowledge.InfiniteNormSubgroup
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.NormalizedDegree
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.UniversalNormDescent

/-!
# Frobenius quotient descent

The Frobenius quotient representation — the actual `G(L̃/K)`-action on
`A_{L̃}` as a `Rep ℤ` object — with its Birkhoff sums identified as
Frobenius power sums, the norm and degree-zero fixedness lemmas that
apply `N_{L̃/K̃}` to equation `(*)`, and the finite-support descent from
the maximal unramified field down to `K` (#104).

## Main definitions

* `DegreeData.frobeniusQuotientRepresentation` — the quotient action as
  a representation.

## Main statements

* `DegreeData.birkhoffSum_eq_frobeniusPowerSum` — Birkhoff sums of the
  quotient action are Frobenius power sums; proved.
* `DegreeData.maximalUnramifiedNorm_fixed_of_hstar` — applying
  `N_{L̃/K̃}` to `(*)` kills the degree-zero differences, so the norm of
  `u` is Frobenius-fixed; proved.
* `DegreeData.descend_maximalUnramified_fixed_of_finiteSupport` — a
  `K̃`-fixed element with finite Galois support fixed by a degree-one
  Frobenius lift descends to `K`; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`ZHat` is `ProfiniteInteger`, and the ambient group is `Type` because
the file leans on the iterate lemmas of
`Atlas.Knowledge.UniversalNormDescent`, whose item fixed `Type` after
the layer's Tate apparatus — the source's universe module-comment is
absorbed here, and its no-op `open`s are dropped, along with the descent
theorem's `IsTopologicalGroup` binder, which fed no callee. The
finiteness of `L̃/K̃` is #138's form, called without the containment the
source passes.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe v

variable {G : Type} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- Underlying coefficient of the actual quotient action, expressed
through the chosen quotient representative ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusQuotientDescent.lean:35`]
[Yamaguchi2026]). -/
theorem frobeniusQuotientAction_coe_out (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    (D.frobeniusQuotientAction A K L hLK q a).1 =
      A.ρ (Quotient.out q).1 a.1 := by
  let k : K.toSubgroup := Quotient.out q
  have hkq : (QuotientGroup.mk k :
      K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) = q :=
    Quotient.out_eq' q
  calc
    (D.frobeniusQuotientAction A K L hLK q a).1 =
        (D.frobeniusQuotientAction A K L hLK (QuotientGroup.mk k) a).1 :=
      congrArg
        (fun z => (D.frobeniusQuotientAction A K L hLK z a).1) hkq.symm
    _ = A.ρ k.1 a.1 := rfl
    _ = A.ρ (Quotient.out q).1 a.1 := rfl

/-- The linear action of `G(L̃/K)` on `A_{L̃}` — the concrete quotient
action packaged for the Tate-cohomology calculation ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusQuotientDescent.lean:56`]
[Yamaguchi2026]). -/
noncomputable def frobeniusQuotientActionLinearMap (D : DegreeData G)
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) :
    ambientFixedAddSubgroup A (D.maximalUnramifiedField L) →ₗ[ℤ]
      ambientFixedAddSubgroup A (D.maximalUnramifiedField L) where
  toFun := D.frobeniusQuotientAction A K L hLK q
  map_add' a b := by
    refine Quotient.inductionOn' q ?_
    intro k
    apply Subtype.ext
    change A.ρ k.1 (a.1 + b.1) = A.ρ k.1 a.1 + A.ρ k.1 b.1
    exact map_add (A.ρ k.1) _ _
  map_smul' n a := by
    refine Quotient.inductionOn' q ?_
    intro k
    apply Subtype.ext
    change A.ρ k.1 (n • a.1) = n • A.ρ k.1 a.1
    exact map_zsmul (A.ρ k.1) n a.1

/-- **The actual `G(L̃/K)`-representation on `A_{L̃}`** used in the
universal norm-descent lemma ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusQuotientDescent.lean:79`]
[Yamaguchi2026]). -/
noncomputable def frobeniusQuotientRepresentation (D : DegreeData G)
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    Rep ℤ (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) :=
  Rep.of
    { toFun := D.frobeniusQuotientActionLinearMap A K L hLK
      map_one' := by
        ext a
        change A.ρ (1 : G) a.1 = a.1
        simp
      map_mul' := by
        intro q r
        refine Quotient.inductionOn₂' q r ?_
        intro k l
        ext a
        change A.ρ (k.1 * l.1) a.1 = A.ρ k.1 (A.ρ l.1 a.1)
        rw [map_mul]
        rfl }

/-- The Frobenius quotient representation evaluates by the chosen
quotient action. -/
@[simp]
theorem frobeniusQuotientRepresentation_apply (D : DegreeData G)
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    (D.frobeniusQuotientRepresentation A K L hLK).ρ q a =
      D.frobeniusQuotientAction A K L hLK q a :=
  rfl

/-- **The Birkhoff sum of the quotient action is the corresponding sum of
Frobenius powers** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusQuotientDescent.lean:112`]
[Yamaguchi2026]). -/
theorem birkhoffSum_eq_frobeniusPowerSum (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    birkhoffSum
        ((D.frobeniusQuotientRepresentation A K L hLK).ρ φ) id n a =
      D.frobeniusPowerSum A K L hLK φ n a := by
  unfold birkhoffSum frobeniusPowerSum
  rw [Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [id_eq, Finset.mem_range.mp hi, dite_true]
  calc
    (((D.frobeniusQuotientRepresentation A K L hLK).ρ φ)^[i]) a =
        (D.frobeniusQuotientRepresentation A K L hLK).ρ (φ ^ i) a :=
      (rep_action_pow_eq_iterate
        (D.frobeniusQuotientRepresentation A K L hLK) φ i a).symm
    _ = D.frobeniusQuotientAction A K L hLK (φ ^ i) a :=
      D.frobeniusQuotientRepresentation_apply A K L hLK (φ ^ i) a

/-- A Frobenius power sum splits into its first `n` terms and a
translated block of `m` terms ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusQuotientDescent.lean:136`]
[Yamaguchi2026]). -/
theorem frobeniusPowerSum_add (D : DegreeData G) (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n m : ℕ)
    (x : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    D.frobeniusPowerSum A K L hLK φ (n + m) x =
      D.frobeniusPowerSum A K L hLK φ n x +
        D.frobeniusPowerSum A K L hLK φ m
          (D.frobeniusQuotientAction A K L hLK (φ ^ n) x) := by
  let B := D.frobeniusQuotientRepresentation A K L hLK
  have h := birkhoffSum_add (B.ρ φ) id n m x
  rw [D.birkhoffSum_eq_frobeniusPowerSum,
    D.birkhoffSum_eq_frobeniusPowerSum,
    D.birkhoffSum_eq_frobeniusPowerSum,
    ← rep_action_pow_eq_iterate B φ n x] at h
  change
    D.frobeniusPowerSum A K L hLK φ (n + m) x =
      D.frobeniusPowerSum A K L hLK φ n x +
        D.frobeniusPowerSum A K L hLK φ m
          (D.frobeniusQuotientAction A K L hLK (φ ^ n) x) at h
  exact h

/-- Actual additive telescoping identity for the Frobenius power sum
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusQuotientDescent.lean:160`]
[Yamaguchi2026]). -/
theorem frobeniusPowerSum_action_sub (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    D.frobeniusQuotientAction A K L hLK φ
        (D.frobeniusPowerSum A K L hLK φ n a) -
        D.frobeniusPowerSum A K L hLK φ n a =
      D.frobeniusQuotientAction A K L hLK (φ ^ n) a - a := by
  let B := D.frobeniusQuotientRepresentation A K L hLK
  have h := birkhoffSum_apply_sub_birkhoffSum (B.ρ φ) id n a
  have hshift :
      B.ρ φ (birkhoffSum (B.ρ φ) id n a) =
        birkhoffSum (B.ρ φ) id n (B.ρ φ a) := by
    calc
      B.ρ φ (birkhoffSum (B.ρ φ) id n a) =
          birkhoffSum (B.ρ φ) (B.ρ φ ∘ id) n a :=
        map_birkhoffSum (B.ρ φ) (B.ρ φ) id n a
      _ = birkhoffSum (B.ρ φ) id n (B.ρ φ a) := by
        unfold birkhoffSum
        apply Finset.sum_congr rfl
        intro i _
        simp only [Function.comp_apply, id_eq]
        exact (Function.Commute.self_iterate (B.ρ φ) i).eq a
  rw [← hshift] at h
  simp only [id_eq] at h
  rw [D.birkhoffSum_eq_frobeniusPowerSum A K L hLK,
    ← rep_action_pow_eq_iterate B φ n a] at h
  change
    D.frobeniusQuotientAction A K L hLK φ
          (D.frobeniusPowerSum A K L hLK φ n a) -
        D.frobeniusPowerSum A K L hLK φ n a =
      D.frobeniusQuotientAction A K L hLK (φ ^ n) a - a at h
  exact h

/-- The Frobenius power sum distributes over differences
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusQuotientDescent.lean:197`]
[Yamaguchi2026]). -/
theorem frobeniusPowerSum_sub_universalNormDescent (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (φ : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (x y : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    D.frobeniusPowerSum A K L hLK φ n (x - y) =
      D.frobeniusPowerSum A K L hLK φ n x -
        D.frobeniusPowerSum A K L hLK φ n y := by
  unfold DegreeData.frobeniusPowerSum
  change
    (∑ i : Fin n,
      D.frobeniusQuotientActionLinearMap A K L hLK (φ ^ i.1) (x - y)) =
      (∑ i : Fin n,
        D.frobeniusQuotientActionLinearMap A K L hLK (φ ^ i.1) x) -
      ∑ i : Fin n,
        D.frobeniusQuotientActionLinearMap A K L hLK (φ ^ i.1) y
  simp only [map_sub, Finset.sum_sub_distrib]

/-- An orbit sum of an element fixed by its first translate is scalar
multiplication by the orbit length ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusQuotientDescent.lean:218`]
[Yamaguchi2026]). -/
theorem frobeniusPowerSum_eq_nsmul_of_fixed (D : DegreeData G)
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (n : ℕ)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (ha : D.frobeniusQuotientAction A K L hLK q a = a) :
    D.frobeniusPowerSum A K L hLK q n a = n • a := by
  let B := D.frobeniusQuotientRepresentation A K L hLK
  have hpow (i : ℕ) :
      D.frobeniusQuotientAction A K L hLK (q ^ i) a = a := by
    have haB : B.ρ q a = a := by
      change D.frobeniusQuotientAction A K L hLK q a = a
      exact ha
    have hi := rep_action_pow_fixed B q a haB i
    change D.frobeniusQuotientAction A K L hLK (q ^ i) a = a at hi
    exact hi
  unfold DegreeData.frobeniusPowerSum
  simp_rw [hpow]
  simp

/-- Equivariance of `N_{L̃/K̃}` expressed inside `A_{L̃}`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusQuotientDescent.lean:241`]
[Yamaguchi2026]). -/
theorem maximalUnramifiedNorm_frobeniusQuotientAction (D : DegreeData G)
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (q : K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK)
    (a : ambientFixedAddSubgroup A (D.maximalUnramifiedField L)) :
    letI : Finite
        ((D.maximalUnramifiedField K).toSubgroup ⧸
          (D.maximalUnramifiedField L).toSubgroup.subgroupOf
            (D.maximalUnramifiedField K).toSubgroup) :=
      D.maximalUnramifiedExtension_finite K L
    fixedFieldInclusion A (D.maximalUnramifiedField K)
        (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
        (relativeNorm A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          (D.frobeniusQuotientAction A K L hLK q a)) =
      D.frobeniusQuotientAction A K L hLK q
        (fixedFieldInclusion A (D.maximalUnramifiedField K)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK)
          (relativeNorm A (D.maximalUnramifiedField K)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK)
            a)) := by
  letI : Finite
      ((D.maximalUnramifiedField K).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K).toSubgroup) :=
    D.maximalUnramifiedExtension_finite K L
  apply Subtype.ext
  exact D.relativeNorm_frobeniusQuotientAction A K L hLK q a

/-- A degree-zero element acts trivially on an element already defined
over `K̃` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusQuotientDescent.lean:276`]
[Yamaguchi2026]). -/
theorem frobeniusQuotientAction_fixed_of_degreeZero (D : DegreeData G)
    (A : Rep ℤ G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : D.extensionNormalizedDegree K L hLK q = 1)
    (a : ambientFixedAddSubgroup A
      (D.maximalUnramifiedField K.field)) :
    D.frobeniusQuotientAction A K.field L hLK q
        (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) a) =
      fixedFieldInclusion A (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField L)
        (D.maximalUnramifiedField_mono hLK) a := by
  let k : K.field.toSubgroup := Quotient.out q
  have hkq :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) =
        q :=
    Quotient.out_eq' q
  have hkDegree : D.normalizedDegree K k = 1 := by
    calc
      D.normalizedDegree K k =
          D.extensionNormalizedDegree K L hLK (QuotientGroup.mk k) := rfl
      _ = D.extensionNormalizedDegree K L hLK q :=
        congrArg (D.extensionNormalizedDegree K L hLK) hkq
      _ = 1 := hq
  have hkInertia : k ∈ D.fieldInertiaWithin K.field := by
    rw [← D.normalizedDegree_ker K]
    exact hkDegree
  let kI : (D.maximalUnramifiedField K.field).toSubgroup :=
    ⟨k.1, ⟨k.2, hkInertia⟩⟩
  rw [← hkq]
  apply Subtype.ext
  exact a.2 kI

/-- **Applying `N_{L̃/K̃}` to equation `(*)` kills all degree-zero
differences** — hence the norm of `u` is fixed by the chosen degree-one
Frobenius element ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusQuotientDescent.lean:312`]
[Yamaguchi2026]). -/
theorem maximalUnramifiedNorm_fixed_of_hstar (D : DegreeData G)
    (A : Rep ℤ G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    {ι : Type v} (s : Finset ι)
    (φ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (τ : ι →
      (D.extensionNormalizedDegreeContinuous K L hLK).toMonoidHom.ker)
    (u : ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (uᵢ : ι → ambientFixedAddSubgroup A (D.maximalUnramifiedField L))
    (hstar : D.frobeniusQuotientAction A K.field L hLK φ u - u =
      ∑ i ∈ s,
        (D.frobeniusQuotientAction A K.field L hLK (τ i).1 (uᵢ i) -
          uᵢ i)) :
    letI : Finite
        ((D.maximalUnramifiedField K.field).toSubgroup ⧸
          (D.maximalUnramifiedField L).toSubgroup.subgroupOf
            (D.maximalUnramifiedField K.field).toSubgroup) :=
      D.maximalUnramifiedExtension_finite K.field L
    let N := relativeNorm A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
    let b := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
      (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
      (N u)
    D.frobeniusQuotientAction A K.field L hLK φ b = b := by
  dsimp only
  letI : Finite
      ((D.maximalUnramifiedField K.field).toSubgroup ⧸
        (D.maximalUnramifiedField L).toSubgroup.subgroupOf
          (D.maximalUnramifiedField K.field).toSubgroup) :=
    D.maximalUnramifiedExtension_finite K.field L
  let N := relativeNorm A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
  let J := fixedFieldInclusion A (D.maximalUnramifiedField K.field)
    (D.maximalUnramifiedField L) (D.maximalUnramifiedField_mono hLK)
  have hnorm := congrArg (J.comp N) hstar
  simp only [map_sub, map_sum] at hnorm
  change J (N (D.frobeniusQuotientAction A K.field L hLK φ u)) -
      J (N u) =
    ∑ i ∈ s,
      (J (N (D.frobeniusQuotientAction A K.field L hLK
        (τ i).1 (uᵢ i))) -
        J (N (uᵢ i))) at hnorm
  have hφEquiv :
      J (N (D.frobeniusQuotientAction A K.field L hLK φ u)) =
        D.frobeniusQuotientAction A K.field L hLK φ (J (N u)) := by
    simpa [J, N] using
      D.maximalUnramifiedNorm_frobeniusQuotientAction A K.field L hLK φ u
  rw [hφEquiv] at hnorm
  have hzero (i : ι) :
      J (N (D.frobeniusQuotientAction A K.field L hLK
        (τ i).1 (uᵢ i))) =
        J (N (uᵢ i)) := by
    calc
      J (N (D.frobeniusQuotientAction A K.field L hLK
          (τ i).1 (uᵢ i))) =
          D.frobeniusQuotientAction A K.field L hLK (τ i).1
            (J (N (uᵢ i))) := by
        simpa [J, N] using
          D.maximalUnramifiedNorm_frobeniusQuotientAction
            A K.field L hLK (τ i).1 (uᵢ i)
      _ = J (N (uᵢ i)) := by
        simpa [J, N] using D.frobeniusQuotientAction_fixed_of_degreeZero
          A K L hLK (τ i).1 (τ i).2 (N (uᵢ i))
  simp_rw [hzero] at hnorm
  have hnormzero :
      D.frobeniusQuotientAction A K.field L hLK φ (J (N u)) -
        J (N u) = 0 := by
    simpa only [sub_self, Finset.sum_const_zero] using hnorm
  simpa [J, N] using sub_eq_zero.mp hnormzero

/-- **A `K̃`-fixed element with finite Galois support descends to `K` as
soon as it is fixed by a degree-one Frobenius lift**: the finite
degree-quotient decomposition writes each element of `Gal(P/K)` as a
positive Frobenius power up to inertia ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusQuotientDescent.lean:383`]
[Yamaguchi2026]). -/
theorem descend_maximalUnramified_fixed_of_finiteSupport (D : DegreeData G)
    (A : Rep ℤ G) (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    [hPnormal : (P.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (aI : ambientFixedAddSubgroup A (D.maximalUnramifiedField K.field))
    (aP : ambientFixedAddSubgroup A P.field)
    (hsupport :
      fixedFieldInclusion A P.field (D.maximalUnramifiedField L)
          P.above aP =
        fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) aI)
    (hfixed :
      D.frobeniusQuotientAction A K.field L hLK φ.1
          (fixedFieldInclusion A (D.maximalUnramifiedField K.field)
            (D.maximalUnramifiedField L)
            (D.maximalUnramifiedField_mono hLK) aI) =
        fixedFieldInclusion A (D.maximalUnramifiedField K.field)
          (D.maximalUnramifiedField L)
          (D.maximalUnramifiedField_mono hLK) aI) :
    ∃ aK : ambientFixedAddSubgroup A K.field,
      fixedFieldInclusion A K.field (D.maximalUnramifiedField K.field)
        (D.maximalUnramifiedField_le K.field) aK = aI := by
  letI hPfinite : Finite
      (K.field.toSubgroup ⧸
        P.field.toSubgroup.subgroupOf K.field.toSubgroup) := P.finite
  let f : K.field.toSubgroup := Quotient.out φ.1
  have hfφ :
      (QuotientGroup.mk f :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) =
        φ.1 :=
    Quotient.out_eq' φ.1
  have hfDegree : D.normalizedDegree K f =
      Multiplicative.ofAdd (1 : ProfiniteInteger) := by
    calc
      D.normalizedDegree K f =
          D.extensionNormalizedDegree K L hLK (QuotientGroup.mk f) := rfl
      _ = D.extensionNormalizedDegree K L hLK φ.1 :=
        congrArg (D.extensionNormalizedDegree K L hLK) hfφ
      _ = (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
            D.frobeniusExponent K L hLK φ :=
        D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ
      _ = Multiplicative.ofAdd (1 : ProfiniteInteger) := by simp [hφ]
  have hfFixed : A.ρ f.1 aI.1 = aI.1 := by
    rw [← hfφ] at hfixed
    exact congrArg Subtype.val hfixed
  have hfPowFixed (n : ℕ) : A.ρ (f.1 ^ n) aI.1 = aI.1 := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, map_mul]
        change A.ρ (f.1 ^ n) (A.ρ f.1 aI.1) = aI.1
        rw [hfFixed, ih]
  have hsval : aP.1 = aI.1 := congrArg Subtype.val hsupport
  have hKfixed (k : K.field.toSubgroup) : A.ρ k.1 aI.1 = aI.1 := by
    obtain ⟨q, hqk⟩ := D.frobeniusRestriction_surjective K P.field
      P.below (QuotientGroup.mk k)
    obtain ⟨n, _hn, hqDegree⟩ := q.2
    let t : K.field.toSubgroup := Quotient.out q.1
    have htq :
        (QuotientGroup.mk t :
          K.field.toSubgroup ⧸
            D.extensionInertiaWithin K.field P.field P.below) = q.1 :=
      Quotient.out_eq' q.1
    have htDegree : D.normalizedDegree K t =
        (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^ n := by
      calc
        D.normalizedDegree K t =
            D.extensionNormalizedDegree K P.field P.below
              (QuotientGroup.mk t) := rfl
        _ = D.extensionNormalizedDegree K P.field P.below q.1 :=
          congrArg (D.extensionNormalizedDegree K P.field P.below) htq
        _ = _ := hqDegree
    let z : K.field.toSubgroup := t⁻¹ * f ^ n
    have hzInertia : z ∈ D.fieldInertiaWithin K.field := by
      rw [← D.normalizedDegree_ker K]
      change D.normalizedDegree K z = 1
      rw [map_mul, map_inv, map_pow, htDegree, hfDegree]
      simp
    let zI : (D.maximalUnramifiedField K.field).toSubgroup :=
      ⟨z.1, ⟨z.2, hzInertia⟩⟩
    have hzFixed : A.ρ z.1 aI.1 = aI.1 := aI.2 zI
    have htFixed : A.ρ t.1 aI.1 = aI.1 := by
      calc
        A.ρ t.1 aI.1 = A.ρ t.1 (A.ρ z.1 aI.1) :=
          congrArg (A.ρ t.1) hzFixed.symm
        _ = A.ρ (t.1 * z.1) aI.1 := by rw [map_mul]; rfl
        _ = A.ρ (f.1 ^ n) aI.1 := by simp [z]
        _ = aI.1 := hfPowFixed n
    have htk :
        (QuotientGroup.mk t :
          K.field.toSubgroup ⧸
            P.field.toSubgroup.subgroupOf K.field.toSubgroup) =
        QuotientGroup.mk k := by
      calc
        QuotientGroup.mk t =
            D.extensionRestriction K.field P.field P.below
              (QuotientGroup.mk t) := rfl
        _ = D.extensionRestriction K.field P.field P.below q.1 :=
          congrArg (D.extensionRestriction K.field P.field P.below) htq
        _ = QuotientGroup.mk k := hqk
    have hrel : t⁻¹ * k ∈
        P.field.toSubgroup.subgroupOf K.field.toSubgroup :=
      QuotientGroup.eq.mp htk
    let rP : P.field.toSubgroup := ⟨(t⁻¹ * k).1, hrel⟩
    have hrval : rP.1 = (t⁻¹ * k).1 := rfl
    have hrval' : rP.1 = t.1⁻¹ * k.1 := hrval
    have hrFixed : A.ρ (t.1⁻¹ * k.1) aI.1 = aI.1 := by
      rw [← hsval, ← hrval']
      exact aP.2 rP
    calc
      A.ρ k.1 aI.1 = A.ρ (t.1 * (t.1⁻¹ * k.1)) aI.1 := by simp
      _ = A.ρ t.1 (A.ρ (t.1⁻¹ * k.1) aI.1) := by rw [map_mul]; rfl
      _ = A.ρ t.1 aI.1 := by rw [hrFixed]
      _ = aI.1 := htFixed
  let aK : ambientFixedAddSubgroup A K.field := ⟨aI.1, hKfixed⟩
  refine ⟨aK, ?_⟩
  apply Subtype.ext
  rfl

end DegreeData

end

end Atlas.Knowledge
