import Mathlib
import Atlas.Knowledge.AbstractExtension
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteIntermediateCompositum
import Atlas.Knowledge.FiniteIntermediateFieldRefinement
import Atlas.Knowledge.FrobeniusElements
import Atlas.Knowledge.FrobeniusExponent
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusFixedField
import Atlas.Knowledge.MaximalUnramifiedField
import Atlas.Knowledge.NormalizedDegree
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeIndexCardinal
import Atlas.Knowledge.TopologicalGeneration
import Atlas.Knowledge.UnramifiedQuotientGenerator

/-!
# Frobenius power fixed fields

The fields fixed by the powers `φⁿ` of a degree-one Frobenius element,
with the tower `Σₘ / Σ` between the fields of `φⁿᵐ` and `φⁿ`: inclusion,
exponent, Galois normality, unramifiedness, finiteness, relative degree
exactly `m`, quotient cardinality, and the concrete degree-one generator
of `Gal(Σₘ/Σ)` the unit-cohomology axiom is applied to (#104).

## Main definitions

* `DegreeData.frobeniusPowerOfDegreeOne` — the power `φⁿ` as a Frobenius
  element with its exponent recorded.

## Main statements

* `DegreeData.frobeniusPowerFixedField_le_finiteField` — a finite Galois
  stage `P ⊆ L̃` lies inside the field of `φ^{|G(P/K)|}`; proved.
* `DegreeData.frobeniusPowerFixedField_le` — the field of `φⁿᵐ` extends
  the field of `φⁿ`; proved.
* `DegreeData.frobeniusPowerFixedField_normal` — the tower is Galois;
  proved.
* `DegreeData.frobeniusPowerFixedField_isUnramified` — the tower is
  unramified; proved.
* `DegreeData.frobeniusPowerFixedField_quotientCard` — the tower's degree
  is exactly `m`; proved.
* `DegreeData.frobeniusPowerFixedField_generator` — the restriction of
  `φⁿ` generates `Gal(Σₘ/Σ)` with normalized degree one; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`AbstractExtension` lives at the layer's top level rather than inside
`DegreeData`, `ZHat` is `ProfiniteInteger`, and the power-injectivity of
the generator is `ProfiniteInteger.ofAdd_one_pow_injective`. The
source's closedness lemma for the relative subgroup is inlined as
`isClosed'.preimage continuous_subtype_val` — under the `subgroupOf`
spelling the relative subgroup's coercion *is* that preimage, and the
layer never grew the wrapper. The spelling frees the statement-level
containments four theorems bind and their statements alone consume, the
finiteness theorem's call sheds the containments #136's generalized form
stopped asking for, and eight of the source's ambient binders fed
separation facts the proofs never used or that instance synthesis
rebuilds from total disconnectedness; all of them go. After the sweep
the finiteness theorem and the quotient-finiteness theorem state the
same fact — faithful to the source, which records it twice by different
routes, the second through the computed relative index. Two proof steps
flatten `by exact` to `from`, and the residue degree's positivity reads
`.pos` for the source's `.property`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- An element fixing `L` commutes modulo the inertia with every
degree-zero element of `G(L̃/K)` — group-theoretically,
`[G_L, I_K] ⊆ G_L ∩ I_K = G_{L̃}` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:34`]
[Yamaguchi2026]). -/
theorem extensionInertia_commutes_of_mem_extensionSubgroup (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (k : K.field.toSubgroup)
    (hk : k ∈ L.toSubgroup.subgroupOf K.field.toSubgroup)
    (q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hq : D.extensionNormalizedDegree K L hLK q = 1) :
    (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) * q =
      q * QuotientGroup.mk k := by
  revert hq
  refine Quotient.inductionOn' q ?_
  intro t hdt
  have htI : t ∈ D.fieldInertiaWithin K.field := by
    rw [← D.normalizedDegree_ker K]
    exact hdt
  change QuotientGroup.mk (k * t) = QuotientGroup.mk (t * k)
  apply QuotientGroup.eq.mpr
  constructor
  · change (k * t)⁻¹ * (t * k) ∈
      L.toSubgroup.subgroupOf K.field.toSubgroup
    have hconj : t⁻¹ * k⁻¹ * t ∈
        L.toSubgroup.subgroupOf K.field.toSubgroup := by
      simpa using hLnormal.conj_mem k⁻¹
        ((L.toSubgroup.subgroupOf K.field.toSubgroup).inv_mem hk) t⁻¹
    simpa [mul_assoc] using
      (L.toSubgroup.subgroupOf K.field.toSubgroup).mul_mem hconj hk
  · change (k * t)⁻¹ * (t * k) ∈ D.fieldInertiaWithin K.field
    have hconj : k⁻¹ * t * k ∈ D.fieldInertiaWithin K.field := by
      simpa using
        (inferInstance : (D.fieldInertiaWithin K.field).Normal).conj_mem
          t htI k⁻¹
    simp [mul_assoc]

/-- For a finite Galois `P/K` inside `L̃/K` containing `L`, the
`|G(P/K)|`-th power of every element of `G(L̃/K)` fixes `P`, hence
commutes with the degree-zero kernel — the finite-stage input behind the
choice `n = [M:K]`, `σ = φⁿ` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:70`]
[Yamaguchi2026]). -/
theorem quotientPower_card_commutes_degreeZero (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    (hPL : P.field.toSubgroup ≤ L.toSubgroup)
    [hPnormal : (P.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (q τ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK)
    (hτ : D.extensionNormalizedDegree K L hLK τ = 1) :
    let n := Nat.card
      (K.field.toSubgroup ⧸
        P.field.toSubgroup.subgroupOf K.field.toSubgroup)
    q ^ n * τ = τ * q ^ n := by
  let R := K.field.toSubgroup ⧸
    P.field.toSubgroup.subgroupOf K.field.toSubgroup
  letI : Finite R := P.finite
  let n := Nat.card R
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let hIP : D.extensionInertiaWithin K.field L hLK ≤
      P.field.toSubgroup.subgroupOf K.field.toSubgroup := by
    intro x hx
    have hxE : x ∈ (D.maximalUnramifiedField L).toSubgroup.subgroupOf
        K.field.toSubgroup := by
      rw [D.subgroupOf_maximalUnramifiedField K.field L hLK]
      exact hx
    apply Subgroup.mem_subgroupOf.2
    exact P.above (Subgroup.mem_subgroupOf.1 hxE)
  let rP : Q →* R :=
    QuotientGroup.map (D.extensionInertiaWithin K.field L hLK)
      (P.field.toSubgroup.subgroupOf K.field.toSubgroup)
      (MonoidHom.id K.field.toSubgroup) hIP
  let k : K.field.toSubgroup := Quotient.out (q ^ n)
  have hkq : (QuotientGroup.mk k : Q) = q ^ n :=
    Quotient.out_eq' (q ^ n)
  have hrPpow : rP (q ^ n) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one'
  have hkP : k ∈ P.field.toSubgroup.subgroupOf K.field.toSubgroup := by
    apply (QuotientGroup.eq_one_iff k).1
    calc
      (QuotientGroup.mk k : R) = rP (QuotientGroup.mk k) := rfl
      _ = rP (q ^ n) := congrArg rP hkq
      _ = 1 := hrPpow
  have hkL : k ∈ L.toSubgroup.subgroupOf K.field.toSubgroup := by
    apply Subgroup.mem_subgroupOf.2
    exact hPL (Subgroup.mem_subgroupOf.1 hkP)
  have hcomm := D.extensionInertia_commutes_of_mem_extensionSubgroup
    K L hLK k hkL τ hτ
  simpa [Q, n, hkq] using hcomm

/- The normalized degree of a power of a degree-one element
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:120`]
[Yamaguchi2026]). -/
private theorem extensionNormalizedDegree_pow_of_degreeOne (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) :
    D.extensionNormalizedDegree K L hLK (φ.1 ^ n) =
      (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^ n := by
  rw [map_pow,
    D.extensionNormalizedDegree_frobenius_eq_pow K L hLK φ, hφ]
  simp

/-- **The power `φⁿ` of a degree-one Frobenius element, with its exponent recorded**
— these are the elements `σ = φⁿ` and `σᵐ = φⁿᵐ` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:135`]
[Yamaguchi2026]). -/
def frobeniusPowerOfDegreeOne (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) (hn : 0 < n) : D.FrobeniusElements K L hLK :=
  ⟨φ.1 ^ n,
    ⟨n, hn, D.extensionNormalizedDegree_pow_of_degreeOne
      K L hLK φ hφ n⟩⟩

/-- The degree-one Frobenius power has the stated ambient coercion. -/
@[simp]
theorem frobeniusPowerOfDegreeOne_coe (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) (hn : 0 < n) :
    (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn).1 = φ.1 ^ n :=
  rfl

/-- **A finite Galois stage `P ⊆ L̃` lies inside the field of `φ^{|G(P/K)|}`**:
the power is trivial in `G(P/K)`, and the kernel of the restriction is
closed, so it swallows the whole procyclic closure ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:163`]
[Yamaguchi2026]). -/
theorem frobeniusPowerFixedField_le_finiteField (D : DegreeData G)
    [IsTopologicalGroup G] (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (P : FiniteIntermediateField (D.maximalUnramifiedField L) K.field)
    [hPnormal : (P.field.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1) :
    let n := P.quotientCard
    let hn : 0 < n := P.quotientCard_pos
    (D.frobeniusFixedField K L hLK
      (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn)).toSubgroup ≤
      P.field.toSubgroup := by
  dsimp only
  let R := K.field.toSubgroup ⧸
    P.field.toSubgroup.subgroupOf K.field.toSubgroup
  let n := P.quotientCard
  have hn : 0 < n := P.quotientCard_pos
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let hIP : D.extensionInertiaWithin K.field L hLK ≤
      P.field.toSubgroup.subgroupOf K.field.toSubgroup := by
    intro x hx
    have hxE : x ∈ (D.maximalUnramifiedField L).toSubgroup.subgroupOf
        K.field.toSubgroup := by
      rw [D.subgroupOf_maximalUnramifiedField K.field L hLK]
      exact hx
    apply Subgroup.mem_subgroupOf.2
    exact P.above (Subgroup.mem_subgroupOf.1 hxE)
  let rP : Q →ₜ* R :=
    { toMonoidHom :=
        QuotientGroup.map
          (N := D.extensionInertiaWithin K.field L hLK)
          (M := P.field.toSubgroup.subgroupOf K.field.toSubgroup)
          (f := MonoidHom.id K.field.toSubgroup) hIP
      continuous_toFun := by
        refine (QuotientGroup.isQuotientMap_mk
          (G := K.field.toSubgroup)
          (N := D.extensionInertiaWithin K.field L hLK)).continuous_iff.2 ?_
        change Continuous
          (⇑(QuotientGroup.map
              (D.extensionInertiaWithin K.field L hLK)
              (P.field.toSubgroup.subgroupOf K.field.toSubgroup)
              (MonoidHom.id K.field.toSubgroup) hIP) ∘
            QuotientGroup.mk'
              (D.extensionInertiaWithin K.field L hLK))
        have hcomp :
            (⇑(QuotientGroup.map
                (D.extensionInertiaWithin K.field L hLK)
                (P.field.toSubgroup.subgroupOf K.field.toSubgroup)
                (MonoidHom.id K.field.toSubgroup) hIP) ∘
              QuotientGroup.mk'
                (D.extensionInertiaWithin K.field L hLK)) =
              QuotientGroup.mk'
                (P.field.toSubgroup.subgroupOf K.field.toSubgroup) := by
          funext k
          exact QuotientGroup.map_mk' _ _ _ _ k
        rw [hcomp]
        exact continuous_quotient_mk' }
  letI : Finite R := P.finite
  letI : IsClosed
      (P.field.toSubgroup.subgroupOf K.field.toSubgroup :
        Set K.field.toSubgroup) :=
    P.field.isClosed'.preimage continuous_subtype_val
  have hrPpow : rP (φ.1 ^ n) = 1 := by
    rw [map_pow]
    change (rP φ.1) ^ Nat.card R = 1
    exact pow_card_eq_one'
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  have hclosure :
      (D.frobeniusClosure K L hLK σ).toSubgroup ≤
        rP.toMonoidHom.ker := by
    apply Subgroup.topologicalClosure_minimal
    · rw [Subgroup.closure_le]
      intro z hz
      have hz' : z = φ.1 ^ n := by simpa [σ] using hz
      subst z
      exact hrPpow
    · change IsClosed {x : Q | rP x = 1}
      exact isClosed_eq rP.continuous continuous_const
  rintro g ⟨k, hk, rfl⟩
  apply Subgroup.mem_subgroupOf.1
  apply (QuotientGroup.eq_one_iff k).1
  have hk' := hclosure hk
  change QuotientGroup.mk'
    (P.field.toSubgroup.subgroupOf K.field.toSubgroup) k = 1 at hk'
  exact hk'

/-- The Frobenius exponent of the degree-one power is the supplied
exponent ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:252`]
[Yamaguchi2026]). -/
@[simp]
theorem frobeniusExponent_powerOfDegreeOne (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n : ℕ) (hn : 0 < n) :
    D.frobeniusExponent K L hLK
      (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn) = n := by
  apply ProfiniteInteger.ofAdd_one_pow_injective
  calc
    (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
        D.frobeniusExponent K L hLK
          (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn) =
        D.extensionNormalizedDegree K L hLK
          (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn).1 :=
      (D.extensionNormalizedDegree_frobenius_eq_pow K L hLK
        (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn)).symm
    _ = (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^ n :=
      D.extensionNormalizedDegree_pow_of_degreeOne K L hLK φ hφ n

/- The closure of `φⁿᵐ` lies inside the closure of `φⁿ`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:274`]
[Yamaguchi2026]). -/
private theorem frobeniusClosure_power_mul_le (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (D.frobeniusClosure K L hLK
      (D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
        (Nat.mul_pos hn hm))).toSubgroup ≤
      (D.frobeniusClosure K L hLK
        (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn)).toSubgroup := by
  let Q := K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK
  let x : Q := φ.1 ^ n
  let C : ClosedSubgroup Q := closedSubgroupGenerated ({x} : Set Q)
  have hxC : x ∈ C.toSubgroup :=
    Subgroup.le_topologicalClosure _
      (Subgroup.subset_closure (by simp [x]))
  have hpowC : φ.1 ^ (n * m) ∈ C.toSubgroup := by
    rw [pow_mul]
    exact C.toSubgroup.pow_mem hxC m
  change (closedSubgroupGenerated
      (Set.range (fun _ : Unit => φ.1 ^ (n * m)))).toSubgroup ≤
    (closedSubgroupGenerated
      (Set.range (fun _ : Unit => φ.1 ^ n))).toSubgroup
  have hrangeLeft : Set.range (fun _ : Unit => φ.1 ^ (n * m)) =
      ({φ.1 ^ (n * m)} : Set Q) := by ext q; simp
  have hrangeRight : Set.range (fun _ : Unit => φ.1 ^ n) =
      ({φ.1 ^ n} : Set Q) := by ext q; simp
  rw [hrangeLeft, hrangeRight]
  apply Subgroup.topologicalClosure_minimal
  · rw [Subgroup.closure_le]
    simpa [C, x] using hpowC
  · exact (closedSubgroupGenerated ({φ.1 ^ n} : Set Q)).isClosed'

/-- **The field fixed by `φⁿᵐ` extends the field fixed by `φⁿ`** — the
tower `Σₘ / Σ` of the universal norm-descent lemma ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:312`]
[Yamaguchi2026]). -/
theorem frobeniusPowerFixedField_le (D : DegreeData G)
    [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (D.frobeniusFixedField K L hLK
      (D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
        (Nat.mul_pos hn hm))).toSubgroup ≤
      (D.frobeniusFixedField K L hLK
        (D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn)).toSubgroup := by
  rintro z ⟨k, hk, rfl⟩
  exact ⟨k,
    D.frobeniusClosure_power_mul_le K L hLK φ hφ n m hn hm hk,
    rfl⟩

/-- **The power-fixed-field tower is Galois** — on the group side, the
normality of the closure of `φⁿᵐ` inside the procyclic closure of `φⁿ`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:333`]
[Yamaguchi2026]). -/
theorem frobeniusPowerFixedField_normal (D : DegreeData G)
    [IsTopologicalGroup G] [T2Space G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
      (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    (T.toSubgroup.subgroupOf S.toSubgroup).Normal := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
    (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hSK := D.frobeniusFixedField_le K L hLK σ
  let hTK := D.frobeniusFixedField_le K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
  let C := D.frobeniusClosure K L hLK σ
  let Cm := D.frobeniusClosure K L hLK σm
  letI : CommGroup C := D.frobeniusClosureCommGroup K L hLK σ
  have hCmC : Cm.toSubgroup ≤ C.toSubgroup :=
    D.frobeniusClosure_power_mul_le K L hLK φ hφ n m hn hm
  constructor
  intro t ht s
  have htT : t.1 ∈ T.toSubgroup := Subgroup.mem_subgroupOf.1 ht
  let tK : K.field.toSubgroup := ⟨t.1, hSK t.2⟩
  let sK : K.field.toSubgroup := ⟨s.1, hSK s.2⟩
  have htFixed : tK ∈ D.frobeniusFixedSubgroupWithin K L hLK σm := by
    rw [← D.subgroupOf_frobeniusFixedField K L hLK σm]
    exact Subgroup.mem_subgroupOf.2 htT
  have hsFixed : sK ∈ D.frobeniusFixedSubgroupWithin K L hLK σ := by
    rw [← D.subgroupOf_frobeniusFixedField K L hLK σ]
    exact Subgroup.mem_subgroupOf.2 s.2
  let a : C := ⟨QuotientGroup.mk sK, hsFixed⟩
  let b : C := ⟨QuotientGroup.mk tK, hCmC htFixed⟩
  have hconj :
      (QuotientGroup.mk sK :
          K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) *
        QuotientGroup.mk tK * (QuotientGroup.mk sK)⁻¹ =
          QuotientGroup.mk tK := by
    exact congrArg Subtype.val (by
      change a * b * a⁻¹ = b
      simp)
  apply Subgroup.mem_subgroupOf.2
  let cK : K.field.toSubgroup := ⟨s.1 * t.1 * s.1⁻¹, by
    exact K.field.toSubgroup.mul_mem
      (K.field.toSubgroup.mul_mem (hSK s.2) (hSK t.2))
      (K.field.toSubgroup.inv_mem (hSK s.2))⟩
  refine ⟨cK, ?_, rfl⟩
  change QuotientGroup.mk cK ∈ Cm.toSubgroup
  change QuotientGroup.mk sK * QuotientGroup.mk tK *
      (QuotientGroup.mk sK)⁻¹ ∈ Cm.toSubgroup
  rw [hconj]
  exact htFixed

/-- **The extension fixed by `φⁿᵐ` over the field fixed by `φⁿ` is unramified**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:398`]
[Yamaguchi2026]). -/
theorem frobeniusPowerFixedField_isUnramified (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
      (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
    (AbstractExtension.mk T S hTS).IsUnramified D := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
    (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
  rw [(AbstractExtension.mk T S hTS).isUnramified_iff_inertia_le D]
  intro x hx
  have hxI : x ∈ D.fieldInertia S := ⟨hx.1, hx.2⟩
  have hSI : D.fieldInertia S = D.fieldInertia L :=
    D.frobeniusFixedField_fieldInertia K L hLK σ
  have hTI : D.fieldInertia T = D.fieldInertia L :=
    D.frobeniusFixedField_fieldInertia K L hLK σm
  rw [hSI, ← hTI] at hxI
  exact hxI.1

/-- Finiteness of the power-fixed-field tower ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:432`]
[Yamaguchi2026]). -/
theorem frobeniusPowerFixedField_finite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
      (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    Finite (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup) := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
    (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hSK := D.frobeniusFixedField_le K L hLK σ
  let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
  letI hTKfinite : Finite
      (K.field.toSubgroup ⧸ T.toSubgroup.subgroupOf K.field.toSubgroup) :=
    D.frobeniusFixedField_finite K L hLK σm
  exact FiniteIntermediateField.finite_extension_of_le hSK hTS

/- The relative degree of the tower is exactly `m` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:465`]
[Yamaguchi2026]). -/
private theorem frobeniusPowerFixedField_relIndex (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
      (n * m) (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    T.toSubgroup.relIndex S.toSubgroup = m := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
    (n * m) (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le
    K L hLK φ hφ n m hn hm
  have hTSunramified : (AbstractExtension.mk T S hTS).IsUnramified D :=
    D.frobeniusPowerFixedField_isUnramified
      K L hLK φ hφ n m hn hm
  have hTSramification :
      (T.toSubgroup ⊓ D.degree.toMonoidHom.ker).relIndex
          (S.toSubgroup ⊓ D.degree.toMonoidHom.ker) = 1 := by
    rw [Subgroup.relIndex_eq_one]
    intro x hx
    exact ⟨hTSunramified hx, hx.2⟩
  rw [relIndex_eq_map_relIndex_mul_inf_ker_relIndex
      D.degree.toMonoidHom hTS,
    hTSramification, Nat.mul_one]
  let SR := D.frobeniusFixedResidueField K L hLK σ
  let TR := D.frobeniusFixedResidueField K L hLK σm
  have hSindex : (D.fieldImage S).index = (SR.residueDegree : ℕ) := by
    have h := D.fieldImageAdd_index SR
    change (D.fieldImage S).index = (SR.residueDegree : ℕ) at h
    exact h
  have hTindex : (D.fieldImage T).index = (TR.residueDegree : ℕ) := by
    have h := D.fieldImageAdd_index TR
    change (D.fieldImage T).index = (TR.residueDegree : ℕ) at h
    exact h
  have hresidueMul :
      (T.toSubgroup.map D.degree.toMonoidHom).relIndex
          (S.toSubgroup.map D.degree.toMonoidHom) *
          (SR.residueDegree : ℕ) = (TR.residueDegree : ℕ) := by
    rw [← hSindex, ← hTindex, D.fieldImage_eq_map, D.fieldImage_eq_map]
    exact Subgroup.relIndex_mul_index (Subgroup.map_mono hTS)
  rw [D.frobeniusFixedResidueField_residueDegree K L hLK σ,
    D.frobeniusFixedResidueField_residueDegree K L hLK σm] at hresidueMul
  rw [show D.frobeniusExponent K L hLK σm = n * m from
      D.frobeniusExponent_powerOfDegreeOne
        K L hLK φ hφ (n * m) (Nat.mul_pos hn hm),
    show D.frobeniusExponent K L hLK σ = n from
      D.frobeniusExponent_powerOfDegreeOne
        K L hLK φ hφ n hn] at hresidueMul
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hn K.residueDegree.pos)
  calc
    (T.toSubgroup.map D.degree.toMonoidHom).relIndex
          (S.toSubgroup.map D.degree.toMonoidHom) *
        (n * (K.residueDegree : ℕ)) =
      (n * m) * (K.residueDegree : ℕ) := hresidueMul
    _ = m * (n * (K.residueDegree : ℕ)) := by ac_rfl

/-- The quotient between two successive Frobenius power fixed fields is
finite, from the computed relative index ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:535`]
[Yamaguchi2026]). -/
theorem frobeniusPowerFixedField_quotientFinite (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
      (n * m) (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    Finite (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup) := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
    (n * m) (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  apply (Subgroup.index_ne_zero_iff_finite).mp
  change T.toSubgroup.relIndex S.toSubgroup ≠ 0
  rw [D.frobeniusPowerFixedField_relIndex
    K L hLK φ hφ n m hn hm]
  exact hm.ne'

/-- **The tower's degree is exactly `m`** — the cardinality form of the
relative-degree computation ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:567`]
[Yamaguchi2026]). -/
theorem frobeniusPowerFixedField_quotientCard (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
      (n * m) (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    Nat.card (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup) = m := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ
    (n * m) (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  letI : Finite (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup) :=
    D.frobeniusPowerFixedField_quotientFinite
      K L hLK φ hφ n m hn hm
  calc
    Nat.card (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup) =
        (T.toSubgroup.subgroupOf S.toSubgroup).index := rfl
    _ = T.toSubgroup.relIndex S.toSubgroup := by
      rfl
    _ = m :=
      D.frobeniusPowerFixedField_relIndex
        K L hLK φ hφ n m hn hm

/-- **The restriction of the concrete `φⁿ` is a degree-one generator of `Gal(Σₘ/Σ)`**
— the generator the unit-cohomology axiom is applied to; retaining the
actual representative is what the subsequent equation involving `σ = φⁿ`
runs on ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusPowerFixedField.lean:608`]
[Yamaguchi2026]). -/
theorem frobeniusPowerFixedField_generator (D : DegreeData G)
    [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite : Finite
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)]
    (φ : D.FrobeniusElements K L hLK)
    (hφ : D.frobeniusExponent K L hLK φ = 1)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
    let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
      (Nat.mul_pos hn hm)
    let S := D.frobeniusFixedField K L hLK σ
    let T := D.frobeniusFixedField K L hLK σm
    let hTSnormal : (T.toSubgroup.subgroupOf S.toSubgroup).Normal :=
      D.frobeniusPowerFixedField_normal K L hLK φ hφ n m hn hm
    letI := hTSnormal
    ∃ s : S.toSubgroup,
      D.frobeniusFixedFieldToClosure K L hLK σ s =
          D.frobeniusInClosure K L hLK σ ∧
      D.normalizedDegree (D.frobeniusFixedResidueField K L hLK σ) s =
        Multiplicative.ofAdd (1 : ProfiniteInteger) ∧
      ∀ x : S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup,
        x ∈ Subgroup.zpowers (QuotientGroup.mk s) := by
  dsimp only
  let σ := D.frobeniusPowerOfDegreeOne K L hLK φ hφ n hn
  let σm := D.frobeniusPowerOfDegreeOne K L hLK φ hφ (n * m)
    (Nat.mul_pos hn hm)
  let S := D.frobeniusFixedField K L hLK σ
  let T := D.frobeniusFixedField K L hLK σm
  let hTS := D.frobeniusPowerFixedField_le K L hLK φ hφ n m hn hm
  let hTSnormal : (T.toSubgroup.subgroupOf S.toSubgroup).Normal :=
    D.frobeniusPowerFixedField_normal K L hLK φ hφ n m hn hm
  letI := hTSnormal
  let k : K.field.toSubgroup := Quotient.out σ.1
  have hkσ :
      (QuotientGroup.mk k :
        K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) =
        σ.1 :=
    Quotient.out_eq' σ.1
  have hkClosure : QuotientGroup.mk k ∈
      (D.frobeniusClosure K L hLK σ).toSubgroup := by
    rw [hkσ]
    exact (D.frobeniusInClosure K L hLK σ).2
  let s : S.toSubgroup := ⟨k.1, ⟨k, hkClosure, rfl⟩⟩
  have hsClosure :
      D.frobeniusFixedFieldToClosure K L hLK σ s =
        D.frobeniusInClosure K L hLK σ := by
    apply Subtype.ext
    exact hkσ
  have hsDegree :
      D.normalizedDegree (D.frobeniusFixedResidueField K L hLK σ) s =
        Multiplicative.ofAdd (1 : ProfiniteInteger) := by
    rw [← D.frobeniusFixedField_normalizedDegree_compatibility
      K L hLK σ s, hsClosure]
    exact D.fixedFieldNormalizedDegree_generator K L hLK σ
  letI hTSfinite : Finite
      (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup) :=
    D.frobeniusPowerFixedField_finite K L hLK φ hφ n m hn hm
  have hTSunramified : (AbstractExtension.mk T S hTS).IsUnramified D :=
    D.frobeniusPowerFixedField_isUnramified
      K L hLK φ hφ n m hn hm
  let SR := D.frobeniusFixedResidueField K L hLK σ
  letI : (T.toSubgroup.subgroupOf SR.field.toSubgroup).Normal := by
    change (T.toSubgroup.subgroupOf S.toSubgroup).Normal
    exact hTSnormal
  letI : Finite
      (SR.field.toSubgroup ⧸
        T.toSubgroup.subgroupOf SR.field.toSubgroup) := by
    change Finite (S.toSubgroup ⧸ T.toSubgroup.subgroupOf S.toSubgroup)
    exact hTSfinite
  have hTSunramifiedR :
      (AbstractExtension.mk T SR.field hTS).IsUnramified D := by
    change (AbstractExtension.mk T S hTS).IsUnramified D
    exact hTSunramified
  refine ⟨s, hsClosure, hsDegree, ?_⟩
  exact D.quotient_generator_of_unramified_degree_one
    SR T hTS hTSunramifiedR s hsDegree

end DegreeData

end

end Atlas.Knowledge
