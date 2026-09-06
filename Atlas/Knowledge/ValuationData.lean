import Mathlib
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.RelativeNorm

/-!
# valuation datum

The henselian-valuation axiom of the reciprocity engine (#104), completing its
input contract: an additive valuation `v : A_k →+ ℤ̂` whose value group contains
the integers and reduces bijectively modulo every positive integer through the
canonical inclusion-and-reduction map, and whose norm composites from every
finite abstract field have image exactly `f_K·Z` — the `norm_range` condition.
From the datum: the normalized valuations `v_K = (1/f_K)·(v ∘ N_{K|k})` over
every finite abstract field, with the exact value-group codomain, and their
surjectivity.

## Main definitions

* `normToBase` — the norm `N_{K|k}` on fixed modules.
* `nsmulWithin` / `nsmulImage` — `nZ` inside a value group and inside `ℤ̂`.
* `canonicalValueQuotientMap` — the canonical `Z/nZ →+ ℤ/nℤ`.
* `ValuationData` — the axiom: `toAddMonoidHom`, `integers_mem`,
  `canonical_value_quotient_bijective`, `norm_range`.
* `ValuationData.valuationAt` — the normalized valuation over a finite field.

## Main statements

* `canonicalValueQuotientMap_top_bijective` — the full value group satisfies
  the quotient condition; proved.
* `ValuationData.residueDegree_nsmul_dividedAt` — `f_K·v_K = v ∘ N_{K|k}`;
  proved.
* `ValuationData.normalizedValuation_surjective` — every normalized valuation
  maps onto the value group; proved.

## Implementation notes

Positivity of moduli is carried as `[NeZero n]` where the source writes
`0 < n`, matching the layer's `ℤ̂` API; the two are interchangeable and the
axiom's content is unchanged. The `f_K·ℤ̂` placements go through
`Atlas.Knowledge.ProfiniteInteger.spanAddSubgroup` and the division through
`Atlas.Knowledge.ProfiniteInteger.divide`, as in the normalized degree, and the
source's `normCompositeAtInResidueImage` is named `normCompositeAtInSpan` for
that vocabulary. The relative subgroup is `Subgroup.subgroupOf` throughout, and
the ambient group is universe-general — only the engine's own instantiation
pins `Type 0`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **The norm to the base** `N_{K|k}` on the fixed modules
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Valuation.lean:27`). -/
def normToBase (A : Rep ℤ G) (K : ClosedSubgroup G)
    [Finite ((baseField G).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField G).toSubgroup)] :
    ambientFixedAddSubgroup A K →+
      ambientFixedAddSubgroup A (baseField G) :=
  relativeNorm A (baseField G) K (le_baseField K)

/-- Multiplication by `n` on an additive subgroup of `ℤ̂`. -/
def nsmulOnAddSubgroup (Z : AddSubgroup ProfiniteInteger) (n : ℕ) : Z →+ Z where
  toFun z := ⟨n • z.1, Z.nsmul_mem z.2 n⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- **The subgroup `nZ` inside a value group**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Valuation.lean:41`). -/
def nsmulWithin (Z : AddSubgroup ProfiniteInteger) (n : ℕ) : AddSubgroup Z :=
  (nsmulOnAddSubgroup Z n).range

/-- **The ambient subgroup `nZ ⊆ ℤ̂`** (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Valuation.lean:45`). -/
def nsmulImage (Z : AddSubgroup ProfiniteInteger) (n : ℕ) :
    AddSubgroup ProfiniteInteger :=
  Z.map
    { toFun := fun z : ProfiniteInteger => n • z
      map_zero' := nsmul_zero n
      map_add' := fun x y => nsmul_add x y n }

/-- Membership in the multiple image is having a preimage in the subgroup. -/
@[simp]
theorem mem_nsmulImage_iff (Z : AddSubgroup ProfiniteInteger) (n : ℕ)
    (z : ProfiniteInteger) :
    z ∈ nsmulImage Z n ↔ ∃ x ∈ Z, n • x = z := by
  rfl

/-- Multiples of the full value group are the span of `n`. -/
@[simp]
theorem nsmulImage_top (n : ℕ) :
    nsmulImage (⊤ : AddSubgroup ProfiniteInteger) n =
      ProfiniteInteger.spanAddSubgroup n := by
  ext z
  rw [mem_nsmulImage_iff, ProfiniteInteger.mem_spanAddSubgroup_iff]
  constructor
  · rintro ⟨x, _hx, rfl⟩
    exact ⟨x, (nsmul_eq_mul n x).symm⟩
  · rintro ⟨x, rfl⟩
    exact ⟨x, AddSubgroup.mem_top x, nsmul_eq_mul n x⟩

/-- Reduction modulo `n` restricted along `Z ≤ ℤ̂`. -/
def valueGroupReduction (Z : AddSubgroup ProfiniteInteger) (n : ℕ) [NeZero n] :
    Z →+ ZMod n :=
  (ProfiniteInteger.reduction n).toAddMonoidHom.comp Z.subtype

/-- **The canonical map `Z/nZ →+ ℤ/nℤ`** — inclusion followed by reduction,
the specific map of the valuation-quotient axiom rather than an arbitrary
equivalence (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Valuation.lean:81`). -/
def canonicalValueQuotientMap (Z : AddSubgroup ProfiniteInteger)
    (n : ℕ) [NeZero n] : (Z ⧸ nsmulWithin Z n) →+ ZMod n :=
  QuotientAddGroup.lift (nsmulWithin Z n) (valueGroupReduction Z n) (by
    rintro _ ⟨z, rfl⟩
    change ProfiniteInteger.reduction n (n • (z : ProfiniteInteger)) = 0
    rw [map_nsmul]
    simp [nsmul_eq_mul])

/-- The canonical map computes on representatives by reduction. -/
@[simp]
theorem canonicalValueQuotientMap_mk (Z : AddSubgroup ProfiniteInteger)
    (n : ℕ) [NeZero n] (z : Z) :
    canonicalValueQuotientMap Z n
        (QuotientAddGroup.mk' (nsmulWithin Z n) z) =
      ProfiniteInteger.reduction n (z : ProfiniteInteger) :=
  rfl

/-- **The full value group satisfies the quotient condition**: the canonical
map is bijective for `Z = ℤ̂` (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Valuation.lean:100`). -/
theorem canonicalValueQuotientMap_top_bijective (n : ℕ) [NeZero n] :
    Function.Bijective
      (canonicalValueQuotientMap (⊤ : AddSubgroup ProfiniteInteger) n) := by
  constructor
  · intro q₁ q₂
    refine Quotient.inductionOn' q₁ ?_
    intro z₁
    refine Quotient.inductionOn' q₂ ?_
    intro z₂ h
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have hz : ProfiniteInteger.reduction n
        ((z₁ : ProfiniteInteger) - (z₂ : ProfiniteInteger)) = 0 := by
      rw [map_sub]
      change ProfiniteInteger.reduction n (z₁ : ProfiniteInteger) =
        ProfiniteInteger.reduction n (z₂ : ProfiniteInteger) at h
      rw [h, sub_self]
    have hrange : (z₁ : ProfiniteInteger) - (z₂ : ProfiniteInteger) ∈
        ProfiniteInteger.spanAddSubgroup n := by
      change (z₁ : ProfiniteInteger) - (z₂ : ProfiniteInteger) ∈
        Ideal.span {(n : ProfiniteInteger)}
      rw [ProfiniteInteger.span_natCast_eq_ker_reduction n]
      exact hz
    obtain ⟨w, hw⟩ :=
      (ProfiniteInteger.mem_spanAddSubgroup_iff _).mp hrange
    refine ⟨⟨w, AddSubgroup.mem_top w⟩, ?_⟩
    apply Subtype.ext
    change n • w = (z₁ : ProfiniteInteger) - (z₂ : ProfiniteInteger)
    rw [nsmul_eq_mul]
    exact hw
  · intro a
    obtain ⟨z, hz⟩ := ProfiniteInteger.reduction_surjective n a
    exact
      ⟨QuotientAddGroup.mk'
          (nsmulWithin (⊤ : AddSubgroup ProfiniteInteger) n)
          ⟨z, AddSubgroup.mem_top z⟩,
        hz⟩

/-- The quotient used by the norm has the field's positive degree
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Valuation.lean:141`). -/
@[simp] theorem FiniteAbstractField.normToBase_index_eq_degree
    (K : FiniteAbstractField G) :
    (K.field.toSubgroup.subgroupOf (baseField G).toSubgroup).index =
      (K.toFiniteAbstractExtension.degree : ℕ) :=
  K.toFiniteAbstractExtension.subgroup_index_eq_degree

/-- **The valuation datum** — the henselian-valuation axiom of the engine:
`integers_mem` and `canonical_value_quotient_bijective` are its condition (i),
`norm_range` its condition (ii) (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Valuation.lean:153`). -/
structure ValuationData (D : DegreeData G) (A : Rep ℤ G) where
  /-- The additive valuation on the base-field fixed module. -/
  toAddMonoidHom : ambientFixedAddSubgroup A (baseField G) →+ ProfiniteInteger
  /-- Every integral value occurs. -/
  integers_mem : ∀ m : ℤ,
    (Int.castRingHom ProfiniteInteger) m ∈ toAddMonoidHom.range
  /-- Reduction of the value group modulo every positive modulus is bijective
  through the canonical map. -/
  canonical_value_quotient_bijective : ∀ (n : ℕ) [NeZero n],
    Function.Bijective (canonicalValueQuotientMap toAddMonoidHom.range n)
  /-- Norms from a finite abstract field have image `f_K·Z`. -/
  norm_range : ∀ K : FiniteAbstractField G,
    (toAddMonoidHom.comp (normToBase A K.field)).range =
      nsmulImage toAddMonoidHom.range (K.residueDegree D : ℕ)

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- The value group `Z = v(A_k)`. -/
def valueGroup (v : ValuationData D A) : AddSubgroup ProfiniteInteger :=
  v.toAddMonoidHom.range

/-- The axiom's canonical map at the value group. -/
def canonicalQuotientMap (v : ValuationData D A) (n : ℕ) [NeZero n] :
    (v.valueGroup ⧸ nsmulWithin v.valueGroup n) →+ ZMod n :=
  canonicalValueQuotientMap v.valueGroup n

/-- **The cyclic value quotients**, derived from the axiom's bijectivity
(Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Valuation.lean:185`). -/
def cyclic_value_quotients (v : ValuationData D A) (n : ℕ) [NeZero n] :
    (v.valueGroup ⧸ nsmulWithin v.valueGroup n) ≃+ ZMod n :=
  AddEquiv.ofBijective (v.canonicalQuotientMap n)
    (v.canonical_value_quotient_bijective n)

/-- Canonical reduction of the value group modulo `n`. -/
def valueModulo (v : ValuationData D A) (n : ℕ) [NeZero n] :
    v.valueGroup →+ ZMod n :=
  (v.cyclic_value_quotients n).toAddMonoidHom.comp
    (QuotientAddGroup.mk' (nsmulWithin v.valueGroup n))

/-- Value modulo `n` is reduction of the underlying value. -/
@[simp]
theorem valueModulo_apply (v : ValuationData D A) (n : ℕ) [NeZero n]
    (z : v.valueGroup) :
    v.valueModulo n z = ProfiniteInteger.reduction n (z : ProfiniteInteger) :=
  rfl

/-- Reduction of the value group modulo a positive modulus is surjective. -/
theorem valueModulo_surjective (v : ValuationData D A) (n : ℕ) [NeZero n] :
    Function.Surjective (v.valueModulo n) := by
  intro z
  obtain ⟨q, rfl⟩ := (v.cyclic_value_quotients n).surjective z
  refine Quotient.inductionOn' q ?_
  intro a
  exact ⟨a, rfl⟩

/-- The composite `v ∘ N_{K|k}` before division. -/
def normCompositeAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ ProfiniteInteger :=
  v.toAddMonoidHom.comp (normToBase A K.field)

/-- The composite has range the residue-degree multiple image. -/
theorem normCompositeAt_range (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    (v.normCompositeAt K).range =
      nsmulImage v.valueGroup (K.residueDegree D : ℕ) :=
  v.norm_range K

/-- `v(N_{K|k}a)` placed in `f_K·ℤ̂`. -/
def normCompositeAtInSpan (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+
      ProfiniteInteger.spanAddSubgroup (K.residueDegree D : ℕ) where
  toFun a := ⟨v.normCompositeAt K a, by
    have ha : v.normCompositeAt K a ∈ (v.normCompositeAt K).range := ⟨a, rfl⟩
    rw [v.normCompositeAt_range K] at ha
    obtain ⟨z, _hz, hz⟩ := ha
    refine (ProfiniteInteger.mem_spanAddSubgroup_iff _).mpr ⟨z, ?_⟩
    rw [← hz]
    exact (nsmul_eq_mul _ _).symm⟩
  map_zero' := by ext; simp [normCompositeAt]
  map_add' x y := by
    apply Subtype.ext
    exact map_add (v.normCompositeAt K) x y

/-- Division by `f_K` before the codomain restriction. -/
def dividedAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ ProfiniteInteger :=
  (ProfiniteInteger.divide (K.residueDegree D : ℕ)).toAddMonoidHom.comp
    (v.normCompositeAtInSpan K)

/-- **The defining identity** `f_K·v_K = v ∘ N_{K|k}`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Valuation.lean:249`). -/
theorem residueDegree_nsmul_dividedAt (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    (K.residueDegree D : ℕ) • v.dividedAt K a = v.normCompositeAt K a := by
  rw [nsmul_eq_mul]
  exact ProfiniteInteger.mul_divide (K.residueDegree D : ℕ)
    (v.normCompositeAtInSpan K a)

/-- The divided value lies in the value group. -/
theorem dividedAt_mem_valueGroup (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    v.dividedAt K a ∈ v.valueGroup := by
  have ha : v.normCompositeAt K a ∈ (v.normCompositeAt K).range := ⟨a, rfl⟩
  rw [v.normCompositeAt_range K] at ha
  obtain ⟨z, hzZ, hz⟩ := ha
  have hzSubtype : v.normCompositeAtInSpan K a =
      ⟨(↑(K.residueDegree D : ℕ) : ProfiniteInteger) * z,
        (ProfiniteInteger.mem_spanAddSubgroup_iff _).mpr ⟨z, rfl⟩⟩ := by
    apply Subtype.ext
    change v.normCompositeAt K a =
      (↑(K.residueDegree D : ℕ) : ProfiniteInteger) * z
    rw [← hz]
    exact nsmul_eq_mul _ _
  change ProfiniteInteger.divide (K.residueDegree D : ℕ)
    (v.normCompositeAtInSpan K a) ∈ v.valueGroup
  rw [hzSubtype, ProfiniteInteger.divide_mul]
  exact hzZ

/-- **The normalized valuation** `v_K = (1/f_K)·(v ∘ N_{K|k})`, with the exact
value-group codomain (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Valuation.lean:279`). -/
def valuationAt (v : ValuationData D A) (K : FiniteAbstractField G) :
    ambientFixedAddSubgroup A K.field →+ v.valueGroup :=
  (v.dividedAt K).codRestrict v.valueGroup
    (fun a => v.dividedAt_mem_valueGroup K a)

/-- The underlying value of the normalized valuation is the divided value. -/
@[simp]
theorem valuationAt_coe (v : ValuationData D A) (K : FiniteAbstractField G)
    (a : ambientFixedAddSubgroup A K.field) :
    (v.valuationAt K a : ProfiniteInteger) = v.dividedAt K a :=
  rfl

/-- **Every normalized valuation maps onto the value group**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Valuation.lean:292`). -/
theorem normalizedValuation_surjective (v : ValuationData D A)
    (K : FiniteAbstractField G) :
    Function.Surjective (v.valuationAt K) := by
  intro z
  have hzImage : (K.residueDegree D : ℕ) • z.1 ∈
      nsmulImage v.valueGroup (K.residueDegree D : ℕ) :=
    ⟨z.1, z.2, rfl⟩
  rw [← v.normCompositeAt_range K] at hzImage
  obtain ⟨a, ha⟩ := hzImage
  refine ⟨a, ?_⟩
  apply Subtype.ext
  change ProfiniteInteger.divide (K.residueDegree D : ℕ)
    (v.normCompositeAtInSpan K a) = z.1
  have hsub : v.normCompositeAtInSpan K a =
      ⟨(↑(K.residueDegree D : ℕ) : ProfiniteInteger) * z.1,
        (ProfiniteInteger.mem_spanAddSubgroup_iff _).mpr ⟨z.1, rfl⟩⟩ := by
    apply Subtype.ext
    change v.normCompositeAt K a =
      (↑(K.residueDegree D : ℕ) : ProfiniteInteger) * z.1
    rw [ha]
    exact nsmul_eq_mul _ _
  rw [hsub, ProfiniteInteger.divide_mul]

end ValuationData

end

end Atlas.Knowledge
