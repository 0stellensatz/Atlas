import Mathlib
import Atlas.Knowledge.IntegerIsIntegralClosure
import Atlas.Knowledge.StandardLubinTateGaloisDescription
import Atlas.Knowledge.StandardLubinTateLevelField

/-!
# standard Lubin–Tate compositum

The common carrier of the changed-uniformizer comparison: the join of two standard
level fields inside the separable closure, with both level generators transported in as
integral primitive roots. The transport is the level-field pattern: the generators'
annihilation descends from the chosen roots in the separable closure through the
injective embedding, integrality is forced by the monic integral primitive polynomial,
and the integer-level identity rides the hand-supplied integer scalar tower. With both
roots in one carrier, the root-proximity gap and the conjugate ceiling apply
simultaneously — the Krasner argument's stage.

## Main definitions

* `standardLubinTateCompositum` — the join, as an intermediate field of the separable
  closure.
* `compositumGenerator` / `compositumGenerator'` — the two level generators read in the
  compositum.
* `compositumGeneratorInteger` / `compositumGeneratorInteger'` — the two generators as
  integers of the compositum.

## Main statements

* `standardLubinTateCompositum_finiteDimensional` — finite over the base; proved.
* `standardLubinTateCompositum_isGalois` — the join of two Galois intermediates is
  Galois; proved.
* `aeval_compositumGenerator_field` / `aeval_compositumGenerator'_field` — the
  field-level annihilations; proved.
* `val_compositumGenerator` / `val_compositumGenerator'` — the way back to the chosen
  roots of the separable closure; proved.
* `aeval_compositumGeneratorInteger` / `aeval_compositumGeneratorInteger'` — the
  integral primitive-root identities; proved.

## Implementation notes

The two parameters are abstract irreducibles `π, π′` rather than `π` and `πu` — the
join and the transports do not see the unit; the Krasner consumer instantiates
`π′ := π u`. The local-field structure on the compositum is hypothesized in the integer
section, as in `Atlas.Knowledge.StandardLubinTateGaloisDescription`, and obtained by the
consumer from `Atlas.Knowledge.exists_extension_isMixedCharLocalField`; the field-level
statements need none of it. The integer scalar tower is supplied by hand as
`Valuation.HasExtension.instIsScalarTowerInteger`, the known instance seam.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section Compositum

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable {π π' : ↥𝒪[K]} (hπ : Irreducible π) (hπ' : Irreducible π') (n : ℕ)

/-- The **compositum of two standard level fields** inside the separable closure — the
common carrier of the changed-uniformizer comparison
([Yamaguchi 2026, `LubinTate/FiniteLevel/ChangedLevelCompositum.lean:37`]
[Yamaguchi2026] — the source's join is the same, specialized there to `π` and `πu`). -/
noncomputable def standardLubinTateCompositum : IntermediateField K (SeparableClosure K) :=
  standardLubinTateLevelField K hπ n ⊔ standardLubinTateLevelField K hπ' n

/-- The compositum is finite over the base. -/
instance standardLubinTateCompositum_finiteDimensional :
    FiniteDimensional K ↥(standardLubinTateCompositum K hπ hπ' n) := by
  unfold standardLubinTateCompositum
  infer_instance

/-- **The compositum is Galois over the base**: the join of two Galois intermediates of
the separable closure ([Milne 2020, Chap. I, §3, Thm. 3.6 (b), p.38][MilneCFT] — each
level is abelian, so the join is Galois;
[Yamaguchi 2026, `LubinTate/FiniteLevel/ChangedLevelCompositum.lean:85`]
[Yamaguchi2026]). -/
theorem standardLubinTateCompositum_isGalois :
    IsGalois K ↥(standardLubinTateCompositum K hπ hπ' n) := by
  haveI h1 := standardLubinTateLevelField_isGalois K hπ n
  haveI h2 := standardLubinTateLevelField_isGalois K hπ' n
  haveI : Normal K ↥(standardLubinTateLevelField K hπ n) := h1.to_normal
  haveI : Normal K ↥(standardLubinTateLevelField K hπ' n) := h2.to_normal
  unfold standardLubinTateCompositum
  constructor

/-- The first level generator, read in the compositum. -/
noncomputable def compositumGenerator :
    ↥(standardLubinTateCompositum K hπ hπ' n) :=
  IntermediateField.inclusion le_sup_left (standardLubinTateLevelGenerator K hπ n)

/-- The second level generator, read in the compositum. -/
noncomputable def compositumGenerator' :
    ↥(standardLubinTateCompositum K hπ hπ' n) :=
  IntermediateField.inclusion le_sup_right (standardLubinTateLevelGenerator K hπ' n)

/-- The first generator satisfies its primitive polynomial over the base field. -/
theorem aeval_compositumGenerator_field :
    Polynomial.aeval (compositumGenerator K hπ hπ' n)
      (standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n) = 0 := by
  have hroot := chosenStandardLubinTatePrimitiveRoot_isRoot K hπ n
  rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hroot
  have hinj : Function.Injective (standardLubinTateCompositum K hπ hπ' n).val :=
    (standardLubinTateCompositum K hπ hπ' n).val.toRingHom.injective
  apply hinj
  rw [map_zero, ← Polynomial.aeval_algHom_apply]
  exact hroot

/-- The second generator satisfies its primitive polynomial over the base field. -/
theorem aeval_compositumGenerator'_field :
    Polynomial.aeval (compositumGenerator' K hπ hπ' n)
      (standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π' n) = 0 := by
  have hroot := chosenStandardLubinTatePrimitiveRoot_isRoot K hπ' n
  rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hroot
  have hinj : Function.Injective (standardLubinTateCompositum K hπ hπ' n).val :=
    (standardLubinTateCompositum K hπ hπ' n).val.toRingHom.injective
  apply hinj
  rw [map_zero, ← Polynomial.aeval_algHom_apply]
  exact hroot

/-- The way out of the carrier: the first generator reads back to the chosen root. -/
theorem val_compositumGenerator :
    (standardLubinTateCompositum K hπ hπ' n).val (compositumGenerator K hπ hπ' n) =
      chosenStandardLubinTatePrimitiveRoot K hπ n := rfl

/-- The way out of the carrier: the second generator reads back to the chosen root. -/
theorem val_compositumGenerator' :
    (standardLubinTateCompositum K hπ hπ' n).val (compositumGenerator' K hπ hπ' n) =
      chosenStandardLubinTatePrimitiveRoot K hπ' n := rfl

section Integer

variable [ValuativeRel ↥(standardLubinTateCompositum K hπ hπ' n)]
  [TopologicalSpace ↥(standardLubinTateCompositum K hπ hπ' n)]
  [ValuativeExtension K ↥(standardLubinTateCompositum K hπ hπ' n)]
  [IsMixedCharLocalField ↥(standardLubinTateCompositum K hπ hπ' n)]

omit [TopologicalSpace ↥(standardLubinTateCompositum K hπ hπ' n)]
  [IsMixedCharLocalField ↥(standardLubinTateCompositum K hπ hπ' n)] in
/-- The first generator is an integer of the compositum. -/
theorem compositumGenerator_mem_integer :
    compositumGenerator K hπ hπ' n ∈ 𝒪[↥(standardLubinTateCompositum K hπ hπ' n)] := by
  rw [mem_integer_iff_isIntegral K]
  exact ⟨standardLubinTatePrimitivePolynomial ↥𝒪[K] π n,
    standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n,
    by rw [← Polynomial.aeval_def]
       have := aeval_compositumGenerator_field K hπ hπ' n
       rwa [standardLubinTatePrimitivePolynomialOverField,
         Polynomial.aeval_map_algebraMap] at this⟩

omit [TopologicalSpace ↥(standardLubinTateCompositum K hπ hπ' n)]
  [IsMixedCharLocalField ↥(standardLubinTateCompositum K hπ hπ' n)] in
/-- The second generator is an integer of the compositum. -/
theorem compositumGenerator'_mem_integer :
    compositumGenerator' K hπ hπ' n ∈ 𝒪[↥(standardLubinTateCompositum K hπ hπ' n)] := by
  rw [mem_integer_iff_isIntegral K]
  exact ⟨standardLubinTatePrimitivePolynomial ↥𝒪[K] π' n,
    standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π' n,
    by rw [← Polynomial.aeval_def]
       have := aeval_compositumGenerator'_field K hπ hπ' n
       rwa [standardLubinTatePrimitivePolynomialOverField,
         Polynomial.aeval_map_algebraMap] at this⟩

/-- The first generator as an integer of the compositum. -/
noncomputable def compositumGeneratorInteger :
    ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)] :=
  ⟨compositumGenerator K hπ hπ' n, compositumGenerator_mem_integer K hπ hπ' n⟩

/-- The second generator as an integer of the compositum. -/
noncomputable def compositumGeneratorInteger' :
    ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)] :=
  ⟨compositumGenerator' K hπ hπ' n, compositumGenerator'_mem_integer K hπ hπ' n⟩

omit [TopologicalSpace ↥(standardLubinTateCompositum K hπ hπ' n)]
  [IsMixedCharLocalField ↥(standardLubinTateCompositum K hπ hπ' n)] in
/-- The first generator is an integral primitive root in the compositum. -/
theorem aeval_compositumGeneratorInteger :
    Polynomial.aeval (compositumGeneratorInteger K hπ hπ' n)
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0 := by
  letI : IsScalarTower ↥𝒪[K] ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)]
      ↥(standardLubinTateCompositum K hπ hπ' n) :=
    Valuation.HasExtension.instIsScalarTowerInteger
      (vR := valuation K) (vA := valuation ↥(standardLubinTateCompositum K hπ hπ' n))
  apply Subtype.ext
  change (IsScalarTower.toAlgHom ↥𝒪[K] ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)]
      ↥(standardLubinTateCompositum K hπ hπ' n))
    ((Polynomial.aeval (compositumGeneratorInteger K hπ hπ' n))
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n)) =
    ((0 : ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)]) :
      ↥(standardLubinTateCompositum K hπ hπ' n))
  rw [← Polynomial.aeval_algHom_apply, ZeroMemClass.coe_zero]
  have := aeval_compositumGenerator_field K hπ hπ' n
  rwa [standardLubinTatePrimitivePolynomialOverField,
    Polynomial.aeval_map_algebraMap] at this

omit [TopologicalSpace ↥(standardLubinTateCompositum K hπ hπ' n)]
  [IsMixedCharLocalField ↥(standardLubinTateCompositum K hπ hπ' n)] in
/-- The second generator is an integral primitive root in the compositum. -/
theorem aeval_compositumGeneratorInteger' :
    Polynomial.aeval (compositumGeneratorInteger' K hπ hπ' n)
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] π' n) = 0 := by
  letI : IsScalarTower ↥𝒪[K] ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)]
      ↥(standardLubinTateCompositum K hπ hπ' n) :=
    Valuation.HasExtension.instIsScalarTowerInteger
      (vR := valuation K) (vA := valuation ↥(standardLubinTateCompositum K hπ hπ' n))
  apply Subtype.ext
  change (IsScalarTower.toAlgHom ↥𝒪[K] ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)]
      ↥(standardLubinTateCompositum K hπ hπ' n))
    ((Polynomial.aeval (compositumGeneratorInteger' K hπ hπ' n))
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] π' n)) =
    ((0 : ↥𝒪[↥(standardLubinTateCompositum K hπ hπ' n)]) :
      ↥(standardLubinTateCompositum K hπ hπ' n))
  rw [← Polynomial.aeval_algHom_apply, ZeroMemClass.coe_zero]
  have := aeval_compositumGenerator'_field K hπ hπ' n
  rwa [standardLubinTatePrimitivePolynomialOverField,
    Polynomial.aeval_map_algebraMap] at this

end Integer

end Compositum

end Atlas.Knowledge
