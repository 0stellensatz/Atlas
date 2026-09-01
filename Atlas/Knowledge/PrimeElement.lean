import Mathlib
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.NormalizedValuationLaws

/-!
# prime elements of a valuation datum

The engine's prime elements: an element of the fixed module of a finite
abstract field whose normalized valuation is the distinguished value `1`,
and the additive unit group as the valuation's kernel. Against the
norm–valuation formula the two ramification degeneracies follow: an
unramified extension restricts the valuation above to the valuation below,
so primes stay prime under inclusion; a totally ramified extension has
relative residue degree one, so norms of primes are prime (#104).

## Main definitions

* `ValuationData.oneValue` — the value `1`, in the value group.
* `ValuationData.IsPrimeElement` — normalized value `1`.
* `ValuationData.unitAddSubgroup` — the kernel of the normalized valuation.

## Main statements

* `ValuationData.valuationAt_fixedFieldInclusion_of_unramified` — over an
  unramified extension the valuation restricts; proved.
* `ValuationData.prime_of_unramified` — primes stay prime in an unramified
  extension; proved.
* `ValuationData.norm_prime_of_totallyRamified` — norms of primes are prime
  in a totally ramified extension; proved.

## Implementation notes

The source's norm-of-inclusion rewrite closes with `simpa`; in the layer the
simplified sides are definitionally equal only at default transparency, which
`simpa`'s closing reducible-transparency check does not reach, so the bridge
is a definitional `show … from` on the underlying finite extension and the
source's local `let` for it is dropped.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {D : DegreeData G} {A : Rep ℤ G}

namespace ValuationData

/-- **The value `1` in the value group**, by the integral-values axiom
([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/PrimeElements.lean:102`][Yamaguchi2026]). -/
def oneValue (v : ValuationData D A) : v.valueGroup :=
  ⟨1, by
    obtain ⟨a, ha⟩ := v.integers_mem 1
    exact ⟨a, by simpa using ha⟩⟩

/-- The distinguished value reads as `1` in `ℤ̂` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/PrimeElements.lean:109`][Yamaguchi2026]). -/
@[simp]
theorem oneValue_coe (v : ValuationData D A) :
    (v.oneValue : ProfiniteInteger) = 1 :=
  rfl

/-- **A prime element**: normalized value `1` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/PrimeElements.lean:114`][Yamaguchi2026]). -/
def IsPrimeElement (v : ValuationData D A) (K : FiniteAbstractField G)
    (π : ambientFixedAddSubgroup A K.field) : Prop :=
  v.valuationAt K π = v.oneValue

/-- **The additive unit group** `U_K = {u | v_K(u) = 0}` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/PrimeElements.lean:120`][Yamaguchi2026]). -/
def unitAddSubgroup (v : ValuationData D A) (K : FiniteAbstractField G) :
    AddSubgroup (ambientFixedAddSubgroup A K.field) :=
  (v.valuationAt K).ker

/-- Membership in the unit group is vanishing normalized valuation
([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/PrimeElements.lean:126`][Yamaguchi2026]). -/
@[simp]
theorem mem_unitAddSubgroup_iff (v : ValuationData D A)
    (K : FiniteAbstractField G)
    (u : ambientFixedAddSubgroup A K.field) :
    u ∈ v.unitAddSubgroup K ↔ v.valuationAt K u = 0 :=
  Iff.rfl

/-- **Over an unramified extension the normalized valuation restricts to the
valuation below** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/PrimeElements.lean:134`][Yamaguchi2026]). -/
theorem valuationAt_fixedFieldInclusion_of_unramified
    (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hUn : E.IsUnramified D)
    (a : ambientFixedAddSubgroup A E.base.field) :
    v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below a) =
      v.valuationAt E.base a := by
  have hfeq : (E.residueDegree D : ℕ) = (E.degree : ℕ) :=
    E.residueDegree_eq_degree_of_isUnramified D hUn
  apply Subtype.ext
  apply ProfiniteInteger.nsmul_left_injective (E.residueDegree D).pos.ne'
  calc
    (E.residueDegree D : ℕ) •
        ((v.valuationAt E.field
          (fixedFieldInclusion A E.base.field E.field.field E.below a) :
          v.valueGroup) : ProfiniteInteger) =
      ((v.valuationAt E.base
        (relativeNorm A E.base.field E.field.field E.below
          (fixedFieldInclusion A E.base.field E.field.field E.below a)) :
          v.valueGroup) : ProfiniteInteger) :=
        v.normalizedValuation_tower E
          (fixedFieldInclusion A E.base.field E.field.field E.below a)
    _ = ((v.valuationAt E.base ((E.degree : ℕ) • a) :
          v.valueGroup) : ProfiniteInteger) := by
        rw [show relativeNorm A E.base.field E.field.field E.below
            (fixedFieldInclusion A E.base.field E.field.field E.below a) =
              (E.degree : ℕ) • a from
          relativeNorm_fixedFieldInclusion A E.toFiniteAbstractExtension a]
    _ = (E.degree : ℕ) •
        ((v.valuationAt E.base a : v.valueGroup) : ProfiniteInteger) :=
      congrArg Subtype.val
        (map_nsmul (v.valuationAt E.base) (E.degree : ℕ) a)
    _ = (E.residueDegree D : ℕ) •
        ((v.valuationAt E.base a : v.valueGroup) : ProfiniteInteger) := by
      rw [hfeq]

/-- **A prime element remains prime in an unramified extension**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/PrimeElements.lean:175`][Yamaguchi2026]). -/
theorem prime_of_unramified (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hUn : E.IsUnramified D)
    (π : ambientFixedAddSubgroup A E.base.field)
    (hπ : v.IsPrimeElement E.base π) :
    v.IsPrimeElement E.field
      (fixedFieldInclusion A E.base.field E.field.field E.below π) := by
  rw [IsPrimeElement,
    v.valuationAt_fixedFieldInclusion_of_unramified E hUn π]
  exact hπ

/-- **The norm of a prime element is prime in a totally ramified extension**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/PrimeElements.lean:187`][Yamaguchi2026]). -/
theorem norm_prime_of_totallyRamified (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hTot : E.IsTotallyRamified D)
    (π : ambientFixedAddSubgroup A E.field.field) :
    v.IsPrimeElement E.field π →
      v.IsPrimeElement E.base
        (relativeNorm A E.base.field E.field.field E.below π) := by
  intro hπ
  have htower := v.normalizedValuation_tower E π
  have hresidue : (E.residueDegree D : ℕ) = 1 :=
    E.toFiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified
      D hTot
  change (E.residueDegree D : ℕ) •
      ((v.valuationAt E.field π : v.valueGroup) : ProfiniteInteger) =
    ((v.valuationAt E.base
      (relativeNorm A E.base.field E.field.field E.below π) :
        v.valueGroup) : ProfiniteInteger) at htower
  rw [hresidue, one_nsmul] at htower
  rw [IsPrimeElement] at hπ ⊢
  apply Subtype.ext
  exact htower.symm.trans (congrArg Subtype.val hπ)

end ValuationData

end

end Atlas.Knowledge
