import Mathlib
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.RelativeNorm

/-!
# norms of elements fixed over the base

The inclusion `A_K → A_L` of fixed coefficient groups along an abstract
extension, and the two norm identities for elements that are already fixed:
the norm of an included element is its degree-fold sum, and the norm of the
trivial extension is the identity. These are the degenerate norm laws the
finite norm quotient's torsion bound and the reciprocity construction's
prime-element bookkeeping read (#104).

## Main definitions

* `fixedFieldInclusion` — the inclusion `A_K → A_L`.

## Main statements

* `relativeNorm_fixedFieldInclusion` — the norm of an included element is
  `[L:K]` times it; proved.
* `relativeNorm_self` — the norm of the trivial extension is the identity;
  proved.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The inclusion `A_K → A_L`** for an abstract extension `L | K`
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/PrimeElements.lean:23`]
[Yamaguchi2026]). -/
def fixedFieldInclusion (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup) :
    ambientFixedAddSubgroup A K →+ ambientFixedAddSubgroup A L where
  toFun a := ⟨a.1, fun l => a.2 ⟨l.1, hLK l.2⟩⟩
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The inclusion keeps the ambient coefficient ([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/PrimeElements.lean:35`][Yamaguchi2026]). -/
@[simp]
theorem fixedFieldInclusion_coe (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A K) :
    ((fixedFieldInclusion A K L hLK a :
      ambientFixedAddSubgroup A L) : A.V) = a.1 :=
  rfl

/-- **The norm of an element fixed over `K` is its `[L:K]`-fold sum**
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/PrimeElements.lean:42`]
[Yamaguchi2026]). -/
theorem relativeNorm_fixedFieldInclusion
    (A : Rep ℤ G) (E : FiniteAbstractExtension G)
    (a : ambientFixedAddSubgroup A E.base) :
    relativeNorm A E.base E.field E.below
        (fixedFieldInclusion A E.base E.field E.below a) =
      (E.degree : ℕ) • a := by
  apply Subtype.ext
  letI := Fintype.ofFinite
    (E.base.toSubgroup ⧸ E.field.toSubgroup.subgroupOf E.base.toSubgroup)
  have hterm : ∀ q : E.base.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf E.base.toSubgroup,
      relativeCosetAction A E.base E.field E.below
        (fixedFieldInclusion A E.base E.field E.below a) q = a.1 := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro k
    rw [relativeCosetAction_mk, fixedFieldInclusion_coe]
    exact a.2 k
  simp only [relativeNorm_apply_coe, relativeNormValue]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ]
  change Fintype.card (E.base.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf E.base.toSubgroup) • a.1 =
    (E.degree : ℕ) • a.1
  rw [← E.subgroup_index_eq_degree,
    Subgroup.index, Nat.card_eq_fintype_card]

/-- **The norm of the trivial extension is the identity** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/PrimeElements.lean:71`][Yamaguchi2026]). -/
@[simp]
theorem relativeNorm_self
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    [Finite (K.toSubgroup ⧸ K.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A K) :
    relativeNorm A K K le_rfl a = a := by
  apply Subtype.ext
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ K.toSubgroup.subgroupOf K.toSubgroup)
  have hterm : ∀ q : K.toSubgroup ⧸ K.toSubgroup.subgroupOf K.toSubgroup,
      relativeCosetAction A K K le_rfl a q = a.1 := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro k
    rw [relativeCosetAction_mk]
    exact a.2 k
  simp only [relativeNorm_apply_coe, relativeNormValue]
  simp_rw [hterm]
  rw [Finset.sum_const, Finset.card_univ]
  have htop : K.toSubgroup.subgroupOf K.toSubgroup = ⊤ :=
    Subgroup.subgroupOf_self _
  have hcard :
      Fintype.card
        (K.toSubgroup ⧸ K.toSubgroup.subgroupOf K.toSubgroup) = 1 := by
    rw [← Nat.card_eq_fintype_card,
      ← Subgroup.index_eq_card (K.toSubgroup.subgroupOf K.toSubgroup),
      htop, Subgroup.index_top]
  rw [hcard, one_nsmul]

end

end Atlas.Knowledge
