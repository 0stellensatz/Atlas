import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup

/-!
# relative norm on abstract fields

The norm of a finite extension of abstract fields, on the fixed coefficient
modules: the sum over the left cosets of `G_L` in `G_K` — the additive form of
the product over conjugates — landing in the base field's fixed module by coset
reindexing. Nothing requires the extension to be Galois: a fixed coefficient
gives a well-defined value on each coset, and left multiplication permutes the
cosets.

## Main definitions

* `relativeCosetAction` — the value of a fixed coefficient at a left coset.
* `relativeNormValue` — the coset sum in the ambient module.
* `relativeNorm` — the norm `A_L →+ A_K` of a finite abstract extension.

## Main statements

* `relativeNormValue_fixed` — the norm value is fixed by the base subgroup;
  proved.
* `relativeNorm_apply_coe` — the norm is the explicit coset sum; proved.

## Implementation notes

The coset permutation used in the reindexing is Mathlib's `MulAction.toPerm`
for the left action on the quotient, where the source bundles its own
equivalence; the relative subgroup is `Subgroup.subgroupOf`, as across the
layer. The ambient group is universe-general: only the engine's own
instantiation pins `Type 0`. The norm value `relativeNormValue` is its own
definition so the fixedness proof can name it before the bundling.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- **The value of a fixed coefficient at a left coset** — independent of the
representative exactly because the coefficient is fixed by the smaller subgroup
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Norm.lean:30`][Yamaguchi2026]). -/
def relativeCosetAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) : A.V :=
  Quotient.liftOn' q (fun k : K.toSubgroup => A.ρ k.1 a.1) (by
    intro x y hxy
    have hmem : x⁻¹ * y ∈ L.toSubgroup.subgroupOf K.toSubgroup :=
      QuotientGroup.leftRel_apply.mp hxy
    let l : L.toSubgroup := ⟨(x⁻¹ * y).1, hmem⟩
    have hy : y = x * ⟨l.1, hLK l.2⟩ := by
      apply Subtype.ext
      simp [l]
    rw [hy]
    change A.ρ x.1 a.1 = A.ρ (x.1 * l.1) a.1
    rw [map_mul]
    change A.ρ x.1 a.1 = A.ρ x.1 (A.ρ l.1 a.1)
    rw [a.2 l])

/-- The coset action computes on representatives. -/
@[simp]
theorem relativeCosetAction_mk
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A L) (k : K.toSubgroup) :
    relativeCosetAction A K L hLK a (QuotientGroup.mk k) = A.ρ k.1 a.1 :=
  rfl

/-- **The additive norm value**: the sum over the left cosets
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Norm.lean:73`][Yamaguchi2026]). -/
def relativeNormValue
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A L) : A.V := by
  letI := Fintype.ofFinite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
  exact ∑ q, relativeCosetAction A K L hLK a q

/-- The coset action is additive in the fixed element. -/
theorem relativeCosetAction_add
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a b : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :
    relativeCosetAction A K L hLK (a + b) q =
      relativeCosetAction A K L hLK a q +
        relativeCosetAction A K L hLK b q := by
  refine Quotient.inductionOn' q ?_
  intro k
  simp only [relativeCosetAction_mk]
  exact map_add (A.ρ k.1) a.1 b.1

/-- Every coset acts trivially on the zero fixed element. -/
@[simp]
theorem relativeCosetAction_zero
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :
    relativeCosetAction A K L hLK 0 q = 0 := by
  refine Quotient.inductionOn' q ?_
  intro k
  simp only [relativeCosetAction_mk]
  exact map_zero (A.ρ k.1)

/-- **The norm value is fixed by the base subgroup**: the action permutes the
cosets and the sum reindexes
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Norm.lean:108`][Yamaguchi2026]). -/
theorem relativeNormValue_fixed
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A L) (k : K.toSubgroup) :
    A.ρ k.1 (relativeNormValue A K L hLK a) =
      relativeNormValue A K L hLK a := by
  letI := Fintype.ofFinite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
  have hterm : ∀ q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup,
      A.ρ k.1 (relativeCosetAction A K L hLK a q) =
        relativeCosetAction A K L hLK a (MulAction.toPerm k q) := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    change A.ρ k.1 (A.ρ x.1 a.1) =
      relativeCosetAction A K L hLK a (QuotientGroup.mk (k * x))
    rw [relativeCosetAction_mk]
    change A.ρ k.1 (A.ρ x.1 a.1) = A.ρ (k.1 * x.1) a.1
    rw [map_mul]
    rfl
  rw [relativeNormValue]
  simp_rw [map_sum, hterm]
  exact Equiv.sum_comp (MulAction.toPerm k) (relativeCosetAction A K L hLK a)

/-- **The relative norm of a finite abstract extension**: the coset sum, with
its fixedness, landing in the base field's fixed module
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Norm.lean:137`][Yamaguchi2026]). -/
def relativeNorm
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    ambientFixedAddSubgroup A L →+ ambientFixedAddSubgroup A K where
  toFun a := ⟨relativeNormValue A K L hLK a,
    relativeNormValue_fixed A K L hLK a⟩
  map_zero' := by
    apply Subtype.ext
    letI := Fintype.ofFinite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    simp [relativeNormValue]
  map_add' a b := by
    apply Subtype.ext
    letI := Fintype.ofFinite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    simp only [AddSubgroup.coe_add, relativeNormValue]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    exact relativeCosetAction_add A K L hLK a b q

/-- The relative norm is the explicit coset sum. -/
@[simp]
theorem relativeNorm_apply_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : ambientFixedAddSubgroup A L) :
    ((relativeNorm A K L hLK a : ambientFixedAddSubgroup A K) : A.V) =
      relativeNormValue A K L hLK a :=
  rfl

end

end Atlas.Knowledge
