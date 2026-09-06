import Mathlib
import Atlas.Knowledge.NormalizedDegree

/-!
# Frobenius elements over a finite Galois extension

The Frobenius semigroup `Frob(L̃|K)` inside the relative maximal-unramified
Galois group: the classes whose normalized degree is a strictly positive natural
power of the generator — positivity carried explicitly, so `0 ∉ ℕ` survives the
encoding. Restriction to `G(L|K)` maps this semigroup onto the finite Galois
group: every class of a finite cyclic quotient of `ℤ̂` is represented by a
strictly positive multiple of `1`, and correcting a preimage by an extension
element realizes it.

## Main definitions

* `DegreeData.extensionInertiaWithin` — `I_L` inside `G_K`, the subgroup of
  `L̃`.
* `DegreeData.extensionNormalizedDegree` — `d_K` factored through
  `G(L̃|K)`.
* `DegreeData.extensionRestriction` — `G(L̃|K) → G(L|K)`.
* `DegreeData.FrobeniusElements` — the Frobenius semigroup carrier.
* `DegreeData.frobeniusRestriction` — its restriction to `G(L|K)`.

## Main statements

* `exists_positive_nsmul_one_sub_mem_of_index_ne_zero` — every class of a
  finite quotient of `ℤ̂` has a strictly positive representative; proved.
* `DegreeData.frobeniusRestriction_surjective` — the Frobenius semigroup
  restricts onto the finite Galois group; proved.

## Implementation notes

The positive-representative lemma reads the classification of finite-index
subgroups of `ℤ̂` through the ideal identity
`Atlas.Knowledge.ProfiniteInteger.span_natCast_eq_ker_reduction`, shifting a
residue by the modulus to force positivity. The relative subgroup is
`Subgroup.subgroupOf`, as across the layer, and the underscore-named
containments enter only as semantic guards, as in
`Atlas.Knowledge.extensionFixedRepresentation`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **Every class of a finite cyclic quotient of `ℤ̂` has a strictly positive
representative**: shift the residue by the modulus (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/FrobeniusLift.lean:23`). -/
theorem exists_positive_nsmul_one_sub_mem_of_index_ne_zero
    (H : AddSubgroup ProfiniteInteger) (hH : H.index ≠ 0) (z : ProfiniteInteger) :
    ∃ n : ℕ, 0 < n ∧ z - n • (1 : ProfiniteInteger) ∈ H := by
  set m := H.index with hm'
  haveI : NeZero m := ⟨hH⟩
  let r : ZMod m := ProfiniteInteger.reduction m z
  let n : ℕ := r.val + m
  refine ⟨n, Nat.add_pos_right r.val (Nat.pos_of_ne_zero hH), ?_⟩
  rw [ProfiniteInteger.addSubgroup_eq_spanAddSubgroup_of_index_ne_zero H hH]
  rw [← hm']
  change z - n • (1 : ProfiniteInteger) ∈ Ideal.span {(m : ProfiniteInteger)}
  rw [ProfiniteInteger.span_natCast_eq_ker_reduction m, RingHom.mem_ker]
  rw [map_sub, map_nsmul, map_one]
  change r - n • (1 : ZMod m) = 0
  rw [nsmul_eq_mul, mul_one]
  have hn : ((n : ℕ) : ZMod m) = r := by
    change ((r.val + m : ℕ) : ZMod m) = r
    rw [Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_self, add_zero]
  rw [hn, sub_self]

namespace DegreeData

/-- **`I_L` viewed inside `G_K`** — the subgroup of `L̃`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/FrobeniusLift.lean:50`). -/
def extensionInertiaWithin (D : DegreeData G) (K L : ClosedSubgroup G)
    (_hLK : L.toSubgroup ≤ K.toSubgroup) : Subgroup K.toSubgroup :=
  L.toSubgroup.subgroupOf K.toSubgroup ⊓ D.fieldInertiaWithin K

/-- The relative inertia is normal whenever the extension subgroup is. -/
instance extensionInertiaWithin_normal (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    (D.extensionInertiaWithin K L hLK).Normal := by
  rw [extensionInertiaWithin]
  infer_instance

private theorem extensionInertiaWithin_le_normalizedDegree_ker
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup) :
    D.extensionInertiaWithin K.field L hLK ≤
      (D.normalizedDegree K).toMonoidHom.ker := by
  intro x hx
  rw [D.normalizedDegree_ker K]
  exact hx.2

/-- **The factorized normalized degree** `d_K : G(L̃|K) → ℤ̂`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/FrobeniusLift.lean:75`). -/
def extensionNormalizedDegree (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    (K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK) →*
      ProfiniteIntegerMul :=
  QuotientGroup.lift (D.extensionInertiaWithin K.field L hLK)
    (D.normalizedDegree K).toMonoidHom
    (D.extensionInertiaWithin_le_normalizedDegree_ker K L hLK)

/-- The factorized degree computes on representatives. -/
@[simp]
theorem extensionNormalizedDegree_mk (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (k : K.field.toSubgroup) :
    D.extensionNormalizedDegree K L hLK (QuotientGroup.mk k) =
      D.normalizedDegree K k :=
  rfl

/-- **Restriction** `G(L̃|K) → G(L|K)` (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/FrobeniusLift.lean:99`). -/
def extensionRestriction (D : DegreeData G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal] :
    (K.toSubgroup ⧸ D.extensionInertiaWithin K L hLK) →*
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
  QuotientGroup.map (D.extensionInertiaWithin K L hLK)
    (L.toSubgroup.subgroupOf K.toSubgroup) (MonoidHom.id K.toSubgroup)
    inf_le_left

/-- Restriction computes on representatives. -/
@[simp]
theorem extensionRestriction_mk (D : DegreeData G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (k : K.toSubgroup) :
    D.extensionRestriction K L hLK (QuotientGroup.mk k) =
      QuotientGroup.mk k :=
  rfl

/-- **The Frobenius semigroup** `Frob(L̃|K)`: the classes of strictly positive
integral normalized degree (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/FrobeniusLift.lean:122`). -/
def FrobeniusElements (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] : Type u :=
  {σ : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK //
    ∃ n : ℕ, 0 < n ∧
      D.extensionNormalizedDegree K L hLK σ =
        (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^ n}

/-- The restriction of the Frobenius semigroup to `G(L|K)`. -/
def frobeniusRestriction (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal] :
    D.FrobeniusElements K L hLK →
      (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup) :=
  fun σ => D.extensionRestriction K.field L hLK σ.1

private def normalizedExtensionImageAdd (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (_hLK : L.toSubgroup ≤ K.field.toSubgroup) :
    AddSubgroup ProfiniteInteger :=
  Subgroup.toAddSubgroup'
    ((L.toSubgroup.subgroupOf K.field.toSubgroup).map
      (D.normalizedDegree K).toMonoidHom)

private theorem normalizedExtensionImageAdd_index_ne_zero
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    (D.normalizedExtensionImageAdd K L hLK).index ≠ 0 := by
  let E := L.toSubgroup.subgroupOf K.field.toSubgroup
  let dK := (D.normalizedDegree K).toMonoidHom
  let H := E.map dK
  have hE : E ≤ H.comap dK := Subgroup.le_comap_map dK E
  have hdvd : (H.comap dK).index ∣ E.index :=
    Subgroup.index_dvd_of_le hE
  have hcomap : (H.comap dK).index = H.index :=
    Subgroup.index_comap_of_surjective H (D.normalizedDegree_surjective K)
  have hHdvd : H.index ∣ E.index := hcomap ▸ hdvd
  have hE0 : E.index ≠ 0 := E.index_ne_zero_of_finite
  have hH0 : H.index ≠ 0 := by
    intro hzero
    rw [hzero] at hHdvd
    exact hE0 (zero_dvd_iff.mp hHdvd)
  exact hH0

/-- **The Frobenius semigroup restricts onto the finite Galois group**: correct
a preimage by an extension element whose degree shifts the class to a positive
multiple of one (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/FrobeniusLift.lean:171`). -/
theorem frobeniusRestriction_surjective (D : DegreeData G)
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    [hLfinite :
      Finite (K.field.toSubgroup ⧸ L.toSubgroup.subgroupOf K.field.toSubgroup)] :
    Function.Surjective (D.frobeniusRestriction K L hLK) := by
  intro σ
  refine Quotient.inductionOn' σ ?_
  intro s
  let H := D.normalizedExtensionImageAdd K L hLK
  have hH0 : H.index ≠ 0 :=
    D.normalizedExtensionImageAdd_index_ne_zero K L hLK
  obtain ⟨n, hn, hmem⟩ :=
    exists_positive_nsmul_one_sub_mem_of_index_ne_zero H hH0
      (D.normalizedDegree K s).toAdd
  have hneg : n • (1 : ProfiniteInteger) - (D.normalizedDegree K s).toAdd ∈ H := by
    simpa [sub_eq_add_neg, add_comm] using H.neg_mem hmem
  change Multiplicative.ofAdd
      (n • (1 : ProfiniteInteger) - (D.normalizedDegree K s).toAdd) ∈
    (L.toSubgroup.subgroupOf K.field.toSubgroup).map
      (D.normalizedDegree K).toMonoidHom at hneg
  obtain ⟨l, hlE, hdl⟩ := hneg
  let t : K.field.toSubgroup := s * l
  let q : K.field.toSubgroup ⧸ D.extensionInertiaWithin K.field L hLK :=
    QuotientGroup.mk t
  have hdq : D.extensionNormalizedDegree K L hLK q =
      (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^ n := by
    apply Multiplicative.ext
    change (D.normalizedDegree K (s * l)).toAdd =
      n • (1 : ProfiniteInteger)
    rw [map_mul]
    change (D.normalizedDegree K s).toAdd +
        (D.normalizedDegree K l).toAdd = n • (1 : ProfiniteInteger)
    have hdl' := congrArg Multiplicative.toAdd hdl
    change (D.normalizedDegree K l).toAdd =
      n • (1 : ProfiniteInteger) - (D.normalizedDegree K s).toAdd at hdl'
    rw [hdl']
    abel
  let qF : D.FrobeniusElements K L hLK := ⟨q, n, hn, hdq⟩
  refine ⟨qF, ?_⟩
  change QuotientGroup.mk (s * l) = QuotientGroup.mk s
  apply QuotientGroup.eq.mpr
  change (s * l)⁻¹ * s ∈ L.toSubgroup.subgroupOf K.field.toSubgroup
  simpa [mul_inv_rev, mul_assoc] using
    (L.toSubgroup.subgroupOf K.field.toSubgroup).inv_mem hlE

end DegreeData

end

end Atlas.Knowledge
