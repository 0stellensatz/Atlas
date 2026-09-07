import Mathlib
import Atlas.Knowledge.IdeleClassGroup
import Atlas.Knowledge.IdeleGroup
import Atlas.Knowledge.Modulus
import Atlas.Knowledge.PrincipalIdele
import Atlas.Knowledge.RayClassGroup

/-!
# real place class subgroup

The image in the idele class group of the full unit group of one real completion, carried in
at that place alone: the idele that is `u` at the real place `w` and `1` everywhere else,
mapped down to `C_K`. It is the piece the positivity condition at `w` cuts, and two facts
about it drive the infinite part of the conductor: at a real place a modulus does not select,
the piece lies in the congruence subgroup outright, and a modulus whose congruence subgroup
lies in `H` may drop a real place whose piece already lies in `H` — the one-place step that
erases from a defining modulus every real place the conductor does not need.

## Main definitions

* `infiniteAdeleUnitsPi` — units of the infinite adele ring, placewise.
* `realIdeleSingle` — the idele concentrated at a real place.
* `realPlaceClassSubgroup` — the image of `K_wˣ` in `C_K`.

## Main statements

* `realPlaceClassSubgroup_le_congruenceSubgroup` — at an unselected real place the piece lies
  in the congruence subgroup.
* `congruenceSubgroup_erase_le`, `congruenceSubgroup_sdiff_le` — erasing one, then finitely
  many, real places keeps `congruenceSubgroup ≤ H` once their pieces are in `H`.

## Implementation notes

The placewise unit equivalence is Mathlib's `MulEquiv.piUnits` read at
`(InfiniteAdeleRing K)ˣ`, which is a definition over the product and does not unify with it
unaided — hence a named copy with its two coordinate lemmas; the source uses the continuous
version (`AlgebraicNumberTheory/Idele/SinglePlace.lean:54`). The erasing steps are stated on
`congruenceSubgroup K m ≤ H` rather than on the `IsDefiningModulus` of
`Atlas.Knowledge.IsConductor`, which unfolds to it, so that the conductor item can import
this one; the erased modulus is written out as `⟨m.finitePart, m.infinitePart.erase w⟩`
rather than named, with equality of places decided classically, declaration by declaration,
as `Finset.erase` and the single idele both ask. The source states the one-place step as an
equivalence (`GlobalClassFieldTheory/GlobalClassFields/ConductorInfinitePart.lean:163`),
whose converse is order reversal of the congruence subgroup; only the direction the conductor
needs is stated. The proof splits an idele congruent for the erased modulus as the single
idele of its `w`-component times an idele congruent for the original one, as on the finite
side.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
/-- The units of the infinite adele ring, placewise: `MulEquiv.piUnits` read at the
archimedean block of the idele group ([Milne 2020, Chap. V, §4, pp.169–170][MilneCFT];
Yamaguchi 2026, `AlgebraicNumberTheory/Idele/SinglePlace.lean:54`). -/
def infiniteAdeleUnitsPi : (InfiniteAdeleRing K)ˣ ≃* Π v : InfinitePlace K, (v.Completion)ˣ :=
  MulEquiv.piUnits

omit [NumberField K] in
/-- The coordinate of a placewise-assembled unit
([Milne 2020, Chap. V, §4, pp.169–170][MilneCFT]). -/
theorem infiniteAdeleUnitsPi_symm_apply_coe (f : Π v : InfinitePlace K, (v.Completion)ˣ)
    (v : InfinitePlace K) :
    (((infiniteAdeleUnitsPi K).symm f : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v =
      (f v : v.Completion) :=
  rfl

omit [NumberField K] in
/-- The placewise reading of a unit's coordinate
([Milne 2020, Chap. V, §4, pp.169–170][MilneCFT]). -/
theorem infiniteAdeleUnitsPi_apply_coe (x : (InfiniteAdeleRing K)ˣ) (v : InfinitePlace K) :
    ((infiniteAdeleUnitsPi K x v : (v.Completion)ˣ) : v.Completion) =
      (x : InfiniteAdeleRing K) v :=
  rfl

open scoped Classical in
/-- The idele **concentrated at a real place** `w`: `u` there, `1` at every other place
([Milne 2020, Chap. V, §4, p.172][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:54`). -/
def realIdeleSingle (w : RealPlace K) : (w.1.Completion)ˣ →* IdeleGroup K where
  toFun u := ((infiniteAdeleUnitsPi K).symm (Pi.mulSingle w.1 u), 1)
  map_one' := Prod.ext (by rw [Pi.mulSingle_one, map_one]; rfl) rfl
  map_mul' u u' := Prod.ext (by rw [Pi.mulSingle_mul, map_mul]; rfl) (one_mul _).symm

/-- The **real place class subgroup**: the image of `K_wˣ` in `C_K` through the single idele
at `w` ([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:172`). -/
def realPlaceClassSubgroup (w : RealPlace K) : Subgroup (IdeleClassGroup K) :=
  ((QuotientGroup.mk' (principalIdeleSubgroup K)).comp (realIdeleSingle K w)).range

open scoped Classical in
/-- At a real place other than its own, the single idele is `1`, hence positive
([Milne 2020, Chap. V, §4, p.172][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:146`). -/
theorem realIdeleSingle_mem_realPositiveSubgroup_of_ne (w v : RealPlace K) (hvw : v ≠ w)
    (u : (w.1.Completion)ˣ) : (realIdeleSingle K w u).1 ∈ realPositiveSubgroup K v := by
  rw [mem_realPositiveSubgroup_iff]
  have hvw' : v.1 ≠ w.1 := fun h => hvw (Subtype.ext h)
  change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2
    ((((infiniteAdeleUnitsPi K).symm (Pi.mulSingle w.1 u) : (InfiniteAdeleRing K)ˣ) :
      InfiniteAdeleRing K) v.1)
  rw [infiniteAdeleUnitsPi_symm_apply_coe, Pi.mulSingle_eq_of_ne hvw', Units.val_one, map_one]
  exact zero_lt_one

/-- At a real place the modulus does not select, the piece lies in the congruence subgroup:
the single idele is `1` at every place the modulus constrains
([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/ConductorInfinitePart.lean:31`). -/
theorem realPlaceClassSubgroup_le_congruenceSubgroup (m : Modulus K) (w : RealPlace K)
    (hw : w ∉ m.infinitePart) : realPlaceClassSubgroup K w ≤ congruenceSubgroup K m := by
  rw [congruenceSubgroup_eq_map]
  rintro _ ⟨u, rfl⟩
  refine ⟨realIdeleSingle K w u, (mem_ideleCongruenceSubgroup_iff K m _).2
    ⟨fun v hv => ?_, fun v => ?_⟩, rfl⟩
  · exact realIdeleSingle_mem_realPositiveSubgroup_of_ne K w v (fun h => hw (h ▸ hv)) u
  · exact Subgroup.one_mem _

open scoped Classical in
/-- **Erasing one real place** from a modulus whose congruence subgroup lies in `H` keeps it
there once the piece at that place lies in `H`: an idele congruent for the erased modulus is
its `w`-component's single idele times an idele congruent for the original one
([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/ConductorInfinitePart.lean:163`). -/
theorem congruenceSubgroup_erase_le {H : Subgroup (IdeleClassGroup K)} {m : Modulus K}
    (hm : congruenceSubgroup K m ≤ H) (w : RealPlace K) (hw : realPlaceClassSubgroup K w ≤ H) :
    congruenceSubgroup K ⟨m.finitePart, m.infinitePart.erase w⟩ ≤ H := by
  rw [congruenceSubgroup_eq_map] at hm ⊢
  rintro _ ⟨y, hy, rfl⟩
  have hy := (mem_ideleCongruenceSubgroup_iff K _ y).1 hy
  -- split off the `w`-component
  set uw : (w.1.Completion)ˣ := infiniteAdeleUnitsPi K y.1 w.1 with huw
  set s : (InfiniteAdeleRing K)ˣ := (infiniteAdeleUnitsPi K).symm (Pi.mulSingle w.1 uw) with hs
  set y' : IdeleGroup K := (y.1 * s⁻¹, y.2) with hy'
  have hsplit : y = y' * realIdeleSingle K w uw := by
    ext1
    · change y.1 = y.1 * s⁻¹ * s
      rw [inv_mul_cancel_right]
    · exact (mul_one _).symm
  have hcomp : ∀ v : InfinitePlace K,
      ((y.1 * s⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v =
        (y.1 : InfiniteAdeleRing K) v *
          (((Pi.mulSingle w.1 uw : Π v : InfinitePlace K, (v.Completion)ˣ)⁻¹ v :
            (v.Completion)ˣ) : v.Completion) := by
    intro v
    change (y.1 : InfiniteAdeleRing K) v *
      ((s⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v = _
    rw [hs, ← map_inv, infiniteAdeleUnitsPi_symm_apply_coe]
  have hy'mem : y' ∈ ideleCongruenceSubgroup K m := by
    refine (mem_ideleCongruenceSubgroup_iff K m y').2 ⟨fun v hv => ?_, fun v => hy.2 v⟩
    rw [mem_realPositiveSubgroup_iff]
    change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2
      (((y.1 * s⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v.1)
    by_cases hvw : v = w
    · subst hvw
      rw [hcomp, Pi.inv_apply, Pi.mulSingle_eq_same, huw, ← infiniteAdeleUnitsPi_apply_coe,
        Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _), map_one]
      exact zero_lt_one
    · have h := hy.1 v (Finset.mem_erase.mpr ⟨hvw, hv⟩)
      rw [mem_realPositiveSubgroup_iff] at h
      have hvw' : v.1 ≠ w.1 := fun h' => hvw (Subtype.ext h')
      rw [hcomp, Pi.inv_apply, Pi.mulSingle_eq_of_ne hvw', inv_one, Units.val_one, mul_one]
      exact h
  have hwmem : (QuotientGroup.mk' (principalIdeleSubgroup K)) (realIdeleSingle K w uw) ∈ H :=
    hw ⟨uw, rfl⟩
  rw [hsplit, map_mul]
  exact H.mul_mem (hm ⟨y', hy'mem, rfl⟩) hwmem

open scoped Classical in
/-- **Erasing finitely many real places** whose pieces lie in `H` keeps the congruence
subgroup in `H`, by erasing them one at a time
([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/ConductorInfinitePart.lean:185`). -/
theorem congruenceSubgroup_sdiff_le {H : Subgroup (IdeleClassGroup K)} {m : Modulus K}
    (hm : congruenceSubgroup K m ≤ H) (s : Finset (RealPlace K))
    (hs : ∀ w ∈ s, realPlaceClassSubgroup K w ≤ H) :
    congruenceSubgroup K ⟨m.finitePart, m.infinitePart \ s⟩ ≤ H := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sdiff_empty]
    exact hm
  | insert w s hw ih =>
    rw [Finset.sdiff_insert]
    exact congruenceSubgroup_erase_le K (ih fun x hx => hs x (Finset.mem_insert_of_mem hx)) w
      (hs w (Finset.mem_insert_self w s))

end Atlas.Knowledge

end
