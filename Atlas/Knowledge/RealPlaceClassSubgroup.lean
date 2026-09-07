import Mathlib
import Atlas.Knowledge.IdeleClassGroup
import Atlas.Knowledge.IdeleGroup
import Atlas.Knowledge.InfinitePlaceIdele
import Atlas.Knowledge.Modulus
import Atlas.Knowledge.PrincipalIdele
import Atlas.Knowledge.RayClassGroup

/-!
# real place class subgroup

The image in the idele class group of the full unit group of one real completion, carried in
at that place alone by the infinite-place idele of `Atlas.Knowledge.InfinitePlaceIdele`. It
is the piece the positivity condition at `w` cuts, and two facts about it drive the infinite
part of the conductor: at a real place a modulus does not select, the piece lies in the
congruence subgroup outright, and a modulus whose congruence subgroup lies in `H` may drop a
real place whose piece already lies in `H` — the one-place step that erases from a defining
modulus every real place the conductor does not need.

## Main definitions

* `realPlaceClassSubgroup` — the image of `K_wˣ` in `C_K`.

## Main statements

* `infinitePlaceIdele_mem_realPositiveSubgroup_of_ne` — the single idele is positive at every
  other real place.
* `realPlaceClassSubgroup_le_congruenceSubgroup` — at an unselected real place the piece lies
  in the congruence subgroup.
* `congruenceSubgroup_erase_le`, `congruenceSubgroup_sdiff_le` — erasing one, then finitely
  many, real places keeps `congruenceSubgroup ≤ H` once their pieces are in `H`.

## Implementation notes

The erasing steps are stated on `congruenceSubgroup K m ≤ H` rather than on the
`IsDefiningModulus` of `Atlas.Knowledge.IsConductor`, which unfolds to it, so that the
conductor item can import this one; the erased modulus is written out as
`⟨m.finitePart, m.infinitePart.erase w⟩` rather than named. Because `Finset.erase` and `\`
carry their decidability instance in the statement, the erasing steps take
`DecidableEq (RealPlace K)` as a binder — a consumer supplies its own, classical or not — and
the proofs go classical only internally. The source states the one-place step as an
equivalence (`GlobalClassFieldTheory/GlobalClassFields/ConductorInfinitePart.lean:163`),
whose converse is order reversal of the congruence subgroup; only the direction the conductor
needs is stated. Its proof splits an idele congruent for the erased modulus as the
infinite-place idele of its `w`-component times an idele congruent for the original one, as
on the finite side, reading the components through the lemmas of
`Atlas.Knowledge.InfinitePlaceIdele`.

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

/-- The **real place class subgroup**: the image of `K_wˣ` in `C_K` through the
infinite-place idele at `w` ([Milne 2020, Chap. V, §4, p.172][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:172`). -/
def realPlaceClassSubgroup (w : RealPlace K) : Subgroup (IdeleClassGroup K) :=
  (infinitePlaceIdeleClass w.1).range

/-- At a real place other than its own, the infinite-place idele is `1`, hence positive
([Milne 2020, Chap. V, §4, p.172][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:146`). -/
theorem infinitePlaceIdele_mem_realPositiveSubgroup_of_ne (w v : RealPlace K) (hvw : v ≠ w)
    (u : (w.1.Completion)ˣ) : (infinitePlaceIdele w.1 u).1 ∈ realPositiveSubgroup K v := by
  rw [mem_realPositiveSubgroup_iff,
    infinitePlaceIdele_apply_of_ne w.1 v.1 u (fun h => hvw (Subtype.ext h)), map_one]
  exact zero_lt_one

/-- At a real place the modulus does not select, the piece lies in the congruence subgroup:
the infinite-place idele is `1` at every place the modulus constrains
([Milne 2020, Chap. V, §4, p.172][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/ConductorInfinitePart.lean:31`). -/
theorem realPlaceClassSubgroup_le_congruenceSubgroup (m : Modulus K) (w : RealPlace K)
    (hw : w ∉ m.infinitePart) : realPlaceClassSubgroup K w ≤ congruenceSubgroup K m := by
  rw [congruenceSubgroup_eq_map]
  rintro _ ⟨u, rfl⟩
  refine ⟨infinitePlaceIdele w.1 u, (mem_ideleCongruenceSubgroup_iff K m _).2
    ⟨fun v hv => ?_, fun v => ?_⟩, rfl⟩
  · exact infinitePlaceIdele_mem_realPositiveSubgroup_of_ne K w v (fun h => hw (h ▸ hv)) u
  · exact Subgroup.one_mem _

/-- **Erasing one real place** from a modulus whose congruence subgroup lies in `H` keeps it
there once the piece at that place lies in `H`: an idele congruent for the erased modulus is
the infinite-place idele of its `w`-component times an idele congruent for the original one
([Milne 2020, Chap. V, §4, p.172][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/ConductorInfinitePart.lean:163`). -/
theorem congruenceSubgroup_erase_le [DecidableEq (RealPlace K)] {H : Subgroup (IdeleClassGroup K)}
    {m : Modulus K} (hm : congruenceSubgroup K m ≤ H) (w : RealPlace K)
    (hw : realPlaceClassSubgroup K w ≤ H) :
    congruenceSubgroup K ⟨m.finitePart, m.infinitePart.erase w⟩ ≤ H := by
  classical
  rw [congruenceSubgroup_eq_map] at hm ⊢
  rintro _ ⟨y, hy, rfl⟩
  have hy := (mem_ideleCongruenceSubgroup_iff K _ y).1 hy
  -- split off the `w`-component
  set uw : (w.1.Completion)ˣ := infiniteAdeleUnitsPi K y.1 w.1 with huw
  set s : (InfiniteAdeleRing K)ˣ := (infinitePlaceIdele w.1 uw).1 with hs
  set y' : IdeleGroup K := (y.1 * s⁻¹, y.2) with hy'
  have hsplit : y = y' * infinitePlaceIdele w.1 uw := by
    ext1
    · change y.1 = y.1 * s⁻¹ * s
      rw [inv_mul_cancel_right]
    · change y.2 = y.2 * (infinitePlaceIdele w.1 uw).2
      rw [infinitePlaceIdele_snd, mul_one]
  have hsinv : s⁻¹ = (infinitePlaceIdele w.1 uw⁻¹).1 := by
    rw [hs, ← Prod.fst_inv, ← map_inv]
  have hy'mem : y' ∈ ideleCongruenceSubgroup K m := by
    refine (mem_ideleCongruenceSubgroup_iff K m y').2 ⟨fun v hv => ?_, fun v => hy.2 v⟩
    rw [mem_realPositiveSubgroup_iff]
    change 0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2
      ((y.1 : InfiniteAdeleRing K) v.1 * ((s⁻¹ : (InfiniteAdeleRing K)ˣ) : InfiniteAdeleRing K) v.1)
    rw [hsinv]
    by_cases hvw : v = w
    · subst hvw
      rw [infinitePlaceIdele_apply_self, huw, ← infiniteAdeleUnitsPi_apply_coe,
        Units.val_inv_eq_inv_val, mul_inv_cancel₀ (Units.ne_zero _), map_one]
      exact zero_lt_one
    · have h := hy.1 v (Finset.mem_erase.mpr ⟨hvw, hv⟩)
      rw [mem_realPositiveSubgroup_iff] at h
      rw [infinitePlaceIdele_apply_of_ne w.1 v.1 _ (fun h' => hvw (Subtype.ext h')), mul_one]
      exact h
  have hwmem : (QuotientGroup.mk' (principalIdeleSubgroup K)) (infinitePlaceIdele w.1 uw) ∈ H :=
    hw ⟨uw, rfl⟩
  rw [hsplit, map_mul]
  exact H.mul_mem (hm ⟨y', hy'mem, rfl⟩) hwmem

/-- **Erasing finitely many real places** whose pieces lie in `H` keeps the congruence
subgroup in `H`, by erasing them one at a time ([Milne 2020, Chap. V, §4, p.172][MilneCFT];
Yamaguchi 2026, `GlobalClassFieldTheory/GlobalClassFields/ConductorInfinitePart.lean:185`). -/
theorem congruenceSubgroup_sdiff_le [DecidableEq (RealPlace K)] {H : Subgroup (IdeleClassGroup K)}
    {m : Modulus K} (hm : congruenceSubgroup K m ≤ H) (s : Finset (RealPlace K))
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
