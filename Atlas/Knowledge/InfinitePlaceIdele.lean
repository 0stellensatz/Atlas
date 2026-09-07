import Mathlib
import Atlas.Knowledge.IdeleClassGroup
import Atlas.Knowledge.IdeleGroup
import Atlas.Knowledge.PrincipalIdele

/-!
# infinite-place idele

The one-place inclusion into the idele group at an archimedean place: a unit of one infinite
completion, placed at its own coordinate with `1` at every other infinite place and `1` in
the finite block — the archimedean case of Milne's `(1, …, 1, a, 1, …)`, beside the finite
case `Atlas.Knowledge.FinitePlaceIdele`. It is how a real place's positivity condition is cut
away one place at a time: `Atlas.Knowledge.RealPlaceClassSubgroup` reads the piece of the
idele class group a real place contributes through this map. Everything here is proved;
nothing is recorded.

## Main definitions

* `infiniteAdeleUnitsPi` — the units of the infinite adele ring, placewise.
* `infinitePlaceIdele` — `(v.Completion)ˣ →* 𝕀_K`.
* `infinitePlaceIdeleClass` — the same, followed by the class-group projection.

## Main statements

* `infinitePlaceIdele_snd`, `infinitePlaceIdele_apply_self`, `infinitePlaceIdele_apply_of_ne`
  — the components: `1` in the finite block, the prescribed unit at `v`, `1` at every other
  infinite place.

## Implementation notes

The archimedean block of the idele group is `(InfiniteAdeleRing K)ˣ`, and
`InfiniteAdeleRing K` is a definition over the product of the completions that does not unify
with it unaided, so Mathlib's `MulEquiv.piUnits` is read at that type once, as
`infiniteAdeleUnitsPi`, with its two coordinate lemmas, both `rfl`; the single idele is then
`Pi.mulSingle` carried through it, where the source builds a dependent value and transports
it along the continuous `piUnits` (`AlgebraicNumberTheory/Idele/SinglePlace.lean:54`).
Equality of infinite places is decided classically, on the one definition and the two
component proofs that ask for it.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open scoped NumberField
open NumberField

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

variable {K}

open scoped Classical in
/-- The **infinite-place idele**: the idele whose `v`-component is prescribed and whose other
components are `1` — the archimedean case of Milne's `(1, …, 1, a, 1, …)`
([Milne 2020, Chap. V, §4, 4.3, p.171][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:54`). -/
def infinitePlaceIdele (v : InfinitePlace K) : (v.Completion)ˣ →* IdeleGroup K where
  toFun u := ((infiniteAdeleUnitsPi K).symm (Pi.mulSingle v u), 1)
  map_one' := Prod.ext (by rw [Pi.mulSingle_one, map_one]; rfl) rfl
  map_mul' u u' := Prod.ext (by rw [Pi.mulSingle_mul, map_mul]; rfl) (one_mul _).symm

/-- The infinite-place idele has finite block `1`
([Milne 2020, Chap. V, §4, 4.3, p.171][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:162`). -/
theorem infinitePlaceIdele_snd (v : InfinitePlace K) (u : (v.Completion)ˣ) :
    (infinitePlaceIdele v u).2 = 1 :=
  rfl

open scoped Classical in
/-- At its own place the infinite-place idele is the prescribed unit
([Milne 2020, Chap. V, §4, 4.3, p.171][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:131`). -/
theorem infinitePlaceIdele_apply_self (v : InfinitePlace K) (u : (v.Completion)ˣ) :
    ((infinitePlaceIdele v u).1 : InfiniteAdeleRing K) v = (u : v.Completion) := by
  change (((infiniteAdeleUnitsPi K).symm (Pi.mulSingle v u) : (InfiniteAdeleRing K)ˣ) :
    InfiniteAdeleRing K) v = _
  rw [infiniteAdeleUnitsPi_symm_apply_coe, Pi.mulSingle_eq_same]

open scoped Classical in
/-- At every other infinite place the infinite-place idele is `1`
([Milne 2020, Chap. V, §4, 4.3, p.171][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:146`). -/
theorem infinitePlaceIdele_apply_of_ne (v w : InfinitePlace K) (u : (v.Completion)ˣ)
    (h : w ≠ v) : ((infinitePlaceIdele v u).1 : InfiniteAdeleRing K) w = 1 := by
  change (((infiniteAdeleUnitsPi K).symm (Pi.mulSingle v u) : (InfiniteAdeleRing K)ˣ) :
    InfiniteAdeleRing K) w = _
  rw [infiniteAdeleUnitsPi_symm_apply_coe, Pi.mulSingle_eq_of_ne h, Units.val_one]

/-- The **infinite-place idele class**: one archimedean unit, made global, made a class
([Milne 2020, Chap. V, §4, 4.3, p.171][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:172`). -/
def infinitePlaceIdeleClass (v : InfinitePlace K) : (v.Completion)ˣ →* IdeleClassGroup K :=
  (QuotientGroup.mk' (principalIdeleSubgroup K)).comp (infinitePlaceIdele v)

end Atlas.Knowledge

end
