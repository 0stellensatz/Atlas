import Mathlib
import Atlas.Knowledge.FinitePlaceIdele
import Atlas.Knowledge.IdeleClassGroup
import Atlas.Knowledge.IdeleGroup
import Atlas.Knowledge.Modulus
import Atlas.Knowledge.PrincipalIdele
import Atlas.Knowledge.RayClassGroup

/-!
# local higher unit class subgroup

The image in the idele class group of one local higher unit group `U_v^(n)`, carried in at
the finite place `v` alone by the finite-place idele of `Atlas.Knowledge.FinitePlaceIdele`.
It is the local piece of a congruence subgroup, and two facts about it drive the finite part
of the conductor: at the modulus's own exponent it sits inside the congruence subgroup, and a
modulus whose congruence subgroup lies in `H` may have its exponent at `v` replaced by any
`n` whose piece already lies in `H` — the one-place step that lowers a defining modulus's
exponents to the least ones.

## Main definitions

* `localHigherUnitClassSubgroup` — the image of `U_v^(n)` in `C_K`.

## Main statements

* `localHigherUnitClassSubgroup_le_congruenceSubgroup` — at the modulus's exponent the piece
  lies in the congruence subgroup.
* `congruenceSubgroup_update_le` — replacing one exponent keeps `congruenceSubgroup ≤ H` once
  the piece at the new exponent is in `H`.

## Implementation notes

The class-level map is `Atlas.Knowledge.finitePlaceIdeleClass`, as the source writes it
(`AlgebraicNumberTheory/RayClass/LocalConductor.lean:24`), and every component computation
goes through the component lemmas of `Atlas.Knowledge.FinitePlaceIdele`. The replacement step
is stated on `congruenceSubgroup K m ≤ H` rather than on the `IsDefiningModulus` of
`Atlas.Knowledge.IsConductor`, which unfolds to it, so that the conductor item can import
this one; the modulus with one exponent replaced is written out as
`⟨m.finitePart.update v n, m.infinitePart⟩` rather than named, and its proof decides equality
of finite places classically, as the update's evaluation lemmas ask. That proof splits an
idele of the replaced modulus's congruence subgroup as the finite-place idele of its
`v`-component times a remainder that lies in the original congruence subgroup, following the
source (`GlobalClassFieldTheory/GlobalClassFields/ConductorLocalComparison.lean:90`).

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

/-- The **local higher unit class subgroup**: the image of `U_v^(n)` in `C_K` through the
finite-place idele at `v` ([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi
2026, `AlgebraicNumberTheory/RayClass/LocalConductor.lean:24`). -/
def localHigherUnitClassSubgroup (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (IdeleClassGroup K) :=
  (localHigherUnitGroup K v n).map (finitePlaceIdeleClass v)

/-- At the modulus's own exponent the local piece lies in the congruence subgroup: the
finite-place idele of a unit congruent to `1` to that depth is trivially positive at the real
places and congruent at every finite one ([Milne 2020, Chap. V, §4, p.172][MilneCFT];
Yamaguchi 2026, `AlgebraicNumberTheory/RayClass/LocalConductor.lean:32`). -/
theorem localHigherUnitClassSubgroup_le_congruenceSubgroup (m : Modulus K)
    (v : HeightOneSpectrum (𝓞 K)) :
    localHigherUnitClassSubgroup K v (m.finitePart v) ≤ congruenceSubgroup K m := by
  rw [congruenceSubgroup_eq_map]
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨finitePlaceIdele v u,
    (mem_ideleCongruenceSubgroup_iff K m _).2 ⟨fun w _ => ?_, fun w => ?_⟩, rfl⟩
  · rw [finitePlaceIdele_fst]
    exact Subgroup.one_mem _
  · by_cases hwv : w = v
    · subst hwv
      rw [finitePlaceIdele_apply_self]
      exact hu
    · rw [finitePlaceIdele_apply_of_ne v w u hwv]
      exact Subgroup.one_mem _

open scoped Classical in
/-- **Replacing one exponent** of a modulus whose congruence subgroup lies in `H` keeps it
there once the local piece at the new exponent lies in `H`: an idele congruent for the
replaced modulus is the finite-place idele of its `v`-component times an idele congruent for
the original one ([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/ConductorLocalComparison.lean:90`). -/
theorem congruenceSubgroup_update_le {H : Subgroup (IdeleClassGroup K)} {m : Modulus K}
    (hm : congruenceSubgroup K m ≤ H) (v : HeightOneSpectrum (𝓞 K)) {n : ℕ}
    (hn : localHigherUnitClassSubgroup K v n ≤ H) :
    congruenceSubgroup K ⟨m.finitePart.update v n, m.infinitePart⟩ ≤ H := by
  rw [congruenceSubgroup_eq_map] at hm ⊢
  rintro _ ⟨y, hy, rfl⟩
  have hy := (mem_ideleCongruenceSubgroup_iff K _ y).1 hy
  -- split off the `v`-component
  set yv : (v.adicCompletion K)ˣ := y.2 v with hyv
  set y' : IdeleGroup K := (y.1, y.2 * ((finitePlaceIdele v yv).2)⁻¹) with hy'
  have hsplit : y = y' * finitePlaceIdele v yv := by
    ext1
    · change y.1 = y.1 * (finitePlaceIdele v yv).1
      rw [finitePlaceIdele_fst, mul_one]
    · change y.2 = y.2 * ((finitePlaceIdele v yv).2)⁻¹ * (finitePlaceIdele v yv).2
      rw [inv_mul_cancel_right]
  have hy'mem : y' ∈ ideleCongruenceSubgroup K m := by
    refine (mem_ideleCongruenceSubgroup_iff K m y').2 ⟨fun w hw => hy.1 w hw, fun w => ?_⟩
    change (y.2 * ((finitePlaceIdele v yv).2)⁻¹) w ∈ _
    rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply]
    by_cases hwv : w = v
    · subst hwv
      rw [finitePlaceIdele_apply_self, hyv, mul_inv_cancel]
      exact Subgroup.one_mem _
    · rw [finitePlaceIdele_apply_of_ne v w yv hwv, inv_one, mul_one]
      have := hy.2 w
      simpa only [Finsupp.coe_update, Function.update_of_ne hwv] using this
  have hvmem : (QuotientGroup.mk' (principalIdeleSubgroup K)) (finitePlaceIdele v yv) ∈ H := by
    apply hn
    refine ⟨yv, ?_, rfl⟩
    have := hy.2 v
    simp only [Finsupp.coe_update, Function.update_self] at this
    exact this
  rw [hsplit, map_mul]
  exact H.mul_mem (hm ⟨y', hy'mem, rfl⟩) hvmem

end Atlas.Knowledge

end
