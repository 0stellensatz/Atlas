import Mathlib
import Atlas.Knowledge.IdeleClassGroup
import Atlas.Knowledge.IdeleGroup
import Atlas.Knowledge.Modulus
import Atlas.Knowledge.PrincipalIdele
import Atlas.Knowledge.RayClassGroup

/-!
# local higher unit class subgroup

The image in the idele class group of one local higher unit group `U_v^(n)`, carried in at
the finite place `v` alone: the idele that is `u` at `v` and `1` everywhere else, mapped down
to `C_K`. It is the local piece of a congruence subgroup, and two facts about it drive the
finite part of the conductor: at the modulus's own exponent it sits inside the congruence
subgroup, and a modulus whose congruence subgroup lies in `H` may have its exponent at `v`
replaced by any `n` whose piece already lies in `H` — the one-place step that lowers a
defining modulus's exponents to the least ones.

## Main definitions

* `finiteIdeleSingle` — the idele concentrated at a finite place.
* `localHigherUnitClassSubgroup` — the image of `U_v^(n)` in `C_K`.

## Main statements

* `localHigherUnitClassSubgroup_le_congruenceSubgroup` — at the modulus's exponent the piece
  lies in the congruence subgroup.
* `congruenceSubgroup_update_le` — replacing one exponent keeps `congruenceSubgroup ≤ H` once
  the piece at the new exponent is in `H`.

## Implementation notes

The single idele is Mathlib's `RestrictedProduct.mulSingle` in the finite slot with `1` in
the archimedean one, where the source builds its own dependent value
(`AlgebraicNumberTheory/Idele/SinglePlace.lean:204`). The replacement step is stated on
`congruenceSubgroup K m ≤ H` rather than on the `IsDefiningModulus` of
`Atlas.Knowledge.IsConductor`, which unfolds to it, so that the conductor item can import
this one; the modulus with one exponent replaced is written out as
`⟨m.finitePart.update v n, m.infinitePart⟩` rather than named, with equality of finite places
decided classically, declaration by declaration, as `Finsupp.update` and the single idele
both ask. Its proof splits an idele of the replaced modulus's congruence subgroup as the
single idele of its `v`-component times a remainder that lies in the original congruence
subgroup, following the source
(`GlobalClassFieldTheory/GlobalClassFields/ConductorLocalComparison.lean:90`).

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- The family of local integer-unit subgroups the finite ideles are restricted along, named
so that `RestrictedProduct.mulSingle` can be told which family it is inserting into
([Milne 2020, Chap. V, §4, pp.169–170][MilneCFT]). -/
abbrev integerUnitsFamily :
    (v : HeightOneSpectrum (𝓞 K)) → Subgroup (v.adicCompletion K)ˣ :=
  fun v => (v.adicCompletionIntegers K).units

open scoped Classical in
/-- The idele **concentrated at a finite place** `v`: `u` there, `1` at every other place
([Milne 2020, Chap. V, §4, p.172][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/Idele/SinglePlace.lean:204`). -/
def finiteIdeleSingle (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* IdeleGroup K where
  toFun u := (1, RestrictedProduct.mulSingle (integerUnitsFamily K) v u)
  map_one' := by
    ext1
    · rfl
    · exact RestrictedProduct.mulSingle_one (integerUnitsFamily K) v
  map_mul' u w := by
    ext1
    · exact (one_mul _).symm
    · exact RestrictedProduct.mulSingle_mul (integerUnitsFamily K) v u w

/-- The **local higher unit class subgroup**: the image of `U_v^(n)` in `C_K` through the
single idele at `v` ([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/RayClass/LocalConductor.lean:25`). -/
def localHigherUnitClassSubgroup (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (IdeleClassGroup K) :=
  (localHigherUnitGroup K v n).map
    ((QuotientGroup.mk' (principalIdeleSubgroup K)).comp (finiteIdeleSingle K v))

open scoped Classical in
/-- At the modulus's own exponent the local piece lies in the congruence subgroup: the single
idele of a unit congruent to `1` to that depth is trivially positive at the real places and
congruent at every finite one ([Milne 2020, Chap. V, §4, p.172][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/RayClass/LocalConductor.lean:34`). -/
theorem localHigherUnitClassSubgroup_le_congruenceSubgroup (m : Modulus K)
    (v : HeightOneSpectrum (𝓞 K)) :
    localHigherUnitClassSubgroup K v (m.finitePart v) ≤ congruenceSubgroup K m := by
  rw [congruenceSubgroup_eq_map]
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨finiteIdeleSingle K v u,
    (mem_ideleCongruenceSubgroup_iff K m _).2 ⟨fun w _ => ?_, fun w => ?_⟩, rfl⟩
  · change (1 : (InfiniteAdeleRing K)ˣ) ∈ realPositiveSubgroup K w
    exact Subgroup.one_mem _
  · by_cases hwv : w = v
    · subst hwv
      change RestrictedProduct.mulSingle (integerUnitsFamily K) w u w ∈ _
      rw [RestrictedProduct.mulSingle_eq_same]
      exact hu
    · change RestrictedProduct.mulSingle (integerUnitsFamily K) v u w ∈ _
      rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hwv]
      exact Subgroup.one_mem _

open scoped Classical in
/-- **Replacing one exponent** of a modulus whose congruence subgroup lies in `H` keeps it
there once the local piece at the new exponent lies in `H`: an idele congruent for the
replaced modulus is its `v`-component's single idele times an idele congruent for the
original one ([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi 2026,
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
  set y' : IdeleGroup K := (y.1, y.2 * (RestrictedProduct.mulSingle
    (integerUnitsFamily K) v yv)⁻¹) with hy'
  have hsplit : y = y' * finiteIdeleSingle K v yv := by
    ext1
    · exact (mul_one _).symm
    · change y.2 = y.2 * (RestrictedProduct.mulSingle (integerUnitsFamily K) v yv)⁻¹ *
        RestrictedProduct.mulSingle (integerUnitsFamily K) v yv
      rw [inv_mul_cancel_right]
  have hy'mem : y' ∈ ideleCongruenceSubgroup K m := by
    refine (mem_ideleCongruenceSubgroup_iff K m y').2 ⟨fun w hw => hy.1 w hw, fun w => ?_⟩
    by_cases hwv : w = v
    · subst hwv
      change (y.2 * (RestrictedProduct.mulSingle (integerUnitsFamily K) w yv)⁻¹ :
        Πʳ v : HeightOneSpectrum (𝓞 K),
          [(v.adicCompletion K)ˣ, integerUnitsFamily K v]) w ∈ _
      rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
        RestrictedProduct.mulSingle_eq_same, hyv, mul_inv_cancel]
      exact Subgroup.one_mem _
    · change (y.2 * (RestrictedProduct.mulSingle (integerUnitsFamily K) v yv)⁻¹ :
        Πʳ v : HeightOneSpectrum (𝓞 K),
          [(v.adicCompletion K)ˣ, integerUnitsFamily K v]) w ∈ _
      rw [RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
        RestrictedProduct.mulSingle_eq_of_ne _ _ hwv, inv_one, mul_one]
      have := hy.2 w
      simpa only [Finsupp.coe_update, Function.update_of_ne hwv] using this
  have hvmem : (QuotientGroup.mk' (principalIdeleSubgroup K)) (finiteIdeleSingle K v yv) ∈ H := by
    apply hn
    refine ⟨yv, ?_, rfl⟩
    have := hy.2 v
    simp only [Finsupp.coe_update, Function.update_self] at this
    exact this
  rw [hsplit, map_mul]
  exact H.mul_mem (hm ⟨y', hy'mem, rfl⟩) hvmem

end Atlas.Knowledge

end
