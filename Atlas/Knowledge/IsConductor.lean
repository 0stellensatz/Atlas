import Mathlib
import Atlas.Knowledge.IdeleClassGroup
import Atlas.Knowledge.LocalHigherUnitClassSubgroup
import Atlas.Knowledge.Modulus
import Atlas.Knowledge.RayClassGroup
import Atlas.Knowledge.RealPlaceClassSubgroup

/-!
# conductor

The conductor of a subgroup of the idele class group, as a characterization: a modulus is
*defining* for `H` when its congruence subgroup sits inside `H`, and the conductor is a
least defining modulus. Stating the conductor as a predicate rather than constructing it
keeps the item choice-free and junk-free — no `Nat.find` over an emptiness-dependent set,
no default value when `H` admits no defining modulus at all — and the statements of
`Atlas.Knowledge.RayClassField` consume the predicate as a slot. Existence of a conductor
for a subgroup that has any defining modulus is proved: a defining modulus is lowered to
the least exponent at each finite place of its support and stripped of every real place
whose piece already lies in `H`, one place at a time.

## Main definitions

* `IsDefiningModulus` — `congruenceSubgroup m ≤ H`.
* `IsConductor` — a defining modulus below every defining modulus.

## Main statements

* `exists_isConductor` — a subgroup with a defining modulus has a conductor; proved.

## Implementation notes

Uniqueness of the conductor is antisymmetry of the modulus order and deliberately not
restated. The source constructs its conductor pointwise by `Nat.find`
(`GlobalClassFieldTheory/GlobalClassFields/Conductor.lean:90`) on a subtype that carries
the defining-modulus existence (`Conductor.lean:34, :42, :119`,
`ConductorInfinitePart.lean:241`); the characterization here is that construction's
defining property, freed of the choice. The existence proof still finds the least exponent
by `Nat.find`, but only inside the proof and under the existence hypothesis, and never
names the conductor's finite part as a `Finsupp`: the descent lemma
`IsConductor.exists_finitePart_agrees` produces a defining modulus whose exponents are
least on a prescribed finite set, and the modulus it produces on the chosen modulus's
support is already the conductor's finite part, since off the support the chosen modulus
is `0`. Its infinite part is the chosen modulus's real places with those whose piece lies
in `H` removed, by `Atlas.Knowledge.RealPlaceClassSubgroup`. The one-place steps are the
two imported items; the source's finite descent is
`ConductorLocalComparison.lean:231, :282` and its real one
`ConductorInfinitePart.lean:247`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- A **defining modulus** for a subgroup of the idele class group: its congruence
subgroup is contained in `H` ([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT];
Yamaguchi 2026, `GlobalClassFieldTheory/GlobalClassFields/Conductor.lean:34`). -/
def IsDefiningModulus (H : Subgroup (IdeleClassGroup K)) (m : Modulus K) : Prop :=
  congruenceSubgroup K m ≤ H

/-- The **conductor**: a defining modulus dividing every defining modulus — the least
modulus through which `H`'s condition factors
([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/ConductorInfinitePart.lean:241`). -/
def IsConductor (H : Subgroup (IdeleClassGroup K)) (f : Modulus K) : Prop :=
  IsDefiningModulus K H f ∧ ∀ m, IsDefiningModulus K H m → f ≤ m

namespace IsConductor

open scoped Classical in
/-- **Finite descent**: a defining modulus whose exponent at each finite place of a
prescribed finite set is least among all defining moduli, and which agrees with the chosen
defining modulus off that set — by replacing one exponent at a time with the least one,
which `Atlas.Knowledge.LocalHigherUnitClassSubgroup` allows since the piece at the least
exponent lies in the congruence subgroup of a defining modulus attaining it
([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/ConductorLocalComparison.lean:231`). -/
theorem exists_finitePart_agrees {H : Subgroup (IdeleClassGroup K)}
    (h : ∃ m, IsDefiningModulus K H m) (s : Finset (HeightOneSpectrum (𝓞 K))) :
    ∃ m, IsDefiningModulus K H m ∧
      (∀ v ∈ s, ∀ m', IsDefiningModulus K H m' → m.finitePart v ≤ m'.finitePart v) ∧
        ∀ v ∉ s, m.finitePart v = h.choose.finitePart v := by
  induction s using Finset.induction_on with
  | empty => exact ⟨h.choose, h.choose_spec, by simp, fun _ _ => rfl⟩
  | insert v s hv ih =>
    obtain ⟨m, hm, hon, hoff⟩ := ih
    have hex : ∃ n : ℕ, ∃ m, IsDefiningModulus K H m ∧ m.finitePart v = n :=
      ⟨_, h.choose, h.choose_spec, rfl⟩
    obtain ⟨m₀, hm₀, hn⟩ := Nat.find_spec hex
    refine ⟨⟨m.finitePart.update v (Nat.find hex), m.infinitePart⟩,
      congruenceSubgroup_update_le K hm v ?_, ?_, ?_⟩
    · rw [← hn]
      exact (localHigherUnitClassSubgroup_le_congruenceSubgroup K m₀ v).trans hm₀
    · intro w hw m' hm'
      rcases Finset.mem_insert.mp hw with rfl | hws
      · simp only [Finsupp.coe_update, Function.update_self]
        exact Nat.find_min' hex ⟨m', hm', rfl⟩
      · have hwv : w ≠ v := fun h' => hv (h' ▸ hws)
        simp only [Finsupp.coe_update, Function.update_of_ne hwv]
        exact hon w hws m' hm'
    · intro w hw
      have hwv : w ≠ v := fun h' => hw (h' ▸ Finset.mem_insert_self v s)
      have hws : w ∉ s := fun h' => hw (Finset.mem_insert_of_mem h')
      simp only [Finsupp.coe_update, Function.update_of_ne hwv]
      exact hoff w hws

end IsConductor

open scoped Classical in
/-- A subgroup with any defining modulus has a conductor: descend on the chosen modulus's
support to a defining modulus with least exponents everywhere, then erase the real places
whose piece already lies in `H`; what is left is below every defining modulus,
exponentwise by leastness and placewise because a real place a defining modulus omits has
its piece in `H` ([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/Conductor.lean:119`,
`ConductorInfinitePart.lean:241`). -/
theorem exists_isConductor (H : Subgroup (IdeleClassGroup K))
    (h : ∃ m, IsDefiningModulus K H m) : ∃ f, IsConductor K H f := by
  obtain ⟨m, hm, hon, hoff⟩ :=
    IsConductor.exists_finitePart_agrees K h h.choose.finitePart.support
  refine ⟨⟨m.finitePart,
    m.infinitePart \ m.infinitePart.filter (fun w => realPlaceClassSubgroup K w ≤ H)⟩,
    congruenceSubgroup_sdiff_le K hm _ (fun w hw => (Finset.mem_filter.1 hw).2),
    fun m' hm' => ⟨Finsupp.le_def.2 fun v => ?_, fun w hw => ?_⟩⟩
  · by_cases hv : v ∈ h.choose.finitePart.support
    · exact hon v hv m' hm'
    · change m.finitePart v ≤ _
      rw [hoff v hv, Finsupp.notMem_support_iff.mp hv]
      exact Nat.zero_le _
  · by_contra hw'
    exact (Finset.mem_sdiff.1 hw).2 (Finset.mem_filter.2 ⟨(Finset.mem_sdiff.1 hw).1,
      (realPlaceClassSubgroup_le_congruenceSubgroup K m' w hw').trans hm'⟩)

end Atlas.Knowledge
