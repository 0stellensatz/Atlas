import Mathlib
import Atlas.Knowledge.DenseGaloisFixedElement
import Atlas.Knowledge.IsLocalHilbertSymbol
import Atlas.Knowledge.IsLocalReciprocity
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LocalHilbertSymbolSkewSymmetry

/-!
# nondegeneracy of the local Hilbert symbol

The Hilbert symbol descends to a nondegenerate pairing on `Kˣ / (Kˣ)ⁿ`: an element killed
against everything is an `n`-th power, in either slot. The two kernel characterizations are
stated as equivalences whose trivial directions are proved in
`Atlas.Knowledge.IsLocalHilbertSymbol`. The substantial direction of the left kernel is
proved here by density: a root of `a` killed against every `b` is fixed by every lift of
every value of the reciprocity map, a dense set of automorphisms, hence is rational. The
substantial direction of the right kernel — the common kernel of the second slot is no larger
than the powers — is proved from skew-symmetry: an element killed against everything in the
second slot is killed against everything in the first, by
`Atlas.Knowledge.LocalHilbertSymbolSkewSymmetry`, and the left kernel finishes. The principal
statement packages the two, matching the shape the read repository proves, and the file
carries no recorded claim. The quotient pairing itself is not constructed: nondegeneracy on
the quotient *is* the kernel statement on representatives, and the layer states in Mathlib's
vocabulary rather than bundling a descended map.

## Main statements

* `localHilbertSymbol_nondegeneracy` — both kernels are exactly the `n`-th powers; proved.
* `localHilbertSymbol_left_kernel` — the first slot's kernel characterization; proved, the
  substantial direction by the density of the reciprocity map's range.
* `localHilbertSymbol_right_kernel` — the second slot's kernel characterization; proved, the
  substantial direction by skew-symmetry into the left kernel.

## Implementation notes

The `n`-th powers enter as `MonoidHom.range (powMonoidHom n)`, the mapped-subgroup form the
layer already uses for norm groups. The left statement quantifies the second slot and needs
no `n ≠ 0` in its trivial direction — the root of an `n`-th power is rational outright —
while the right one runs through the values being `n`-th roots of unity. The left kernel's
substantial direction needs no roots of unity at all: the lifts of the values `φ (b)` form
the preimage of a dense range — the `denseRange` field of
`Atlas.Knowledge.IsLocalReciprocity` — under the open quotient map onto `G_K^ab`, they all
fix a root of `a` once every `h a b` is `1`, and `Atlas.Knowledge.denseGaloisFixedElement`
puts the root in `K`; the `hmu` binder of `localHilbertSymbol_left_kernel` is therefore
carried unused, the statement keeping its recorded form beside its sibling. The source proves
the left kernel from its maximal-Kummer-extension apparatus
(`LocalClassFieldTheory/Kummer/LocalHilbertPairingNondegeneracy.lean:49`), derives the right
kernel from it through skew-symmetry (`:120`), and packages nondegeneracy at `:355` — on the
descended quotient, so the shape stated here on representatives is that of `:49` and `:120`.
The left kernel is discharged by density instead: the source's first slot is its Artin slot
and this layer's is its root slot, so fixing it varies the Kummer extension there and only
the reciprocity classes here, where density suffices. The right kernel is discharged by the
source's skew-symmetry route: `Atlas.Knowledge.IsLocalHilbertSymbol.skew` turns
`∀ a, h a b = 1` into `∀ a, h b a = 1`, and the left kernel at `b` finishes — which is why
its `hmu` is consumed where the left kernel's is not.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
variable {n : ℕ} {h : Kˣ → Kˣ → Kˣ}

set_option linter.unusedVariables false in
-- The roots-of-unity guard `hmu` is not consumed: the substantial direction is the density
-- argument, which reads only the reciprocity map's range, and the trivial one is
-- rational-root bookkeeping. The binder is kept so that the statement keeps its recorded
-- form; the sibling right kernel's discharge does consume it.
/-- The left kernel of the Hilbert symbol is exactly the `n`-th powers: `h a b = 1` for every
`b` iff `a ∈ (Kˣ)ⁿ`. The forward direction is the density of the reciprocity map's range —
every lift of every `φ (b)` fixes a root of `a`, so the root is fixed by a dense set of
automorphisms and is rational; the reverse is
`Atlas.Knowledge.IsLocalHilbertSymbol.pow_left_eq_one`
([Serre 1979, Chap. XIV, §2, Prop. 7 vi, p.208][Serre1979];
[Milne 2020, Chap. III, §4, Thm. 4.4 (c), p.113][MilneCFT]; Yamaguchi 2026,
`LocalClassFieldTheory/Kummer/LocalHilbertPairingNondegeneracy.lean:49`). -/
theorem localHilbertSymbol_left_kernel (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) (a : Kˣ) :
    (∀ b : Kˣ, h a b = 1) ↔ a ∈ MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ) := by
  constructor
  · intro ha
    obtain ⟨φ, hφ, hspec⟩ := hh
    obtain ⟨β, hβ⟩ := IsAlgClosed.exists_pow_nat_eq
      (algebraMap K (AlgebraicClosure K) (a : K)) (Nat.pos_of_ne_zero hn)
    haveI : IsGalois K (AlgebraicClosure K) := ⟨⟩
    have hdense : Dense ((QuotientGroup.mk : Field.absoluteGaloisGroup K →
        Field.absoluteGaloisGroupAbelianization K) ⁻¹' Set.range φ) :=
      hφ.denseRange.preimage QuotientGroup.isOpenMap_coe
    have hfix : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
        (σ : Field.absoluteGaloisGroup K) ∈ ((QuotientGroup.mk : Field.absoluteGaloisGroup K →
          Field.absoluteGaloisGroupAbelianization K) ⁻¹' Set.range φ) → σ β = β := by
      rintro σ ⟨b, hb⟩
      have h1 := hspec a b σ hb.symm β hβ
      rw [ha b, Units.val_one, map_one, one_mul] at h1
      exact h1
    obtain ⟨x, hx⟩ := denseGaloisFixedElement hdense hfix
    have ha0 : algebraMap K (AlgebraicClosure K) (a : K) ≠ 0 :=
      (map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr a.ne_zero
    have hx0 : x ≠ 0 := by
      rintro rfl
      apply ha0
      rw [← hβ, ← hx, (algebraMap K (AlgebraicClosure K)).map_zero, zero_pow hn]
    refine ⟨Units.mk0 x hx0, Units.ext ?_⟩
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mk0, map_pow, hx, hβ]
  · rintro ⟨c, hc⟩ b
    have hc' : c ^ n = a := hc
    rw [← hc']
    exact IsLocalHilbertSymbol.pow_left_eq_one hh c b

/-- The right kernel of the Hilbert symbol is exactly the `n`-th powers: `h a b = 1` for
every `a` iff `b ∈ (Kˣ)ⁿ`. The forward direction is skew-symmetry into the left kernel —
`h b a = (h a b)⁻¹` for every `a`, so `b` lies in the left kernel; the reverse is
`Atlas.Knowledge.IsLocalHilbertSymbol.pow_right_eq_one`
([Serre 1979, Chap. XIV, §2, Prop. 7 and Cor., pp.208–209][Serre1979];
[Milne 2020, Chap. III, §4, Thm. 4.4 (c), p.113][MilneCFT]; Yamaguchi 2026,
`LocalClassFieldTheory/Kummer/LocalHilbertPairingNondegeneracy.lean:120`). -/
theorem localHilbertSymbol_right_kernel (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) (b : Kˣ) :
    (∀ a : Kˣ, h a b = 1) ↔ b ∈ MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ) := by
  constructor
  · intro hb
    refine (localHilbertSymbol_left_kernel K hh hn hmu b).mp (fun a => ?_)
    have h1 := IsLocalHilbertSymbol.skew hh hn hmu b a
    rw [hb a, mul_one] at h1
    exact h1
  · rintro ⟨c, hc⟩ a
    have hc' : c ^ n = b := hc
    rw [← hc']
    exact IsLocalHilbertSymbol.pow_right_eq_one hh hn a c

/-- **Nondegeneracy of the local Hilbert symbol**: on power classes, both kernels are
trivial: an element paired to `1` against everything is an `n`-th power, in either slot.
Derived from the two kernel characterizations, both proved
([Serre 1979, Chap. XIV, §2, Prop. 7 vi and Cor., pp.208–209][Serre1979];
[Milne 2020, Chap. III, §4, Thm. 4.4 (c), p.113][MilneCFT]; Yamaguchi 2026,
`LocalClassFieldTheory/Kummer/LocalHilbertPairingNondegeneracy.lean:355`). -/
theorem localHilbertSymbol_nondegeneracy (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) :
    (∀ a : Kˣ, (∀ b : Kˣ, h a b = 1) →
      a ∈ MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ)) ∧
    (∀ b : Kˣ, (∀ a : Kˣ, h a b = 1) →
      b ∈ MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ)) :=
  ⟨fun a ha => (localHilbertSymbol_left_kernel K hh hn hmu a).mp ha,
    fun b hb => (localHilbertSymbol_right_kernel K hh hn hmu b).mp hb⟩

end Atlas.Knowledge
