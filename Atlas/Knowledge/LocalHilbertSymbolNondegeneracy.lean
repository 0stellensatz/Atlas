import Mathlib
import Atlas.Knowledge.IsLocalHilbertSymbol

/-!
# nondegeneracy of the local Hilbert symbol

The Hilbert symbol descends to a nondegenerate pairing on `Kˣ / (Kˣ)ⁿ`: an element killed
against everything is an `n`-th power, in either slot. The two kernel characterizations are
stated as equivalences whose trivial directions are already proved in
`Atlas.Knowledge.IsLocalHilbertSymbol`; the substantial directions — the common kernel is no
larger than the powers — are the recorded claims, and the principal statement packages the
two, matching the shape the read repository proves. The quotient pairing itself is not
constructed: nondegeneracy on the quotient *is* the kernel statement on representatives, and
the layer states in Mathlib's vocabulary rather than bundling a descended map.

## Main statements

* `localHilbertSymbol_nondegeneracy` — both kernels are exactly the `n`-th powers.
* `localHilbertSymbol_left_kernel` / `localHilbertSymbol_right_kernel` — the two slots'
  kernel characterizations, each an equivalence with its trivial direction proved and its
  substantial direction recorded ahead of its proof.

## Implementation notes

The `n`-th powers enter as `MonoidHom.range (powMonoidHom n)`, the mapped-subgroup form the
layer already uses for norm groups. The left statement quantifies the second slot and needs
no `n ≠ 0` in its proved direction — the root of an `n`-th power is rational outright — while
the right one runs through the values being `n`-th roots of unity. The source proves the
left kernel from its maximal-Kummer-extension apparatus
(`LocalClassFieldTheory/Kummer/LocalHilbertPairingNondegeneracy.lean:49`), derives the right
kernel from it through skew-symmetry (`:120`), and packages nondegeneracy at `:355` — on the
descended quotient, so the shape stated here on representatives is that of `:49` and `:120`;
the discharge of the claims will follow that route.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
variable {n : ℕ} {h : Kˣ → Kˣ → Kˣ}

/-- The left kernel of the Hilbert symbol is exactly the `n`-th powers: `h a b = 1` for
every `b` iff `a ∈ (Kˣ)ⁿ`. The forward direction is a claim recorded ahead of its proof; the
reverse is `Atlas.Knowledge.IsLocalHilbertSymbol.pow_left_eq_one`
([Serre 1979, Chap. XIV, §2, Prop. 7 vi, p.208][Serre1979];
[Milne 2020, Chap. III, §4, Thm. 4.4 (c), p.113][MilneCFT];
[Yamaguchi 2026,
`LocalClassFieldTheory/Kummer/LocalHilbertPairingNondegeneracy.lean:49`][Yamaguchi2026]). -/
theorem localHilbertSymbol_left_kernel (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) (a : Kˣ) :
    (∀ b : Kˣ, h a b = 1) ↔ a ∈ MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ) := by
  constructor
  · intro ha
    sorry
  · rintro ⟨c, hc⟩ b
    have hc' : c ^ n = a := hc
    rw [← hc']
    exact IsLocalHilbertSymbol.pow_left_eq_one hh c b

/-- The right kernel of the Hilbert symbol is exactly the `n`-th powers: `h a b = 1` for
every `a` iff `b ∈ (Kˣ)ⁿ`. The forward direction is a claim recorded ahead of its proof; the
reverse is `Atlas.Knowledge.IsLocalHilbertSymbol.pow_right_eq_one`
([Serre 1979, Chap. XIV, §2, Prop. 7 and Cor., pp.208–209][Serre1979];
[Milne 2020, Chap. III, §4, Thm. 4.4 (c), p.113][MilneCFT];
[Yamaguchi 2026,
`LocalClassFieldTheory/Kummer/LocalHilbertPairingNondegeneracy.lean:120`][Yamaguchi2026]). -/
theorem localHilbertSymbol_right_kernel (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) (b : Kˣ) :
    (∀ a : Kˣ, h a b = 1) ↔ b ∈ MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ) := by
  constructor
  · intro hb
    sorry
  · rintro ⟨c, hc⟩ a
    have hc' : c ^ n = b := hc
    rw [← hc']
    exact IsLocalHilbertSymbol.pow_right_eq_one hh hn a c

/-- **Nondegeneracy of the local Hilbert symbol**: on power classes, both kernels are
trivial — an element paired to `1` against everything is an `n`-th power, in either slot.
Derived from the two kernel characterizations, whose recorded claims carry the backlog
([Serre 1979, Chap. XIV, §2, Prop. 7 vi and Cor., pp.208–209][Serre1979];
[Milne 2020, Chap. III, §4, Thm. 4.4 (c), p.113][MilneCFT];
[Yamaguchi 2026,
`LocalClassFieldTheory/Kummer/LocalHilbertPairingNondegeneracy.lean:355`][Yamaguchi2026]). -/
theorem localHilbertSymbol_nondegeneracy (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) :
    (∀ a : Kˣ, (∀ b : Kˣ, h a b = 1) →
      a ∈ MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ)) ∧
    (∀ b : Kˣ, (∀ a : Kˣ, h a b = 1) →
      b ∈ MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ)) :=
  ⟨fun a ha => (localHilbertSymbol_left_kernel K hh hn hmu a).mp ha,
    fun b hb => (localHilbertSymbol_right_kernel K hh hn hmu b).mp hb⟩

end Atlas.Knowledge
