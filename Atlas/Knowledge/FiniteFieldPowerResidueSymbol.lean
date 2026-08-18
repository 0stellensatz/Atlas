import Mathlib

/-!
# finite-field power residue symbol

The `n`-th power residue symbol of a finite field: for `n` dividing `q - 1`, the character
`u ↦ u ^ ((q - 1) / n)` from the units into the `n`-th roots of unity. Its kernel is
exactly the subgroup of `n`-th powers — the counting argument through cyclicity of the
unit group — which is what makes the symbol detect power residues. This is the residue
layer under `Atlas.Knowledge.PrimeIdealPowerResidueSymbol`; everything here is proved.

## Main definitions

* `finiteFieldPowerResidueSymbol` — `kˣ →* ↥(rootsOfUnity n k)`.

## Main statements

* `finiteFieldPowerResidueSymbol_apply` — the value is `u ^ ((q - 1) / n)`.
* `finiteFieldPowerResidueSymbol_eq_one_iff` — the kernel is the `n`-th powers.

## Implementation notes

The codomain is Mathlib's `rootsOfUnity n k` inside `kˣ`. The kernel computation
identifies the range of the `n`-th power map with the kernel of the `(q - 1)/n`-th power
map by comparing cardinalities through `IsCyclic.card_powMonoidHom_ker` and `_range` —
the source's route verbatim (`AlgebraicNumberTheory/PowerResidueSymbols/FiniteField.lean:21`,
`:47`); Milne reads the same fact off the exact sequence
`1 → 𝔽_q^{×n} → 𝔽_q^× → μ_n → 1`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

variable (k : Type*) [Field k] [Fintype k]

/-- The **finite-field power residue symbol**: for `n ∣ q - 1`, the character
`u ↦ u ^ ((q - 1) / n)` into the `n`-th roots of unity
([Milne 2020, Chap. VIII, §5, p.244][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/PowerResidueSymbols/FiniteField.lean:21`]
[Yamaguchi2026]). -/
def finiteFieldPowerResidueSymbol (n : ℕ) (hn : n ∣ Fintype.card k - 1) :
    kˣ →* rootsOfUnity n k where
  toFun u :=
    ⟨u ^ ((Fintype.card k - 1) / n), by
      rw [mem_rootsOfUnity, ← pow_mul, Nat.div_mul_cancel hn]
      exact Units.ext (FiniteField.pow_card_sub_one_eq_one (u : k) (Units.ne_zero u))⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' u v := by
    apply Subtype.ext
    simp [mul_pow]

variable {k}

/-- The symbol's value is the `(q - 1)/n`-th power of its argument
([Milne 2020, Chap. VIII, §5, p.244][MilneCFT]). -/
@[simp]
theorem finiteFieldPowerResidueSymbol_apply (n : ℕ) (hn : n ∣ Fintype.card k - 1)
    (u : kˣ) :
    ((finiteFieldPowerResidueSymbol k n hn u : rootsOfUnity n k) : kˣ) =
      u ^ ((Fintype.card k - 1) / n) :=
  rfl

/-- The symbol is trivial exactly on the `n`-th powers — the kernel computation through
the cyclic unit group ([Milne 2020, Chap. VIII, §5, 5.2, p.244][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/PowerResidueSymbols/FiniteField.lean:47`]
[Yamaguchi2026]). -/
theorem finiteFieldPowerResidueSymbol_eq_one_iff (n : ℕ)
    (hn : n ∣ Fintype.card k - 1) (u : kˣ) :
    finiteFieldPowerResidueSymbol k n hn u = 1 ↔ ∃ v : kˣ, v ^ n = u := by
  classical
  let m := (Fintype.card k - 1) / n
  have hRange_le_ker : (powMonoidHom n : kˣ →* kˣ).range ≤ (powMonoidHom m).ker := by
    rintro _ ⟨v, rfl⟩
    rw [MonoidHom.mem_ker]
    change (v ^ n) ^ m = 1
    rw [← pow_mul, Nat.mul_comm n m, Nat.div_mul_cancel hn]
    exact Units.ext (FiniteField.pow_card_sub_one_eq_one (v : k) (Units.ne_zero v))
  have hUnitsCard : Nat.card kˣ = Fintype.card k - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  have hCard : Nat.card (powMonoidHom m : kˣ →* kˣ).ker ≤
      Nat.card (powMonoidHom n : kˣ →* kˣ).range := by
    rw [IsCyclic.card_powMonoidHom_ker, IsCyclic.card_powMonoidHom_range, hUnitsCard,
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd hn), Nat.gcd_eq_right hn]
  have hRange_eq_ker : (powMonoidHom n : kˣ →* kˣ).range = (powMonoidHom m).ker :=
    Subgroup.eq_of_le_of_card_ge hRange_le_ker hCard
  constructor
  · intro hsymbol
    have huKer : u ∈ (powMonoidHom m : kˣ →* kˣ).ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hsymbol
    rw [← hRange_eq_ker] at huKer
    exact huKer
  · rintro ⟨v, hv⟩
    have huKer : u ∈ (powMonoidHom m : kˣ →* kˣ).ker := by
      rw [← hRange_eq_ker]
      exact ⟨v, hv⟩
    exact Subtype.ext (MonoidHom.mem_ker.mp huKer)

end Atlas.Knowledge
