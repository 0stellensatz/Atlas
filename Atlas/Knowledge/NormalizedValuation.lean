import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# normalized valuation

The normalized additive valuation of a mixed-characteristic local field: `v : Kˣ → ℤ`,
surjective with value `+1` on uniformizers, the map written `ord_K` in the anabelian
literature. Mathlib carries the multiplicative valuation and, under
`IsNonarchimedeanLocalField`, the order isomorphism
`valueGroupWithZeroIsoInt : ValueGroupWithZero K ≃*o ℤᵐ⁰` — but no additive ℤ-valued
valuation; this item defines one by reading an element's value through that isomorphism and
negating.

## Main definitions

* `normalizedValuation` — `v : Kˣ → ℤ`, uniformizer ↦ `+1`.

## Main statements

* `normalizedValuation_mul` — additivity on products.
* `normalizedValuation_pos_of_lt_one` — elements of valuation `< 1` have positive value: the
  sign anchor that machine-pins the orientation.
* `normalizedValuation_eq_zero_of_valuation_eq_one` — units of the integer ring have value `0`.
* `normalizedValuation_irreducible` — uniformizers have value exactly `1`, recorded ahead of
  its proof.
* `normalizedValuation_surjective` — the value group is all of `ℤ`, recorded ahead of its
  proof.

## Implementation notes

The sign is a decision, made once here for the layer: the order isomorphism is forced to send
the valuation of a uniformizer — an element `< 1` — to `ofAdd (-1)`, so the raw `toAdd`
readout gives uniformizers value `-1`, and this item negates it to the classical orientation
`v (π) = +1` of [Serre1979] and [Hyeon2025]. The repository read alongside keeps the raw
readout instead — its `valuationMap`
(`LocalFieldTheory/NonarchimedeanLocalField/ValuationExactSequence.lean:31`, values `-1` on
uniformizers per `LocalFieldTheory/NonarchimedeanLocalField/IdealQuotients.lean:204`) calls
itself inverse-standard out loud (`ValuationExactSequence.lean:82`) — so any port of its
proofs into this vocabulary must compose with negation; the
convention fork is deliberate and must not be repaired silently from either side. The map is
kept a bare function with a multiplicativity lemma rather than a bundled `MonoidHom` into
`Multiplicative ℤ`: every consumer writes `σ ^ v x`, where the bare form reads correctly.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic
  local fields*, J. London Math. Soc. **112** (2025), e70402.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- The **normalized valuation** `v : Kˣ → ℤ` of a mixed-characteristic local field:
the value of `x` under the order isomorphism of the value group with `ℤᵐ⁰`, negated so that
uniformizers get `+1` — the `ord_K` of the reciprocity diagram
([Serre 1979, Chap. XIII, §4, Prop. 13, p.197][Serre1979];
[Hyeon 2025, §3, p.10][Hyeon2025]). -/
noncomputable def normalizedValuation (x : Kˣ) : ℤ :=
  - Multiplicative.toAdd
      (WithZero.unzero
        (x := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (x : K)))
        (by simp))

private theorem toAdd_unzero_mul {a b c : WithZero (Multiplicative ℤ)}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (h : c = a * b) :
    Multiplicative.toAdd (WithZero.unzero hc) =
      Multiplicative.toAdd (WithZero.unzero ha) + Multiplicative.toAdd (WithZero.unzero hb) := by
  subst h
  rw [WithZero.unzero_mul hc]
  cases a with
  | zero => exact absurd rfl ha
  | coe d =>
    cases b with
    | zero => exact absurd rfl hb
    | coe e =>
      rw [WithZero.unzero_coe, WithZero.unzero_coe]
      rfl

/-- The normalized valuation is additive on products
([Serre 1979, Chap. XIII, §4, p.198][Serre1979]). -/
theorem normalizedValuation_mul (x y : Kˣ) :
    normalizedValuation K (x * y) = normalizedValuation K x + normalizedValuation K y := by
  unfold normalizedValuation
  have hxy : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
        (valuation K ((x * y : Kˣ) : K)) =
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (x : K)) *
        IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (y : K)) := by
    rw [← map_mul]; congr 1; rw [Units.val_mul, map_mul]
  have := toAdd_unzero_mul (by simp) (by simp) (by simp) hxy
  omega

private theorem toAdd_unzero_lt_zero {a : WithZero (Multiplicative ℤ)} (ha : a ≠ 0)
    (hlt : a < 1) : Multiplicative.toAdd (WithZero.unzero ha) < 0 := by
  cases a with
  | zero => exact absurd rfl ha
  | coe d =>
    rw [WithZero.unzero_coe]
    have h1 : (d : WithZero (Multiplicative ℤ)) <
        ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := by simpa using hlt
    rw [WithZero.coe_lt_coe] at h1
    exact Multiplicative.toAdd_lt.mpr h1

/-- Elements of multiplicative valuation `< 1` have positive normalized valuation: the sign
anchor. Together with `Atlas.Knowledge.normalizedValuation_mul` this pins the classical
orientation — uniformizers land at `+1`, not `-1` — as a machine-checked fact rather than a
docstring promise ([Serre 1979, Chap. XIII, §4, Prop. 13, p.197][Serre1979]). -/
theorem normalizedValuation_pos_of_lt_one (x : Kˣ) (hx : valuation K (x : K) < 1) :
    0 < normalizedValuation K x := by
  have hlt : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (x : K)) < 1 := by
    have := (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).strictMono hx
    rwa [map_one] at this
  have := toAdd_unzero_lt_zero (a :=
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (x : K))) (by simp) hlt
  unfold normalizedValuation
  omega

private theorem toAdd_unzero_eq_zero {a : WithZero (Multiplicative ℤ)} (ha : a ≠ 0)
    (h1 : a = 1) : Multiplicative.toAdd (WithZero.unzero ha) = 0 := by
  cases a with
  | zero => exact absurd rfl ha
  | coe d =>
    rw [WithZero.unzero_coe]
    have : d = 1 := by
      rw [show (1 : WithZero (Multiplicative ℤ)) =
        ((1 : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl] at h1
      exact WithZero.coe_inj.mp h1
    rw [this]; rfl

/-- Elements of multiplicative valuation `1` — the units of the integer ring — have
normalized valuation `0` ([Serre 1979, Chap. XIII, §4, p.198][Serre1979]). -/
theorem normalizedValuation_eq_zero_of_valuation_eq_one (x : Kˣ)
    (hx : valuation K (x : K) = 1) : normalizedValuation K x = 0 := by
  have h1 : IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (x : K)) = 1 := by
    rw [hx, map_one]
  have := toAdd_unzero_eq_zero (a :=
    IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K (valuation K (x : K))) (by simp) h1
  unfold normalizedValuation
  omega

/-- Uniformizers — irreducibles of the integer ring, read in `Kˣ` — have normalized valuation
exactly `1`. Claim recorded ahead of its proof
([Serre 1979, Chap. XIII, §4, Prop. 13, p.197][Serre1979];
[Yamaguchi 2026, `LocalFieldTheory/NonarchimedeanLocalField/IdealQuotients.lean:204`, sign
reversed][Yamaguchi2026]). -/
theorem normalizedValuation_irreducible (π : 𝒪[K]) (hπ : Irreducible π) (x : Kˣ)
    (hx : (x : K) = (π : K)) : normalizedValuation K x = 1 := by
  sorry

/-- The normalized valuation is surjective onto `ℤ`: the valuation is discrete and the
normalization exact, `ord_K` in the split exact sequence `1 → U_K → Kˣ → ℤ → 1`. Claim
recorded ahead of its proof ([Hyeon 2025, §3, p.10][Hyeon2025]). -/
theorem normalizedValuation_surjective : Function.Surjective (normalizedValuation K) := by
  sorry

end Atlas.Knowledge
