import Mathlib
import Atlas.Knowledge.NormalizedValuation

/-!
# integer valuation

The normalized valuation of `Atlas.Knowledge.normalizedValuation`, read on the integer
ring: `ν : 𝒪[K] → ℤ` with junk value `0` at zero, nonnegative, additive on products,
value `1` on irreducibles, positive exactly on the maximal ideal, and ultrametric — the
`ord` of an integer element, packaged so that valuation bookkeeping over the integers
needs no `Units.mk0` plumbing at the use site. Consumers doing induction on
valuations — the Lubin–Tate valuation bootstrap of
`Atlas.Knowledge.standardLubinTatePrimitiveValuation` is the motivating one — work
here.

## Main definitions

* `integerValuation` — `ν : 𝒪[K] → ℤ`, the normalized valuation of a nonzero integer,
  junk `0` at zero.

## Main statements

* `integerValuation_of_ne_zero` — the unfolding to `normalizedValuation`; proved.
* `integerValuation_zero` / `integerValuation_one` — the junk value and the unit value;
  proved.
* `integerValuation_nonneg` / `integerValuation_pos_iff` — nonnegative, positive
  exactly on the maximal ideal; proved.
* `integerValuation_mul` / `integerValuation_pow` / `integerValuation_neg` — the
  multiplicative laws; proved.
* `integerValuation_irreducible` — irreducibles have value one; proved.
* `integerValuation_add_of_lt` / `min_le_integerValuation_add` — the ultrametric
  equality and inequality; proved.

## Implementation notes

The carrier is `ℤ` and the junk value is `0` — where [Serre1979] sets `v(0) = +∞` and
Mathlib's `IsDiscreteValuationRing.addVal` junks at `⊤` in `ℕ∞` — because the `ℤ`
arithmetic is the point: subtraction does not truncate and `omega` closes the
bookkeeping, which an `ℕ∞` carrier would not survive; every lemma that needs
nonvanishing carries it as a hypothesis. The order-reversing
bridge between the multiplicative valuation and the normalized value — strict
comparison flips — is kept private: consumers reason in `ℤ`, and the bridge is the
device that lets them.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic
  local fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

private theorem toAdd_unzero_lt_iff {a b : WithZero (Multiplicative ℤ)}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    Multiplicative.toAdd (WithZero.unzero ha) < Multiplicative.toAdd (WithZero.unzero hb) ↔
      a < b := by
  cases a with
  | zero => exact absurd rfl ha
  | coe c =>
    cases b with
    | zero => exact absurd rfl hb
    | coe d =>
      rw [WithZero.unzero_coe, WithZero.unzero_coe, WithZero.coe_lt_coe]
      exact Multiplicative.toAdd_lt

private theorem unzero_congr {a b : WithZero (Multiplicative ℤ)}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : a = b) :
    WithZero.unzero ha = WithZero.unzero hb := by
  subst h
  rfl

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

open Classical in
/-- The **integer valuation** `ν : 𝒪[K] → ℤ`: the normalized valuation of a nonzero
integer element, with junk value `0` at zero — the *order* of an integer, Serre's
`v(x) = n` for `x = πⁿu` ([Serre 1979, Chap. I, §1, p.5][Serre1979];
[Hyeon 2025, §3, p.10][Hyeon2025]; the normalization is
`Atlas.Knowledge.normalizedValuation`'s). -/
noncomputable def integerValuation (y : ↥𝒪[K]) : ℤ :=
  if h : algebraMap ↥𝒪[K] K y = 0 then 0
  else normalizedValuation K (Units.mk0 (algebraMap ↥𝒪[K] K y) h)

/-- The unfolding of the integer valuation at a nonzero element. -/
theorem integerValuation_of_ne_zero {y : ↥𝒪[K]} (h : algebraMap ↥𝒪[K] K y ≠ 0) :
    integerValuation K y = normalizedValuation K (Units.mk0 (algebraMap ↥𝒪[K] K y) h) := by
  rw [integerValuation, dif_neg h]

/-- The junk value: zero valuates to zero. -/
@[simp]
theorem integerValuation_zero : integerValuation K (0 : ↥𝒪[K]) = 0 := by
  rw [integerValuation, dif_pos (by simp)]

/-- The unit value: one valuates to zero. -/
@[simp]
theorem integerValuation_one : integerValuation K (1 : ↥𝒪[K]) = 0 := by
  have h1 : algebraMap ↥𝒪[K] K (1 : ↥𝒪[K]) ≠ 0 := by
    rw [map_one]; exact one_ne_zero
  rw [integerValuation_of_ne_zero K h1,
    show Units.mk0 (algebraMap ↥𝒪[K] K (1 : ↥𝒪[K])) h1 = 1 by ext; simp,
    normalizedValuation_one]

omit [TopologicalSpace K] [IsMixedCharLocalField K] in
private theorem algebraMap_integer_ne_zero {y : ↥𝒪[K]} (hy : y ≠ 0) :
    algebraMap ↥𝒪[K] K y ≠ 0 := by
  intro h0
  exact hy (Subtype.ext h0)

/-- The order bridge: the normalized valuation reverses the multiplicative comparison. -/
private theorem normalizedValuation_lt_iff (x y : Kˣ) :
    normalizedValuation K x < normalizedValuation K y ↔
      valuation K (y : K) < valuation K (x : K) := by
  unfold normalizedValuation
  rw [neg_lt_neg_iff, toAdd_unzero_lt_iff]
  exact ⟨fun h =>
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).strictMono.lt_iff_lt).mp h,
    fun h => (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).strictMono h⟩

/-- Equal multiplicative valuations give equal normalized valuations. -/
private theorem normalizedValuation_eq_of_valuation_eq {x y : Kˣ}
    (h : valuation K (x : K) = valuation K (y : K)) :
    normalizedValuation K x = normalizedValuation K y := by
  unfold normalizedValuation
  simp only [h]

/-- The integer valuation is nonnegative: integers have valuation at most one. -/
theorem integerValuation_nonneg (y : ↥𝒪[K]) : 0 ≤ integerValuation K y := by
  by_cases h : algebraMap ↥𝒪[K] K y = 0
  · rw [integerValuation, dif_pos h]
  · rw [integerValuation_of_ne_zero K h]
    have hle : valuation K (algebraMap ↥𝒪[K] K y) ≤ 1 := y.2
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact le_of_lt (normalizedValuation_pos_of_lt_one K _ hlt)
    · rw [normalizedValuation_eq_zero_of_valuation_eq_one K _ heq]

/-- The integer valuation is additive on products of nonzero elements. -/
theorem integerValuation_mul {y z : ↥𝒪[K]} (hy : y ≠ 0) (hz : z ≠ 0) :
    integerValuation K (y * z) = integerValuation K y + integerValuation K z := by
  have hy' := algebraMap_integer_ne_zero K hy
  have hz' := algebraMap_integer_ne_zero K hz
  have hyz' : algebraMap ↥𝒪[K] K (y * z) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hy' hz'
  rw [integerValuation_of_ne_zero K hy', integerValuation_of_ne_zero K hz',
    integerValuation_of_ne_zero K hyz']
  rw [show Units.mk0 (algebraMap ↥𝒪[K] K (y * z)) hyz' =
    Units.mk0 (algebraMap ↥𝒪[K] K y) hy' * Units.mk0 (algebraMap ↥𝒪[K] K z) hz' by
      ext; simp]
  exact normalizedValuation_mul K _ _

/-- Powers scale the integer valuation. -/
theorem integerValuation_pow (y : ↥𝒪[K]) (k : ℕ) :
    integerValuation K (y ^ k) = k * integerValuation K y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [zero_pow (by omega : k ≠ 0), integerValuation_zero, mul_zero]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, integerValuation_mul K (pow_ne_zero k hy) hy, ih]
    push_cast
    ring

/-- Negation preserves the integer valuation. -/
theorem integerValuation_neg (y : ↥𝒪[K]) :
    integerValuation K (-y) = integerValuation K y := by
  by_cases h : algebraMap ↥𝒪[K] K y = 0
  · have h' : algebraMap ↥𝒪[K] K (-y) = 0 := by rw [map_neg, h, neg_zero]
    simp only [integerValuation, dif_pos h, dif_pos h']
  · have h' : algebraMap ↥𝒪[K] K (-y) ≠ 0 := by
      rw [map_neg]; exact neg_ne_zero.mpr h
    rw [integerValuation_of_ne_zero K h, integerValuation_of_ne_zero K h']
    refine normalizedValuation_eq_of_valuation_eq K ?_
    change valuation K (algebraMap ↥𝒪[K] K (-y)) = valuation K (algebraMap ↥𝒪[K] K y)
    rw [map_neg, Valuation.map_neg]

/-- **Positivity detects the maximal ideal**: a nonzero integer has positive value
exactly when it is a nonunit ([Hyeon 2025, §3, p.10][Hyeon2025]). -/
theorem integerValuation_pos_iff {y : ↥𝒪[K]} (hy : y ≠ 0) :
    0 < integerValuation K y ↔ y ∈ 𝓂[K] := by
  have hy' := algebraMap_integer_ne_zero K hy
  rw [integerValuation_of_ne_zero K hy']
  constructor
  · intro hpos
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    by_contra hnot
    have heq : valuation K (algebraMap ↥𝒪[K] K y) = 1 := by
      have hle : valuation K (algebraMap ↥𝒪[K] K y) ≤ 1 := y.2
      rcases lt_or_eq_of_le hle with hlt | heq'
      · exact absurd hlt hnot
      · exact heq'
    rw [normalizedValuation_eq_zero_of_valuation_eq_one K _ heq] at hpos
    omega
  · intro hmem
    refine normalizedValuation_pos_of_lt_one K _ ?_
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hmem
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp hmem

/-- Irreducibles — the uniformizers of the integer ring — have integer valuation
exactly one ([Hyeon 2025, §3, p.10][Hyeon2025]). -/
theorem integerValuation_irreducible {y : ↥𝒪[K]} (hy : Irreducible y) :
    integerValuation K y = 1 := by
  have hy' := algebraMap_integer_ne_zero K hy.ne_zero
  rw [integerValuation_of_ne_zero K hy']
  exact normalizedValuation_irreducible K y hy _ rfl

/-- **The ultrametric equality**: when the values differ, the sum takes the smaller
value ([Serre 1979, Chap. I, §1, p.5][Serre1979], property b) of the valuation, read
through the normalization). -/
theorem integerValuation_add_of_lt {y z : ↥𝒪[K]} (hy : y ≠ 0)
    (h : integerValuation K y < integerValuation K z) :
    integerValuation K (y + z) = integerValuation K y := by
  have hz : z ≠ 0 := by
    rintro rfl
    rw [integerValuation_zero] at h
    exact absurd h (not_lt.mpr (integerValuation_nonneg K y))
  have hy' := algebraMap_integer_ne_zero K hy
  have hz' := algebraMap_integer_ne_zero K hz
  have hvlt : valuation K (algebraMap ↥𝒪[K] K z) < valuation K (algebraMap ↥𝒪[K] K y) := by
    rw [integerValuation_of_ne_zero K hy', integerValuation_of_ne_zero K hz'] at h
    exact (normalizedValuation_lt_iff K _ _).mp h
  have hvsum : valuation K (algebraMap ↥𝒪[K] K (y + z)) =
      valuation K (algebraMap ↥𝒪[K] K y) := by
    rw [map_add]
    exact Valuation.map_add_eq_of_lt_left _ hvlt
  have hsum' : algebraMap ↥𝒪[K] K (y + z) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hvsum
    exact hy' ((valuation K).zero_iff.mp hvsum.symm)
  rw [integerValuation_of_ne_zero K hsum', integerValuation_of_ne_zero K hy']
  exact normalizedValuation_eq_of_valuation_eq K hvsum

/-- **The ultrametric inequality**: a nonvanishing sum is at least the smaller value
([Serre 1979, Chap. I, §1, p.5][Serre1979], property b) of the valuation). -/
theorem min_le_integerValuation_add {y z : ↥𝒪[K]} (hsum : y + z ≠ 0) :
    min (integerValuation K y) (integerValuation K z) ≤ integerValuation K (y + z) := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [zero_add]
    exact min_le_right _ _
  rcases eq_or_ne z 0 with rfl | hz
  · rw [add_zero]
    exact min_le_left _ _
  have hy' := algebraMap_integer_ne_zero K hy
  have hz' := algebraMap_integer_ne_zero K hz
  have hsum' := algebraMap_integer_ne_zero K hsum
  rcases lt_trichotomy (integerValuation K y) (integerValuation K z) with hlt | heq | hgt
  · rw [integerValuation_add_of_lt K hy hlt]
    exact min_le_left _ _
  · by_contra hcon
    rw [heq, min_self, not_le] at hcon
    have hzv := integerValuation_of_ne_zero K hz'
    have hsv := integerValuation_of_ne_zero K hsum'
    rw [hsv, hzv] at hcon
    have hvzlt : valuation K (algebraMap ↥𝒪[K] K z) <
        valuation K (algebraMap ↥𝒪[K] K (y + z)) :=
      (normalizedValuation_lt_iff K _ _).mp hcon
    have hveq : valuation K (algebraMap ↥𝒪[K] K y) =
        valuation K (algebraMap ↥𝒪[K] K z) := by
      rcases lt_trichotomy (valuation K (algebraMap ↥𝒪[K] K y))
          (valuation K (algebraMap ↥𝒪[K] K z)) with h1 | h1 | h1
      · have := (normalizedValuation_lt_iff K (Units.mk0 _ hz') (Units.mk0 _ hy')).mpr h1
        rw [← hzv, ← integerValuation_of_ne_zero K hy'] at this
        omega
      · exact h1
      · have := (normalizedValuation_lt_iff K (Units.mk0 _ hy') (Units.mk0 _ hz')).mpr h1
        rw [← hzv, ← integerValuation_of_ne_zero K hy'] at this
        omega
    have hvle : valuation K (algebraMap ↥𝒪[K] K (y + z)) ≤
        valuation K (algebraMap ↥𝒪[K] K z) := by
      rw [map_add]
      refine le_trans (Valuation.map_add _ _ _) ?_
      rw [max_le_iff]
      exact ⟨hveq.le, le_refl _⟩
    exact absurd hvle (not_le.mpr hvzlt)
  · rw [add_comm] at hsum ⊢
    rw [integerValuation_add_of_lt K hz hgt]
    exact min_le_right _ _

end Atlas.Knowledge
