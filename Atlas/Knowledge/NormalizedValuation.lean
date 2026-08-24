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

## Main definitions

* `normalizedValuationHom` — the map bundled as a homomorphism into `Multiplicative ℤ`.

## Main statements

* `normalizedValuation_mul` — additivity on products.
* `normalizedValuation_pos_of_lt_one` — elements of valuation `< 1` have positive value: the
  sign anchor that machine-pins the orientation.
* `normalizedValuation_eq_zero_of_valuation_eq_one` — units of the integer ring have value `0`.
* `normalizedValuation_irreducible` — uniformizers have value exactly `1`; proved.
* `normalizedValuation_surjective` — the value group is all of `ℤ`; proved, through the
  value `1` on a uniformizer and the `zpow` law of the trio `normalizedValuation_one` /
  `normalizedValuation_inv` / `normalizedValuation_zpow`.
* `mem_ker_normalizedValuationHom` / `ker_normalizedValuationHom` — the bundled
  homomorphism's kernel is the valuation-one units, the unit group of the integers; proved.

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
convention fork is deliberate and must not be repaired silently from either side. The map
lives twice: as a bare function with a multiplicativity lemma — consumers writing `σ ^ v x`
read the bare form correctly — and bundled as `normalizedValuationHom` into
`Multiplicative ℤ` for the consumers that feed it to the Herbrand machinery.

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

private theorem neg_one_le_toAdd_unzero {a : WithZero (Multiplicative ℤ)} (ha : a ≠ 0)
    (hle : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) ≤ a) :
    -1 ≤ Multiplicative.toAdd (WithZero.unzero ha) := by
  cases a with
  | zero => exact absurd rfl ha
  | coe d =>
    rw [WithZero.unzero_coe]
    rw [WithZero.coe_le_coe] at hle
    simpa using Multiplicative.toAdd_le.mpr hle

/-- Uniformizers — irreducibles of the integer ring, read in `Kˣ` — have normalized valuation
exactly `1`: the value of an irreducible is nonzero and strictly below one, and it dominates
every value strictly below one, because the maximal ideal is what the irreducible
generates — under the order isomorphism that pins `ofAdd (-1)`, and the normalization negates
([Serre 1979, Chap. XIII, §4, Prop. 13, p.197][Serre1979];
[Yamaguchi 2026, `LocalFieldTheory/NonarchimedeanLocalField/IdealQuotients.lean:204`, sign
reversed][Yamaguchi2026]). -/
theorem normalizedValuation_irreducible (π : 𝒪[K]) (hπ : Irreducible π) (x : Kˣ)
    (hx : (x : K) = (π : K)) : normalizedValuation K x = 1 := by
  set e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K
  have hint := Valuation.integer.integers (v := valuation K)
  -- the uniformizer's value sits strictly below one
  have hvlt : valuation K (x : K) < 1 := by
    rw [hx]
    exact hint.valuation_irreducible_lt_one hπ
  have hglt : e (valuation K (x : K)) < 1 := by
    have := e.strictMono hvlt
    rwa [map_one] at this
  -- an element of value exactly `ofAdd (-1)`, which the uniformizer divides
  obtain ⟨γ, hγ⟩ := EquivLike.surjective e
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
  obtain ⟨b, rfl⟩ := ValuativeRel.valuation_surjective γ
  have hblt : valuation K b < 1 := by
    have h1 : e (valuation K b) < e 1 := by
      rw [hγ, map_one]
      exact WithZero.coe_lt_one.mpr (by decide)
    exact e.strictMono.lt_iff_lt.mp h1
  have hbmem : b ∈ 𝒪[K] := (Valuation.mem_integer_iff _ _).mpr hblt.le
  have hdvd : π ∣ (⟨b, hbmem⟩ : 𝒪[K]) := by
    rw [← Ideal.mem_span_singleton,
      ← (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ]
    exact (IsLocalRing.mem_maximalIdeal _).mpr
      (mem_nonunits_iff.mpr (Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr hblt))
  have hle : valuation K b ≤ valuation K (x : K) := by
    rw [hx]
    exact hint.le_iff_dvd.mpr hdvd
  have hgle : ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) ≤ e (valuation K (x : K)) := by
    rw [← hγ]
    exact e.strictMono.le_iff_le.mpr hle
  have h1 := toAdd_unzero_lt_zero (a := e (valuation K (x : K))) (by simp) hglt
  have h2 := neg_one_le_toAdd_unzero (a := e (valuation K (x : K))) (by simp) hgle
  unfold normalizedValuation
  omega

/-- The unit `1` has normalized valuation `0`
([Serre 1979, Chap. XIII, §4, p.198][Serre1979]). -/
theorem normalizedValuation_one : normalizedValuation K 1 = 0 :=
  normalizedValuation_eq_zero_of_valuation_eq_one K 1 (by simp)

/-- Inversion negates the normalized valuation
([Serre 1979, Chap. XIII, §4, p.198][Serre1979]). -/
theorem normalizedValuation_inv (x : Kˣ) :
    normalizedValuation K x⁻¹ = - normalizedValuation K x := by
  have h := normalizedValuation_mul K x x⁻¹
  rw [mul_inv_cancel, normalizedValuation_one] at h
  omega

/-- Integer powers scale the normalized valuation
([Serre 1979, Chap. XIII, §4, p.198][Serre1979]). -/
theorem normalizedValuation_zpow (x : Kˣ) (k : ℤ) :
    normalizedValuation K (x ^ k) = k * normalizedValuation K x := by
  induction k using Int.induction_on with
  | zero => simpa using normalizedValuation_one K
  | succ n ih =>
    rw [zpow_add_one, normalizedValuation_mul, ih]
    ring
  | pred n ih =>
    rw [zpow_sub_one, normalizedValuation_mul, ih, normalizedValuation_inv]
    ring

/-- The normalized valuation is surjective onto `ℤ`: the valuation is discrete and the
normalization exact, `ord_K` in the split exact sequence `1 → U_K → Kˣ → ℤ → 1` — a
uniformizer unit has value `1`, and its integer powers reach everything
([Hyeon 2025, §3, p.10][Hyeon2025]). -/
theorem normalizedValuation_surjective : Function.Surjective (normalizedValuation K) := by
  intro k
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[K])
  have hπ0 : (π : K) ≠ 0 := fun h0 => hπ.ne_zero (Subtype.ext h0)
  refine ⟨(Units.mk0 (π : K) hπ0) ^ k, ?_⟩
  rw [normalizedValuation_zpow,
    normalizedValuation_irreducible K π hπ (Units.mk0 (π : K) hπ0) rfl, mul_one]

/-- The normalized valuation bundled as a homomorphism into `Multiplicative ℤ` — the
`ord_K` of the exact sequence `1 → U_K → Kˣ → ℤ → 1`, ready for the Herbrand machinery
([Hyeon 2025, §3, p.10][Hyeon2025]). -/
noncomputable def normalizedValuationHom : Kˣ →* Multiplicative ℤ :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (normalizedValuation K x))
    (fun x y => by
      rw [← ofAdd_add, normalizedValuation_mul])

/-- **The kernel of the normalized valuation is the valuation-one units**: value `0`
exactly at valuation `1`, by the sign anchor applied to the unit and to its inverse
([Hyeon 2025, §3, p.10][Hyeon2025]). -/
theorem mem_ker_normalizedValuationHom (x : Kˣ) :
    x ∈ (normalizedValuationHom K).ker ↔ valuation K (x : K) = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h0
    have hz : normalizedValuation K x = 0 := by
      have := congrArg Multiplicative.toAdd h0
      simpa [normalizedValuationHom] using this
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := normalizedValuation_pos_of_lt_one K x hlt
      omega
    · have hxinv : valuation K ((x⁻¹ : Kˣ) : K) < 1 := by
        have hmul : valuation K ((x : Kˣ) : K) * valuation K ((x⁻¹ : Kˣ) : K) = 1 := by
          rw [← map_mul]
          simp
        have hinv : valuation K ((x⁻¹ : Kˣ) : K) = (valuation K ((x : Kˣ) : K))⁻¹ :=
          eq_inv_of_mul_eq_one_right hmul
        rw [hinv]
        exact inv_lt_one_of_one_lt₀ hgt
      have hpos := normalizedValuation_pos_of_lt_one K x⁻¹ hxinv
      rw [normalizedValuation_inv] at hpos
      omega
  · intro h1
    have := normalizedValuation_eq_zero_of_valuation_eq_one K x h1
    rw [show (1 : Multiplicative ℤ) = Multiplicative.ofAdd 0 from rfl]
    exact congrArg Multiplicative.ofAdd this

/-- **The kernel is the unit group of the integers**: value `0` exactly on `𝒪[K]ˣ` — the
identity that makes the classical `U_K` and this kernel the same subgroup of `Kˣ`, not
merely isomorphic ones ([Hyeon 2025, §3, p.10][Hyeon2025]). -/
theorem ker_normalizedValuationHom :
    (normalizedValuationHom K).ker = (𝒪[K].toSubmonoid).units := by
  ext x
  have hmul : valuation K (x : K) * valuation K ((x⁻¹ : Kˣ) : K) = 1 := by
    rw [← map_mul]
    simp
  rw [mem_ker_normalizedValuationHom, Submonoid.mem_units_iff]
  constructor
  · intro h
    have hinv : valuation K ((x⁻¹ : Kˣ) : K) = 1 := by
      rw [h, one_mul] at hmul
      exact hmul
    exact ⟨(Valuation.mem_integer_iff _ _).mpr h.le,
      (Valuation.mem_integer_iff _ _).mpr hinv.le⟩
  · rintro ⟨h1, h2⟩
    have h1' : valuation K (x : K) ≤ 1 := (Valuation.mem_integer_iff _ _).mp h1
    have h2' : valuation K ((x⁻¹ : Kˣ) : K) ≤ 1 := (Valuation.mem_integer_iff _ _).mp h2
    refine le_antisymm h1' ?_
    calc (1 : ValueGroupWithZero K)
        = valuation K (x : K) * valuation K ((x⁻¹ : Kˣ) : K) := hmul.symm
    _ ≤ valuation K (x : K) := mul_le_of_le_one_right' h2'

end Atlas.Knowledge
