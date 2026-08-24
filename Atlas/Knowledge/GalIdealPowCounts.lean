import Mathlib
import Atlas.Knowledge.HerbrandQuotient
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.PadicExpEquivariant

/-!
# graded counts of a deep ideal power

The additive Galois module of a deep ideal power of a cyclic extension of
mixed-characteristic local fields has equal, finite graded Tate counts:
`#Ĥ⁰(𝓂[L] ^ i) = #Ĥ¹(𝓂[L] ^ i)` at a generator of the Galois group. This is the lattice
half of the class field axiom's unit computation — a scaled orbit of Mathlib's
`IsGalois.normalBasis` spans an open `𝒪[K]`-sublattice of the ideal power isomorphic to
the co-induced shift module of `Atlas.Knowledge.HerbrandQuotient.shiftAut`, open in the
compact ideal and hence of finite index, and Serre's corollary carries the lattice's
trivial counts to the ambient ideal power.

## Main statements

* `galIdealPowCounts` — for `L/K` cyclic and any exponent `i`, the two graded pieces of
  the additive action `Atlas.Knowledge.galIdealPow` on `𝓂[L] ^ i` are finite of equal
  cardinality at `n = orderOf σ`; proved.

## Implementation notes

The lattice is `∑ 𝒪[K] · σ⁻ʲ(c · b)` over `j : ZMod (orderOf σ)`, with `b` the
normal-basis generator and `c : K` a scalar sinking the orbit into the ideal power —
inverse generator powers make the Galois action on indices the shift by `+1`. Finiteness
of the index is topological: the coordinate functionals of the orbit basis are continuous
— the normed plumbing of `Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField`, staged
on both fields, feeds `LinearMap.continuous_of_finiteDimensional` — so a deep enough
valuation ball has integral coordinates, making the lattice an open subgroup of the
compact ideal power, and `Subgroup.quotient_finite_of_isOpen` closes the index. Serre's
corollary is instantiated over an opaque carrier: applying
`Atlas.Knowledge.HerbrandQuotient.finite_of_exact` at the concrete `Multiplicative`
subtype deadlocks the elaborator's postponed unification, and the generic restatement
elaborates exactly as in the toolkit's own context.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel Nat

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] [IsMixedCharLocalField L]
  [IsGalois K L]

/- Powers of a value strictly below one sink below any nonzero value. -/
private theorem exists_pow_le (γ δ : ValueGroupWithZero L) (hγ1 : γ < 1) (hγ0 : γ ≠ 0)
    (hδ0 : δ ≠ 0) : ∃ N : ℕ, γ ^ N ≤ δ := by
  set e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L
  have hγe : e γ < 1 := by
    have := e.strictMono hγ1
    rwa [map_one] at this
  have hγe0 : e γ ≠ 0 := by simp [hγ0]
  have hδe0 : e δ ≠ 0 := by simp [hδ0]
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp hγe0
  obtain ⟨d, hd⟩ := WithZero.ne_zero_iff_exists.mp hδe0
  have haneg : Multiplicative.toAdd a ≤ -1 := by
    have h1 : (a : WithZero (Multiplicative ℤ)) < 1 := by
      rw [ha]
      exact hγe
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h1
    have h2 : Multiplicative.toAdd a < Multiplicative.toAdd (1 : Multiplicative ℤ) :=
      Multiplicative.toAdd_lt.mpr h1
    simp only [toAdd_one] at h2
    omega
  refine ⟨(Multiplicative.toAdd d).natAbs, ?_⟩
  have hmono := e.strictMono.le_iff_le (a := γ ^ (Multiplicative.toAdd d).natAbs) (b := δ)
  rw [← hmono, map_pow, ← ha, ← hd, ← WithZero.coe_pow, WithZero.coe_le_coe]
  rw [← Multiplicative.toAdd_le, _root_.toAdd_pow, nsmul_eq_mul]
  set t := Multiplicative.toAdd a
  set u := Multiplicative.toAdd d
  have hprod : ((Int.natAbs u : ℤ)) * (t + 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (by omega)
  have : ((Int.natAbs u : ℤ)) * t ≤ u := by
    rcases Int.natAbs_eq u with hu | hu
    · nlinarith [Int.natCast_nonneg (Int.natAbs u)]
    · nlinarith [Int.natCast_nonneg (Int.natAbs u)]
  exact this

/- Membership in the ideal power's field image is a valuation bound. -/
private theorem mem_idealPow_image_iff {ϖ : ↥𝒪[L]} (hϖ : Irreducible ϖ) (i : ℕ) (y : L) :
    y ∈ ((↑) : ↥𝒪[L] → L) '' ((𝓂[L] ^ i : Ideal ↥𝒪[L]) : Set ↥𝒪[L]) ↔
      valuation L y ≤ valuation L ((ϖ : L)) ^ i := by
  constructor
  · rintro ⟨⟨m, hm⟩, hmem, rfl⟩
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    have : valuation L ((⟨m, hm⟩ : ↥𝒪[L]) : L) =
        valuation L ((ϖ : L)) ^ i * valuation L ((c : ↥𝒪[L]) : L) := by
      rw [show ((⟨m, hm⟩ : ↥𝒪[L]) : L) = ((ϖ ^ i * c : ↥𝒪[L]) : L) from by rw [← hc],
        show ((ϖ ^ i * c : ↥𝒪[L]) : L) = ((ϖ : L)) ^ i * ((c : ↥𝒪[L]) : L) from by
          push_cast; ring, map_mul, map_pow]
    rw [this]
    exact mul_le_of_le_one_right'
      ((Valuation.mem_integer_iff _ _).mp (c : ↥𝒪[L]).2)
  · intro hy
    have hy1 : valuation L y ≤ 1 := by
      refine hy.trans ?_
      calc valuation L ((ϖ : L)) ^ i ≤ 1 ^ i :=
        pow_le_pow_left' ((Valuation.mem_integer_iff _ _).mp ϖ.2) i
      _ = 1 := one_pow i
    have hdvd : (ϖ ^ i) ∣ (⟨y, (Valuation.mem_integer_iff _ _).mpr hy1⟩ : ↥𝒪[L]) := by
      refine (Valuation.integer.integers (v := valuation L)).le_iff_dvd.mp ?_
      have h1 : (algebraMap ↥𝒪[L] L)
          (⟨y, (Valuation.mem_integer_iff _ _).mpr hy1⟩ : ↥𝒪[L]) = y := rfl
      have h2 : (algebraMap ↥𝒪[L] L) (ϖ ^ i) = ((ϖ : L)) ^ i := by rfl
      rw [h1, h2, map_pow]
      exact hy
    refine ⟨⟨y, (Valuation.mem_integer_iff _ _).mpr hy1⟩, ?_, rfl⟩
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
      Ideal.span_singleton_pow, SetLike.mem_coe, Ideal.mem_span_singleton]
    exact hdvd

/- A base-field scalar sinks any finite family into a prescribed ideal power: Milne's
common denominator, pushed deep ([Milne 2020, Chap. III, Lemma 2.3, p.104][MilneCFT]). -/
omit [FiniteDimensional K L] [IsGalois K L] in
private theorem exists_scale_into_ideal (i : ℕ) (s : Finset L) :
    ∃ c : K, c ≠ 0 ∧ ∀ x ∈ s, algebraMap K L c * x ∈
      ((↑) : ↥𝒪[L] → L) '' ((𝓂[L] ^ i : Ideal ↥𝒪[L]) : Set ↥𝒪[L]) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[L])
  have hϖ0 : (ϖ : L) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  -- a base element of small value in `L`
  obtain ⟨κ, hκ0, hκ1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
  have hκL1 : valuation L (algebraMap K L κ) < 1 := by
    rw [← ValuativeExtension.mapValueGroupWithZero_valuation]
    have := ValuativeExtension.mapValueGroupWithZero_strictMono (A := K) (B := L) hκ1
    rwa [map_one] at this
  have hκL0 : valuation L (algebraMap K L κ) ≠ 0 := by
    simp only [Ne, Valuation.zero_iff]
    intro h0
    exact hκ0 (by simpa using (algebraMap K L).injective (by rw [h0, map_zero]) : κ = 0)
  -- per-element sink exponents, then the maximum
  have hchoice : ∀ x ∈ s, ∃ N : ℕ, ∀ M ≥ N,
      valuation L (algebraMap K L κ) ^ M * valuation L x ≤ valuation L ((ϖ : L)) ^ i := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact ⟨0, fun M _ => by simp⟩
    have hvx0 : valuation L x ≠ 0 := (Valuation.ne_zero_iff _).mpr hx0
    have hδ0 : valuation L ((ϖ : L)) ^ i * (valuation L x)⁻¹ ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ ((Valuation.ne_zero_iff _).mpr hϖ0)) (inv_ne_zero hvx0)
    obtain ⟨N, hN⟩ := exists_pow_le L (valuation L (algebraMap K L κ))
      (valuation L ((ϖ : L)) ^ i * (valuation L x)⁻¹) hκL1 hκL0 hδ0
    refine ⟨N, fun M hM => ?_⟩
    have hmono : valuation L (algebraMap K L κ) ^ M ≤
        valuation L (algebraMap K L κ) ^ N :=
      pow_le_pow_right_of_le_one' (le_of_lt hκL1) hM
    calc valuation L (algebraMap K L κ) ^ M * valuation L x
        ≤ (valuation L ((ϖ : L)) ^ i * (valuation L x)⁻¹) * valuation L x :=
          mul_le_mul' (hmono.trans hN) le_rfl
      _ = valuation L ((ϖ : L)) ^ i := by
          rw [mul_assoc, inv_mul_cancel₀ hvx0, mul_one]
  choose Nfun hNfun using hchoice
  classical
  refine ⟨κ ^ (s.attach.sup fun x => Nfun x x.2), pow_ne_zero _ hκ0, fun x hx => ?_⟩
  rw [mem_idealPow_image_iff L hϖ, map_pow, map_mul, map_pow]
  exact hNfun x hx _ (Finset.le_sup (f := fun x => Nfun x.1 x.2) (s.mem_attach ⟨x, hx⟩))


section OrbitLattice

open HerbrandQuotient

variable {K} {L}
variable (σ : L ≃ₐ[K] L)

/- Inverse generator powers indexed by the cyclic group: the labelling under which the
Galois action on the orbit is the co-induced module's shift by one. -/
private noncomputable def gpow (j : ZMod (orderOf σ)) : L ≃ₐ[K] L := σ ^ (-(j.val : ℤ))

/- Integer powers of the generator depend only on the exponent mod its order. -/
omit [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [ValuativeExtension K L] [FiniteDimensional K L]
  [IsMixedCharLocalField L] [IsGalois K L] in
private theorem zpow_val_eq {a b : ℤ} (h : (a : ZMod (orderOf σ)) = (b : ZMod (orderOf σ))) :
    σ ^ a = σ ^ b := by
  have hd : ((orderOf σ : ℕ) : ℤ) ∣ a - b := by
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
  obtain ⟨k, hk⟩ := hd
  have h1 : σ ^ (a - b) = 1 := by
    rw [hk, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  calc σ ^ a = σ ^ (b + (a - b)) := by congr 1; omega
  _ = σ ^ b * σ ^ (a - b) := zpow_add σ b (a - b)
  _ = σ ^ b := by rw [h1, mul_one]

/- The shift law: composing with the generator moves the label down by one. -/
omit [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [ValuativeExtension K L] [FiniteDimensional K L]
  [IsMixedCharLocalField L] [IsGalois K L] in
private theorem mul_gpow [NeZero (orderOf σ)] (j : ZMod (orderOf σ)) :
    σ * gpow σ j = gpow σ (j - 1) := by
  have h1 : σ * gpow σ j = σ ^ ((1 : ℤ) + -(j.val : ℤ)) := by
    rw [gpow, zpow_one_add]
  rw [h1, gpow]
  exact zpow_val_eq σ (by push_cast [ZMod.natCast_val, ZMod.cast_id]; ring)

/- Distinct labels give distinct automorphisms: `ZMod`-values stay below the order. -/
omit [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [ValuativeExtension K L] [FiniteDimensional K L]
  [IsMixedCharLocalField L] [IsGalois K L] in
private theorem gpow_injective [NeZero (orderOf σ)] : Function.Injective (gpow σ) := by
  intro j k hjk
  have hpow : σ ^ (j.val : ℤ) = σ ^ (k.val : ℤ) := by
    have h2 := congrArg Inv.inv hjk
    simpa only [gpow, zpow_neg, inv_inv] using h2
  have hpow' : σ ^ j.val = σ ^ k.val := by
    simpa only [zpow_natCast] using hpow
  exact ZMod.val_injective _
    (pow_injOn_Iio_orderOf (ZMod.val_lt j) (ZMod.val_lt k) hpow')

/- At a generator the labelling enumerates the whole group: injectivity plus the card
count `#(ZMod n) = #zpowers = #Gal`. -/
omit [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [ValuativeExtension K L] [IsMixedCharLocalField L]
  [IsGalois K L] in
private theorem gpow_bijective [NeZero (orderOf σ)]
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) : Function.Bijective (gpow σ) := by
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨gpow_injective σ, ?_⟩
  rw [Nat.card_zmod]
  have htop : Subgroup.zpowers σ = ⊤ := (Subgroup.eq_top_iff' _).mpr hgen
  have hcard := Nat.card_zpowers σ
  rw [htop] at hcard
  rw [← hcard]
  exact Subgroup.card_top

/- The orbit-lattice embedding of the co-induced module. -/

/- The orbit lattice as a hom from the co-induced module: `f ↦ ∑ f j · W (σ⁻ʲ)`, with
the orbit `W` handed in as ideal-power elements and coefficients from `𝒪[K]`. -/
set_option linter.overlappingInstances false in
private noncomputable def latticeHom [NeZero (orderOf σ)] (i : ℕ)
    (W : (L ≃ₐ[K] L) → ↥(𝓂[L] ^ i : Ideal ↥𝒪[L])) :
    (ZMod (orderOf σ) → Multiplicative ↥𝒪[K]) →*
      Multiplicative ↥(𝓂[L] ^ i : Ideal ↥𝒪[L]) where
  toFun f := Multiplicative.ofAdd (∑ j : ZMod (orderOf σ),
    algebraMap ↥𝒪[K] ↥𝒪[L] (Multiplicative.toAdd (f j)) • W (gpow σ j))
  map_one' := by
    simp
  map_mul' f g := by
    rw [← ofAdd_add]
    congr 1
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : Multiplicative.toAdd ((f * g) j) =
        Multiplicative.toAdd (f j) + Multiplicative.toAdd (g j) := rfl
    rw [h1, map_add, add_smul]

/- The embedding intertwines the shift with the ideal action: the automorphism fixes the
base coefficients and moves the orbit labels by one, and reindexing restores the sum. -/
omit [IsGalois K L] in
private theorem latticeHom_shift [NeZero (orderOf σ)] (i : ℕ)
    (W : (L ≃ₐ[K] L) → ↥(𝓂[L] ^ i : Ideal ↥𝒪[L]))
    (hW : ∀ g, galIdealPow K L σ i (W g) = W (σ * g))
    (f : ZMod (orderOf σ) → Multiplicative ↥𝒪[K]) :
    AddEquiv.toMultiplicative (galIdealPow K L σ i) (latticeHom σ i W f) =
      latticeHom σ i W (shiftAut (orderOf σ) f) := by
  have hsc : ∀ (r : ↥𝒪[K]) (w : ↥(𝓂[L] ^ i : Ideal ↥𝒪[L])),
      galIdealPow K L σ i (algebraMap ↥𝒪[K] ↥𝒪[L] r • w) =
        algebraMap ↥𝒪[K] ↥𝒪[L] r • galIdealPow K L σ i w := by
    intro r w
    refine Subtype.ext (Subtype.ext ?_)
    change σ (((algebraMap ↥𝒪[K] ↥𝒪[L] r • w : ↥(𝓂[L] ^ i : Ideal ↥𝒪[L])) : ↥𝒪[L]) : L) = _
    rw [SetLike.val_smul, smul_eq_mul]
    push_cast
    rw [map_mul, AlgEquiv.commutes, smul_eq_mul]
    rfl
  have hmap := map_sum (galIdealPow K L σ i)
    (fun j => algebraMap ↥𝒪[K] ↥𝒪[L] (Multiplicative.toAdd (f j)) • W (gpow σ j))
    (Finset.univ : Finset (ZMod (orderOf σ)))
  refine Multiplicative.toAdd.injective ?_
  change galIdealPow K L σ i (∑ j : ZMod (orderOf σ),
      algebraMap ↥𝒪[K] ↥𝒪[L] (Multiplicative.toAdd (f j)) • W (gpow σ j)) =
    ∑ j : ZMod (orderOf σ),
      algebraMap ↥𝒪[K] ↥𝒪[L] (Multiplicative.toAdd (shiftAut (orderOf σ) f j)) • W (gpow σ j)
  rw [hmap]
  refine Fintype.sum_equiv (Equiv.subRight (1 : ZMod (orderOf σ))) _ _ fun j => ?_
  rw [hsc, hW, mul_gpow]
  change algebraMap ↥𝒪[K] ↥𝒪[L] (Multiplicative.toAdd (f j)) • W (gpow σ (j - 1)) =
    algebraMap ↥𝒪[K] ↥𝒪[L] (Multiplicative.toAdd (f (j - 1 + 1))) • W (gpow σ (j - 1))
  rw [sub_add_cancel]

/- Injectivity from the linear independence of the orbit: the embedded sum's field value
is a coordinate combination in the orbit family. -/
omit [TopologicalSpace K] [IsMixedCharLocalField K] [FiniteDimensional K L]
  [IsGalois K L] in
private theorem latticeHom_injective [NeZero (orderOf σ)] (i : ℕ)
    (W : (L ≃ₐ[K] L) → ↥(𝓂[L] ^ i : Ideal ↥𝒪[L])) (b' : L)
    (hval : ∀ g : L ≃ₐ[K] L, ((W g : ↥𝒪[L]) : L) = g b')
    (hli : LinearIndependent K fun g : L ≃ₐ[K] L => g b') :
    Function.Injective (latticeHom σ i W) := by
  rw [injective_iff_map_eq_one]
  intro f hf
  have hsum0 : (∑ j : ZMod (orderOf σ),
      algebraMap ↥𝒪[K] ↥𝒪[L] (Multiplicative.toAdd (f j)) • W (gpow σ j)) = 0 := hf
  have hL : (∑ j : ZMod (orderOf σ),
      (((Multiplicative.toAdd (f j) : ↥𝒪[K]) : K) • (gpow σ j b' : L))) = 0 := by
    have h0 : (((∑ j : ZMod (orderOf σ),
        algebraMap ↥𝒪[K] ↥𝒪[L] (Multiplicative.toAdd (f j)) • W (gpow σ j) :
        ↥(𝓂[L] ^ i : Ideal ↥𝒪[L])) : ↥𝒪[L]) : L) = 0 := by
      rw [hsum0]; rfl
    rw [← h0]
    rw [AddSubmonoidClass.coe_finsetSum, AddSubmonoidClass.coe_finsetSum]
    refine (Finset.sum_congr rfl fun j _ => ?_).symm
    rw [SetLike.val_smul, smul_eq_mul]
    push_cast
    rw [hval, Algebra.smul_def]
  have hli' : LinearIndependent K fun j : ZMod (orderOf σ) => (gpow σ j) b' :=
    hli.comp (gpow σ) (gpow_injective σ)
  have hzero := (Fintype.linearIndependent_iff.mp hli')
    (fun j => ((Multiplicative.toAdd (f j) : ↥𝒪[K]) : K)) hL
  funext j
  have hcoe : ((Multiplicative.toAdd (f j) : ↥𝒪[K]) : K) = 0 := hzero j
  have : Multiplicative.toAdd (f j) = 0 := Subtype.ext hcoe
  simpa using congrArg Multiplicative.ofAdd this

/- Topological finiteness of the lattice's index. -/

/- Closed balls about the origin of nonzero radius are open: the ultrametric inequality
keeps the basic neighborhood of any member inside the ball. Deliberately duplicates the
private `isOpen_valuation_le` of `Atlas.Knowledge.UnitsFiniteIndexOpen` rather than
promoting it mid-phase. -/
private theorem isOpen_val_le {γ : ValueGroupWithZero L} (hγ : γ ≠ 0) :
    IsOpen {y : L | valuation L y ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  refine (IsValuativeTopology.hasBasis_nhds' x).mem_iff.mpr ⟨γ, hγ, fun y hy => ?_⟩
  calc valuation L y = valuation L ((y - x) + x) := by rw [sub_add_cancel]
  _ ≤ max (valuation L (y - x)) (valuation L x) := Valuation.map_add _ _ _
  _ ≤ γ := max_le (le_of_lt hy) hx

/- Ideal-power membership of an integer is the valuation bound, read off the image
characterization. -/
private theorem mem_idealPow_iff_val {ϖ : ↥𝒪[L]} (hϖ : Irreducible ϖ) (i : ℕ)
    (x : ↥𝒪[L]) : x ∈ (𝓂[L] ^ i : Ideal ↥𝒪[L]) ↔
      valuation L ((x : ↥𝒪[L]) : L) ≤ valuation L ((ϖ : L)) ^ i := by
  rw [← mem_idealPow_image_iff L hϖ i ((x : ↥𝒪[L]) : L)]
  constructor
  · exact fun hx => ⟨x, hx, rfl⟩
  · rintro ⟨m, hm, hmx⟩
    rwa [show m = x from Subtype.ext hmx] at hm

/- The embedding of the base is continuous: powers of one small base value are coinitial
in the extension's value group, so base balls map into arbitrarily deep balls. -/
omit [FiniteDimensional K L] [IsGalois K L] in
private theorem algebraMap_continuous : Continuous (algebraMap K L) := by
  refine continuous_of_continuousAt_zero (algebraMap K L) ?_
  rw [ContinuousAt, map_zero, (IsValuativeTopology.hasBasis_nhds_zero K).tendsto_iff
    (IsValuativeTopology.hasBasis_nhds_zero L)]
  rintro γ -
  obtain ⟨κ, hκ0, hκ1⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
  have hκL1 : valuation L (algebraMap K L κ) < 1 := by
    rw [← ValuativeExtension.mapValueGroupWithZero_valuation]
    have := ValuativeExtension.mapValueGroupWithZero_strictMono (A := K) (B := L) hκ1
    rwa [map_one] at this
  have hκL0 : valuation L (algebraMap K L κ) ≠ 0 := by
    simp only [Ne, Valuation.zero_iff]
    intro h0
    exact hκ0 (by simpa using (algebraMap K L).injective (by rw [h0, map_zero]) : κ = 0)
  obtain ⟨N, hN⟩ := exists_pow_le L (valuation L (algebraMap K L κ)) (γ : ValueGroupWithZero L)
    hκL1 hκL0 γ.ne_zero
  have hκN0 : valuation K (κ ^ N) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr (pow_ne_zero _ hκ0)
  refine ⟨Units.mk0 (valuation K (κ ^ N)) hκN0, trivial, fun a ha => ?_⟩
  have hlt : valuation L (algebraMap K L a) < valuation L (algebraMap K L (κ ^ N)) := by
    rw [← ValuativeExtension.mapValueGroupWithZero_valuation,
      ← ValuativeExtension.mapValueGroupWithZero_valuation]
    exact ValuativeExtension.mapValueGroupWithZero_strictMono ha
  calc valuation L (algebraMap K L a) < valuation L (algebraMap K L (κ ^ N)) := hlt
  _ = valuation L (algebraMap K L κ) ^ N := by rw [map_pow, map_pow]
  _ ≤ (γ : ValueGroupWithZero L) := hN

/- The analytic core: some valuation ball has integral coordinates along any basis. The
coordinate functionals are continuous by `LinearMap.continuous_of_finiteDimensional`
under the normed structures both fields carry compatibly with their topologies. -/
omit [IsGalois K L] in
private theorem exists_coord_integral_ball [NeZero (orderOf σ)]
    (bZ : Module.Basis (ZMod (orderOf σ)) K L)
    {ϖ : ↥𝒪[L]} (hϖ : Irreducible ϖ) :
    ∃ m : ℕ, ∀ y : L, valuation L y ≤ valuation L ((ϖ : L)) ^ m →
      ∀ j, valuation K (bZ.repr y j) ≤ 1 := by
  have hϖ0 : (ϖ : L) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  have hϖv0 : valuation L ((ϖ : L)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ0
  have hϖv1 : valuation L ((ϖ : L)) < 1 :=
    (Valuation.integer.integers (v := valuation L)).valuation_irreducible_lt_one hϖ
  haveI : ContinuousSMul K L :=
    continuousSMul_of_algebraMap K L (algebraMap_continuous (K := K) (L := L))
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : CompleteSpace K := inferInstance
  letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  haveI : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := L)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := L).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField L := Valued.toNontriviallyNormedField L (ValueGroupWithZero L)
  haveI : T2Space L := inferInstance
  have hcont : ∀ j : ZMod (orderOf σ), Continuous fun y : L => bZ.repr y j := fun j => by
    have h := (bZ.coord j).continuous_of_finiteDimensional
    have he : (fun y : L => bZ.repr y j) = ⇑(bZ.coord j) := by
      funext y
      rw [Module.Basis.coord_apply]
    rw [he]
    exact h
  have hV : {y : L | ∀ j, valuation K (bZ.repr y j) ≤ 1} ∈ nhds (0 : L) := by
    have hsub : {y : L | ∀ j, valuation K (bZ.repr y j) ≤ 1} =
        ⋂ j : ZMod (orderOf σ), (fun y : L => bZ.repr y j) ⁻¹' {c : K | valuation K c ≤ 1} := by
      ext y
      simp [Set.mem_iInter]
    rw [hsub]
    refine (Filter.iInter_mem).mpr fun j => ?_
    refine ContinuousAt.preimage_mem_nhds (hcont j).continuousAt ?_
    have h0 : bZ.repr (0 : L) j = 0 := by simp
    rw [h0]
    refine Filter.mem_of_superset
      ((IsValuativeTopology.hasBasis_nhds_zero K).mem_of_mem
        (i := Units.mk0 (1 : ValueGroupWithZero K) one_ne_zero) trivial) fun c hc => ?_
    simp only [Set.mem_setOf_eq] at hc ⊢
    exact le_of_lt hc
  obtain ⟨γ, -, hγsub⟩ := (IsValuativeTopology.hasBasis_nhds_zero L).mem_iff.mp hV
  obtain ⟨N, hN⟩ := exists_pow_le L (valuation L ((ϖ : L))) (γ : ValueGroupWithZero L)
    hϖv1 hϖv0 γ.ne_zero
  refine ⟨N + 1, fun y hy j => ?_⟩
  refine hγsub ?_ j
  change valuation L y < (γ : ValueGroupWithZero L)
  refine lt_of_le_of_lt hy (lt_of_lt_of_le ?_ hN)
  exact pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.mpr hϖv0) hϖv1 (Nat.lt_succ_self N)

/- The field value of an embedded lattice point: the coordinate combination of the orbit. -/
omit [TopologicalSpace K] [IsMixedCharLocalField K] [FiniteDimensional K L]
  [IsGalois K L] in
private theorem latticeHom_coe [NeZero (orderOf σ)] (i : ℕ)
    (W : (L ≃ₐ[K] L) → ↥(𝓂[L] ^ i : Ideal ↥𝒪[L])) (b' : L)
    (hval : ∀ g : L ≃ₐ[K] L, ((W g : ↥𝒪[L]) : L) = g b')
    (f : ZMod (orderOf σ) → Multiplicative ↥𝒪[K]) :
    ((↑(Multiplicative.toAdd (latticeHom σ i W f)) : ↥𝒪[L]) : L) =
      ∑ j : ZMod (orderOf σ),
        ((Multiplicative.toAdd (f j) : ↥𝒪[K]) : K) • gpow σ j b' := by
  change ((((∑ j : ZMod (orderOf σ),
      algebraMap ↥𝒪[K] ↥𝒪[L] (Multiplicative.toAdd (f j)) • W (gpow σ j)) :
      ↥(𝓂[L] ^ i : Ideal ↥𝒪[L])) : ↥𝒪[L]) : L) = _
  rw [AddSubmonoidClass.coe_finsetSum, AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [SetLike.val_smul, smul_eq_mul]
  push_cast
  rw [hval, Algebra.smul_def]

/- The lattice has finite index: a deep ball's integral coordinates put it inside the
range, so the range is an open subgroup of the compact ideal power and
`Subgroup.quotient_finite_of_isOpen` counts the quotient. -/
omit [IsGalois K L] in
private theorem latticeHom_range_quotient_finite [NeZero (orderOf σ)] (i : ℕ)
    (W : (L ≃ₐ[K] L) → ↥(𝓂[L] ^ i : Ideal ↥𝒪[L])) (b' : L)
    (hval : ∀ g : L ≃ₐ[K] L, ((W g : ↥𝒪[L]) : L) = g b')
    (bZ : Module.Basis (ZMod (orderOf σ)) K L)
    (hbZ : ∀ j, bZ j = gpow σ j b') :
    Finite (Multiplicative ↥(𝓂[L] ^ i : Ideal ↥𝒪[L]) ⧸ (latticeHom σ i W).range) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[L])
  have hϖ0 : (ϖ : L) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  have hϖv0 : valuation L ((ϖ : L)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ0
  have hϖv1 : valuation L ((ϖ : L)) ≤ 1 := (Valuation.mem_integer_iff _ _).mp ϖ.2
  obtain ⟨m, hm⟩ := exists_coord_integral_ball σ bZ hϖ
  have hr0 : valuation L ((ϖ : L)) ^ (max m i) ≠ 0 := pow_ne_zero _ hϖv0
  have hrm : valuation L ((ϖ : L)) ^ (max m i) ≤ valuation L ((ϖ : L)) ^ m :=
    pow_le_pow_right_of_le_one' hϖv1 (le_max_left m i)
  -- a small enough element is a lattice point: its coordinates are integral
  have hball : ∀ x : Multiplicative ↥(𝓂[L] ^ i : Ideal ↥𝒪[L]),
      valuation L ((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L) ≤
        valuation L ((ϖ : L)) ^ (max m i) →
      x ∈ (latticeHom σ i W).range := by
    intro x hx
    have hcoords : ∀ j, valuation K
        (bZ.repr ((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L) j) ≤ 1 :=
      hm _ (le_trans hx hrm)
    refine ⟨fun j => Multiplicative.ofAdd
      ⟨bZ.repr ((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L) j,
        (Valuation.mem_integer_iff _ _).mpr (hcoords j)⟩, ?_⟩
    refine Multiplicative.toAdd.injective (Subtype.ext (Subtype.ext ?_))
    rw [latticeHom_coe σ i W b' hval]
    simp only [toAdd_ofAdd]
    calc ∑ j : ZMod (orderOf σ),
        bZ.repr ((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L) j • gpow σ j b'
        = ∑ j : ZMod (orderOf σ),
          bZ.repr ((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L) j • bZ j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hbZ]
      _ = ((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L) := bZ.sum_repr _
  -- the range is open: it contains a ball around each of its points
  have hcval : Continuous fun z : Multiplicative ↥(𝓂[L] ^ i : Ideal ↥𝒪[L]) =>
      ((↑(Multiplicative.toAdd z) : ↥𝒪[L]) : L) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hopen : IsOpen ((latticeHom σ i W).range :
      Set (Multiplicative ↥(𝓂[L] ^ i : Ideal ↥𝒪[L]))) := by
    rw [isOpen_iff_mem_nhds]
    intro x hxmem
    have hLopen : IsOpen {w : L | valuation L
        (w - ((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L)) ≤ valuation L ((ϖ : L)) ^ (max m i)} := by
      have hsubc : Continuous fun w : L =>
          w - ((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L) := continuous_id.sub continuous_const
      exact (isOpen_val_le (L := L) hr0).preimage hsubc
    refine Filter.mem_of_superset (((hLopen.preimage hcval).mem_nhds ?_)) fun z hz => ?_
    · change valuation L (((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L) -
        ((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L)) ≤ valuation L ((ϖ : L)) ^ (max m i)
      rw [sub_self, map_zero]
      exact _root_.zero_le
    · have hzx : z / x ∈ (latticeHom σ i W).range := by
        refine hball (z / x) ?_
        have hval' : ((↑(Multiplicative.toAdd (z / x)) : ↥𝒪[L]) : L) =
            ((↑(Multiplicative.toAdd z) : ↥𝒪[L]) : L) -
              ((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L) := by
          rfl
        rw [hval']
        exact hz
      simpa using mul_mem hzx hxmem
  -- an open subgroup of the compact ideal has finite index
  have h𝓂open : IsOpen (((𝓂[L] ^ i : Ideal ↥𝒪[L]) : Set ↥𝒪[L])) := by
    have hset : (((𝓂[L] ^ i : Ideal ↥𝒪[L]) : Set ↥𝒪[L])) =
        (fun x : ↥𝒪[L] => (x : L)) ⁻¹'
          {w : L | valuation L w ≤ valuation L ((ϖ : L)) ^ i} := by
      ext x
      simpa using mem_idealPow_iff_val (L := L) hϖ i x
    rw [hset]
    exact (isOpen_val_le (L := L) (pow_ne_zero _ hϖv0)).preimage continuous_subtype_val
  have h𝓂closed : IsClosed (((𝓂[L] ^ i : Ideal ↥𝒪[L]) : Set ↥𝒪[L])) :=
    AddSubgroup.isClosed_of_isOpen (𝓂[L] ^ i : Ideal ↥𝒪[L]).toAddSubgroup h𝓂open
  haveI : CompactSpace ↥(𝓂[L] ^ i : Ideal ↥𝒪[L]) :=
    isCompact_iff_compactSpace.mp h𝓂closed.isCompact
  haveI : CompactSpace (Multiplicative ↥(𝓂[L] ^ i : Ideal ↥𝒪[L])) :=
    inferInstanceAs (CompactSpace ↥(𝓂[L] ^ i : Ideal ↥𝒪[L]))
  haveI : SeparatelyContinuousMul (Multiplicative ↥(𝓂[L] ^ i : Ideal ↥𝒪[L])) :=
    { continuous_const_mul := fun {a} => by
        have : Continuous fun z : ↥(𝓂[L] ^ i : Ideal ↥𝒪[L]) =>
            Multiplicative.toAdd a + z := continuous_const.add continuous_id
        exact this
      continuous_mul_const := fun {a} => by
        have : Continuous fun z : ↥(𝓂[L] ^ i : Ideal ↥𝒪[L]) =>
            z + Multiplicative.toAdd a := continuous_id.add continuous_const
        exact this }
  exact Subgroup.quotient_finite_of_isOpen _ hopen

/- The graded counts of the deep ideal power agree. -/

/- The multiplicative wrapper of the ideal action inherits the generator's order. -/
omit [IsGalois K L] in
private theorem galIdealPow_toMultiplicative_pow (i : ℕ) {n : ℕ} (hσn : σ ^ n = 1) :
    (AddEquiv.toMultiplicative (galIdealPow K L σ i)) ^ n = 1 := by
  have hvalpow : ∀ (k : ℕ) (x : Multiplicative ↥(𝓂[L] ^ i : Ideal ↥𝒪[L])),
      ((↑(Multiplicative.toAdd (((AddEquiv.toMultiplicative (galIdealPow K L σ i)) ^ k) x)) :
        ↥𝒪[L]) : L) = (σ ^ k) ((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L) := by
    intro k
    induction k with
    | zero => intro x; rfl
    | succ m ih =>
      intro x
      have h1 : ((AddEquiv.toMultiplicative (galIdealPow K L σ i)) ^ (m + 1)) x =
          ((AddEquiv.toMultiplicative (galIdealPow K L σ i)) ^ m)
            (AddEquiv.toMultiplicative (galIdealPow K L σ i) x) := by
        rw [pow_succ]
        rfl
      have h2 : (σ ^ (m + 1)) ((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L) =
          (σ ^ m) (σ ((↑(Multiplicative.toAdd x) : ↥𝒪[L]) : L)) := by
        rw [pow_succ]
        rfl
      rw [h1, ih, h2]
      rfl
  ext x
  rw [hvalpow n x, hσn]
  rfl

/- Serre's Corollary packaged: a stable finite-index subgroup with trivial graded counts
forces the ambient counts to be finite and equal. Stated over an opaque carrier. -/
private theorem finiteIndex_card_eq {A : Type*} [CommGroup A] {σA : A ≃* A} {n : ℕ}
    (hσ : σA ^ n = 1) (N : Subgroup A)
    (hN : ∀ x ∈ N, σA x ∈ N) (hN' : ∀ x ∈ N, σA.symm x ∈ N)
    [Finite (A ⧸ N)]
    (hc0 : Nat.card (H0 (stableRestrict σA N hN hN') n) = 1)
    (hc1 : Nat.card (H1 (stableRestrict σA N hN hN') n) = 1) :
    (Nat.card (H0 σA n) = Nat.card (H1 σA n)) ∧ Finite (H0 σA n) ∧ Finite (H1 σA n) := by
  haveI : Subsingleton (H0 (stableRestrict σA N hN hN') n) :=
    (Nat.card_eq_one_iff_unique.mp hc0).1
  haveI : Subsingleton (H1 (stableRestrict σA N hN hN') n) :=
    (Nat.card_eq_one_iff_unique.mp hc1).1
  haveI : Finite (H0 (stableRestrict σA N hN hN') n) := Finite.of_subsingleton
  haveI : Finite (H1 (stableRestrict σA N hN hN') n) := Finite.of_subsingleton
  have hexact : (QuotientGroup.mk' N).ker = N.subtype.range := by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  have hfinB := finite_of_exact (σA := stableRestrict σA N hN hN') (σB := σA)
    (σC := stableQuotient σA N hN hN') hσ (f := N.subtype) (g := QuotientGroup.mk' N)
    (fun x => rfl) (fun b => rfl) N.subtype_injective (QuotientGroup.mk'_surjective N) hexact
  haveI := hfinB.1
  haveI := hfinB.2
  have hid := card_identity_of_finiteIndex hσ N hN hN'
  rw [hc0, hc1] at hid
  exact ⟨by simpa using hid, hfinB.1, hfinB.2⟩

/- The counting theorem over handed-in data: the lattice's counts are the co-induced
module's, both `1`, and the finite index carries them to the ambient ideal power. -/
set_option maxHeartbeats 1600000 in
-- the instance chains of the concrete subtype carriers overrun the default budget
omit [IsGalois K L] in
private theorem card_pieces_idealPow [NeZero (orderOf σ)] (i : ℕ)
    (W : (L ≃ₐ[K] L) → ↥(𝓂[L] ^ i : Ideal ↥𝒪[L])) (b' : L)
    (hval : ∀ g : L ≃ₐ[K] L, ((W g : ↥𝒪[L]) : L) = g b')
    (hW : ∀ g, galIdealPow K L σ i (W g) = W (σ * g))
    (hli : LinearIndependent K fun g : L ≃ₐ[K] L => g b')
    (bZ : Module.Basis (ZMod (orderOf σ)) K L)
    (hbZ : ∀ j, bZ j = gpow σ j b') :
    Nat.card (H0 (AddEquiv.toMultiplicative (galIdealPow K L σ i)) (orderOf σ)) =
      Nat.card (H1 (AddEquiv.toMultiplicative (galIdealPow K L σ i)) (orderOf σ)) ∧
    Finite (H0 (AddEquiv.toMultiplicative (galIdealPow K L σ i)) (orderOf σ)) ∧
    Finite (H1 (AddEquiv.toMultiplicative (galIdealPow K L σ i)) (orderOf σ)) := by
  have hΛ : ∀ x ∈ (latticeHom σ i W).range,
      AddEquiv.toMultiplicative (galIdealPow K L σ i) x ∈ (latticeHom σ i W).range := by
    rintro x ⟨f, rfl⟩
    exact ⟨shiftAut (orderOf σ) f, (latticeHom_shift σ i W hW f).symm⟩
  have hΛ' : ∀ x ∈ (latticeHom σ i W).range,
      (AddEquiv.toMultiplicative (galIdealPow K L σ i)).symm x ∈ (latticeHom σ i W).range := by
    rintro x ⟨f, rfl⟩
    refine ⟨(shiftAut (orderOf σ)).symm f, ?_⟩
    apply (AddEquiv.toMultiplicative (galIdealPow K L σ i)).injective
    rw [latticeHom_shift σ i W hW, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  have hinj := latticeHom_injective σ i W b' hval hli
  have hbij : Function.Bijective (latticeHom σ i W).rangeRestrict :=
    ⟨fun a b h => hinj (congrArg Subtype.val h), (latticeHom σ i W).rangeRestrict_surjective⟩
  have he : ∀ f, (MulEquiv.ofBijective _ hbij) (shiftAut (orderOf σ) f) =
      stableRestrict (AddEquiv.toMultiplicative (galIdealPow K L σ i))
        (latticeHom σ i W).range hΛ hΛ' ((MulEquiv.ofBijective _ hbij) f) := by
    intro f
    refine Subtype.ext ?_
    change latticeHom σ i W (shiftAut (orderOf σ) f) =
      AddEquiv.toMultiplicative (galIdealPow K L σ i) (latticeHom σ i W f)
    exact (latticeHom_shift σ i W hW f).symm
  have hc0 : Nat.card (H0 (stableRestrict (AddEquiv.toMultiplicative (galIdealPow K L σ i))
      (latticeHom σ i W).range hΛ hΛ') (orderOf σ)) = 1 := by
    rw [← card_H0_congr (orderOf σ) (MulEquiv.ofBijective _ hbij) he]
    exact card_H0_shiftAut (orderOf σ)
  have hc1 : Nat.card (H1 (stableRestrict (AddEquiv.toMultiplicative (galIdealPow K L σ i))
      (latticeHom σ i W).range hΛ hΛ') (orderOf σ)) = 1 := by
    rw [← card_H1_congr (orderOf σ) (MulEquiv.ofBijective _ hbij) he]
    exact card_H1_shiftAut (orderOf σ)
  haveI : Finite (Multiplicative ↥(𝓂[L] ^ i : Ideal ↥𝒪[L]) ⧸ (latticeHom σ i W).range) :=
    latticeHom_range_quotient_finite σ i W b' hval bZ hbZ
  have hσAn := galIdealPow_toMultiplicative_pow σ i (pow_orderOf_eq_one σ)
  exact finiteIndex_card_eq hσAn (latticeHom σ i W).range hΛ hΛ' hc0 hc1

set_option maxHeartbeats 1600000 in
-- the instance chains of the concrete subtype carriers overrun the default budget
/-- **The graded counts of a deep ideal power agree and are finite**: at a generator of
the cyclic Galois group, the additive action of `Atlas.Knowledge.galIdealPow` on
`𝓂[L] ^ i` has `#Ĥ⁰ = #Ĥ¹`, both finite — the lattice computation of the class field
axiom ([Milne 2020, Chap. III, Lemma 2.3, p.104][MilneCFT];
[Yamaguchi 2026, `LocalClassFieldTheory/ClassFormation/NormalBasisCohomology.lean:33`]
[Yamaguchi2026]). -/
theorem galIdealPowCounts
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (i : ℕ) :
    (Nat.card (H0 (AddEquiv.toMultiplicative (galIdealPow K L σ i)) (orderOf σ)) =
      Nat.card (H1 (AddEquiv.toMultiplicative (galIdealPow K L σ i)) (orderOf σ))) ∧
    Finite (H0 (AddEquiv.toMultiplicative (galIdealPow K L σ i)) (orderOf σ)) ∧
    Finite (H1 (AddEquiv.toMultiplicative (galIdealPow K L σ i)) (orderOf σ)) := by
  classical
  haveI : Finite (L ≃ₐ[K] L) := inferInstance
  haveI : NeZero (orderOf σ) := ⟨(orderOf_pos σ).ne'⟩
  obtain ⟨c, hc0, hc⟩ := exists_scale_into_ideal K L i
    (Finset.image (fun g : L ≃ₐ[K] L => g (IsGalois.normalBasis K L 1)) Finset.univ)
  have himg : ∀ g : L ≃ₐ[K] L,
      g (algebraMap K L c * IsGalois.normalBasis K L 1) ∈
        ((↑) : ↥𝒪[L] → L) '' ((𝓂[L] ^ i : Ideal ↥𝒪[L]) : Set ↥𝒪[L]) := by
    intro g
    have hg : g (algebraMap K L c * IsGalois.normalBasis K L 1) =
        algebraMap K L c * g (IsGalois.normalBasis K L 1) := by
      rw [map_mul, AlgEquiv.commutes]
    rw [hg]
    exact hc _ (Finset.mem_image_of_mem _ (Finset.mem_univ g))
  choose Wfun hWmem hWcoe using fun g => himg g
  have hval : ∀ g : L ≃ₐ[K] L,
      (((⟨Wfun g, hWmem g⟩ : ↥(𝓂[L] ^ i : Ideal ↥𝒪[L])) : ↥𝒪[L]) : L) =
        g (algebraMap K L c * IsGalois.normalBasis K L 1) := fun g => hWcoe g
  have hW : ∀ g, galIdealPow K L σ i ⟨Wfun g, hWmem g⟩ = ⟨Wfun (σ * g), hWmem (σ * g)⟩ := by
    intro g
    refine Subtype.ext (Subtype.ext ?_)
    change σ ((Wfun g : ↥𝒪[L]) : L) = ((Wfun (σ * g) : ↥𝒪[L]) : L)
    rw [hWcoe, hWcoe]
    rfl
  have happ : ∀ g : L ≃ₐ[K] L,
      ((IsGalois.normalBasis K L).unitsSMul fun _ => Units.mk0 c hc0) g =
        g (algebraMap K L c * IsGalois.normalBasis K L 1) := by
    intro g
    rw [Module.Basis.unitsSMul_apply, IsGalois.normalBasis_apply, Units.smul_def,
      Units.val_mk0, Algebra.smul_def, map_mul, AlgEquiv.commutes]
  have hli : LinearIndependent K
      fun g : L ≃ₐ[K] L => g (algebraMap K L c * IsGalois.normalBasis K L 1) := by
    have h := ((IsGalois.normalBasis K L).unitsSMul fun _ => Units.mk0 c hc0).linearIndependent
    rwa [show ⇑((IsGalois.normalBasis K L).unitsSMul fun _ => Units.mk0 c hc0) =
      fun g : L ≃ₐ[K] L => g (algebraMap K L c * IsGalois.normalBasis K L 1)
      from funext happ] at h
  have hbij := gpow_bijective σ hgen
  have hbZ : ∀ j, (((IsGalois.normalBasis K L).unitsSMul fun _ => Units.mk0 c hc0).reindex
      (Equiv.ofBijective (gpow σ) hbij).symm) j =
        gpow σ j (algebraMap K L c * IsGalois.normalBasis K L 1) := by
    intro j
    rw [Module.Basis.reindex_apply, Equiv.symm_symm, Equiv.ofBijective_apply, happ]
  exact card_pieces_idealPow σ i (fun g => ⟨Wfun g, hWmem g⟩) _ hval hW hli _ hbZ

end OrbitLattice

end Atlas.Knowledge
