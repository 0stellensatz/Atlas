import Mathlib
import Atlas.Knowledge.GalIdealPowCounts
import Atlas.Knowledge.GalUnits
import Atlas.Knowledge.NormalizedValuationAlgEquiv
import Atlas.Knowledge.PadicExpEquivariant
import Atlas.Knowledge.UnitLevelFiniteIndex

/-!
# norm index of a cyclic extension

The class field axiom for mixed-characteristic local fields: a cyclic extension `L/K` has
norm index the degree, `#(Kˣ ⧸ N_{L/K} Lˣ) = [L : K]`. This is Milne's computation
`h(Lˣ) = h(U_L) · h(ℤ) = n` read through the layer's staged pieces: the deep unit level
carries the ideal power's equal counts across the exponential, the finite index of the
level carries them to the valuation-one units, the valuation's exact sequence multiplies
in the counts of the trivial `ℤ`-module, and Hilbert 90 with the fixed-point
identification converts the surviving `Ĥ⁰`-count into the norm index.

## Main statements

* `normIndexCyclic` — for `σ` generating the Galois group of a cyclic extension `L/K`,
  `#(Kˣ ⧸ (Units.map (Algebra.norm K)).range) = [L : K]`; proved.

## Implementation notes

The sequence count `card_of_exact_with_int` (along `1 → A → B → ℤ → 1`) is packaged over
opaque carriers, because instantiating
`Atlas.Knowledge.HerbrandQuotient.finite_of_exact` directly at the concrete subtype
carriers deadlocks the elaborator's postponed unification; the generic statement
elaborates in the toolkit's own context and its instantiation is a plain application.
The finite-index climb and the trivial-`ℤ` counts are the toolkit's own
`Atlas.Knowledge.HerbrandQuotient.card_H0_eq_card_H1_of_finiteIndex` and
`Atlas.Knowledge.HerbrandQuotient.card_H0_int` / `card_H1_int`. Finiteness rides every
cardinality transport through `Nat.finite_of_card_ne_zero`: the graded pieces are groups,
hence nonempty, so equal `Nat.card` moves `Finite` without an equivalence.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

open HerbrandQuotient

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] [IsMixedCharLocalField L] [IsGalois K L]

variable {K L}

/- A deep level always exists: the residue characteristic is at least two. -/
private theorem exists_deep_level :
    ∃ i : ℕ+, absoluteRamificationIndex L < (residueCharacteristic L - 1) * (i : ℕ) := by
  have hp : 2 ≤ residueCharacteristic L := (residueCharacteristic_prime L).two_le
  refine ⟨⟨absoluteRamificationIndex L + 1, Nat.succ_pos _⟩, ?_⟩
  have h1 : 1 ≤ residueCharacteristic L - 1 := by omega
  calc absoluteRamificationIndex L < absoluteRamificationIndex L + 1 := Nat.lt_succ_self _
  _ = 1 * (absoluteRamificationIndex L + 1) := (one_mul _).symm
  _ ≤ (residueCharacteristic L - 1) * (absoluteRamificationIndex L + 1) :=
      Nat.mul_le_mul_right _ h1

/- The unit action inherits the generator's order. -/
omit [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K] [ValuativeRel L]
  [TopologicalSpace L] [ValuativeExtension K L] [FiniteDimensional K L]
  [IsMixedCharLocalField L] [IsGalois K L] in
private theorem galUnits_pow_orderOf (σ : L ≃ₐ[K] L) :
    galUnits (K := K) σ ^ orderOf σ = 1 := by
  ext u
  have h1 := galUnits_pow_coe σ (orderOf σ) u
  rw [pow_orderOf_eq_one] at h1
  have h2 : ((galUnits σ ^ orderOf σ) u : L) = (u : L) := h1
  exact congrArg Units.val (Units.ext h2)

/- Step 1: a deep unit level has equal finite graded counts, through the exponential. -/
private theorem card_units_level (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) (i : ℕ+)
    (hi : absoluteRamificationIndex L < (residueCharacteristic L - 1) * (i : ℕ))
    (hst : ∀ u ∈ higherUnitGroup L i, galUnits (K := K) σ u ∈ higherUnitGroup L i)
    (hst' : ∀ u ∈ higherUnitGroup L i,
      (galUnits (K := K) σ).symm u ∈ higherUnitGroup L i) :
    (Nat.card (H0 (stableRestrict (galUnits σ) (higherUnitGroup L i) hst hst')
        (orderOf σ)) =
      Nat.card (H1 (stableRestrict (galUnits σ) (higherUnitGroup L i) hst hst')
        (orderOf σ))) ∧
    Finite (H0 (stableRestrict (galUnits σ) (higherUnitGroup L i) hst hst') (orderOf σ)) ∧
    Finite (H1 (stableRestrict (galUnits σ) (higherUnitGroup L i) hst hst') (orderOf σ)) := by
  obtain ⟨heq, hf0, hf1⟩ := galIdealPowCounts σ hgen (i : ℕ)
  haveI := hf0
  haveI := hf1
  have he : ∀ m, expLevel L i hi
      ((AddEquiv.toMultiplicative (galIdealPow K L σ (i : ℕ))) m) =
      stableRestrict (galUnits σ) (higherUnitGroup L i) hst hst' (expLevel L i hi m) :=
    fun m => (expLevel_intertwines K L σ i hi m).symm
  have h0 := card_H0_congr (orderOf σ) (expLevel L i hi) he
  have h1 := card_H1_congr (orderOf σ) (expLevel L i hi) he
  refine ⟨by rw [← h0, ← h1]; exact heq, ?_, ?_⟩
  · exact Nat.finite_of_card_ne_zero (by rw [← h0]; exact Nat.card_pos.ne')
  · exact Nat.finite_of_card_ne_zero (by rw [← h1]; exact Nat.card_pos.ne')

/- Step 2: the valuation-one units have equal finite graded counts — the level's counts
climb the finite index. -/
private theorem card_units_ker (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (hk : ∀ u ∈ (normalizedValuationHom L).ker,
      galUnits (K := K) σ u ∈ (normalizedValuationHom L).ker)
    (hk' : ∀ u ∈ (normalizedValuationHom L).ker,
      (galUnits (K := K) σ).symm u ∈ (normalizedValuationHom L).ker) :
    (Nat.card (H0 (stableRestrict (galUnits σ) (normalizedValuationHom L).ker hk hk')
        (orderOf σ)) =
      Nat.card (H1 (stableRestrict (galUnits σ) (normalizedValuationHom L).ker hk hk')
        (orderOf σ))) ∧
    Finite (H0 (stableRestrict (galUnits σ) (normalizedValuationHom L).ker hk hk')
      (orderOf σ)) ∧
    Finite (H1 (stableRestrict (galUnits σ) (normalizedValuationHom L).ker hk hk')
      (orderOf σ)) := by
  obtain ⟨i, hi⟩ := exists_deep_level (L := L)
  have hle := higherUnitGroup_le_ker L i
  have hst : ∀ u ∈ higherUnitGroup L i, galUnits (K := K) σ u ∈ higherUnitGroup L i :=
    fun u hu => galUnits_mem_higherUnitGroup K L σ i hu
  have hst' : ∀ u ∈ higherUnitGroup L i,
      (galUnits (K := K) σ).symm u ∈ higherUnitGroup L i :=
    fun u hu => galUnits_mem_higherUnitGroup K L σ.symm i hu
  have hNstab : ∀ x ∈ (higherUnitGroup L i).subgroupOf (normalizedValuationHom L).ker,
      stableRestrict (galUnits σ) (normalizedValuationHom L).ker hk hk' x ∈
        (higherUnitGroup L i).subgroupOf (normalizedValuationHom L).ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact galUnits_mem_higherUnitGroup K L σ i hx
  have hNstab' : ∀ x ∈ (higherUnitGroup L i).subgroupOf (normalizedValuationHom L).ker,
      (stableRestrict (galUnits σ) (normalizedValuationHom L).ker hk hk').symm x ∈
        (higherUnitGroup L i).subgroupOf (normalizedValuationHom L).ker := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact galUnits_mem_higherUnitGroup K L σ.symm i hx
  obtain ⟨hUeq, hUf0, hUf1⟩ := card_units_level σ hgen i hi hst hst'
  haveI := hUf0
  haveI := hUf1
  have he' : ∀ x : ↥((higherUnitGroup L i).subgroupOf (normalizedValuationHom L).ker),
      Subgroup.subgroupOfEquivOfLe hle
        (stableRestrict (stableRestrict (galUnits σ) (normalizedValuationHom L).ker hk hk')
          ((higherUnitGroup L i).subgroupOf (normalizedValuationHom L).ker)
          hNstab hNstab' x) =
      stableRestrict (galUnits σ) (higherUnitGroup L i) hst hst'
        (Subgroup.subgroupOfEquivOfLe hle x) := by
    intro x
    refine Subtype.ext ?_
    rfl
  have h0 := card_H0_congr (orderOf σ) (Subgroup.subgroupOfEquivOfLe hle) he'
  have h1 := card_H1_congr (orderOf σ) (Subgroup.subgroupOfEquivOfLe hle) he'
  haveI : Finite (H0 (stableRestrict
      (stableRestrict (galUnits σ) (normalizedValuationHom L).ker hk hk')
      ((higherUnitGroup L i).subgroupOf (normalizedValuationHom L).ker) hNstab hNstab')
      (orderOf σ)) :=
    Nat.finite_of_card_ne_zero (by rw [h0]; exact Nat.card_pos.ne')
  haveI : Finite (H1 (stableRestrict
      (stableRestrict (galUnits σ) (normalizedValuationHom L).ker hk hk')
      ((higherUnitGroup L i).subgroupOf (normalizedValuationHom L).ker) hNstab hNstab')
      (orderOf σ)) :=
    Nat.finite_of_card_ne_zero (by rw [h1]; exact Nat.card_pos.ne')
  haveI := unitLevelFiniteIndex L i
  exact card_H0_eq_card_H1_of_finiteIndex
    (stableRestrict_pow (galUnits σ) (galUnits_pow_orderOf σ)
      (normalizedValuationHom L).ker hk hk')
    ((higherUnitGroup L i).subgroupOf (normalizedValuationHom L).ker) hNstab hNstab'
    (by rw [h0, h1]; exact hUeq)

section ExactWithInt

variable {A B : Type*} [CommGroup A] [CommGroup B]

/- The count along `1 → A → B → ℤ → 1` with equal counts upstairs and trivial `Ĥ¹`
downstairs: `#Ĥ⁰(B) = n`. Stated over opaque carriers. -/
private theorem card_of_exact_with_int
    {σA : A ≃* A} {σB : B ≃* B} {n : ℕ}
    (hσA : σA ^ n = 1) (hσB : σB ^ n = 1) (hn : n ≠ 0)
    {f : A →* B} {g : B →* Multiplicative ℤ}
    (hf : ∀ a, f (σA a) = σB (f a)) (hg : ∀ b, g (σB b) = g b)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g)
    (hexact : g.ker = f.range)
    [Finite (H0 σA n)] [Finite (H1 σA n)]
    (hAeq : Nat.card (H0 σA n) = Nat.card (H1 σA n))
    (h1B : Nat.card (H1 σB n) = 1) :
    Nat.card (H0 σB n) = n := by
  haveI : Finite (H0 (MulEquiv.refl (Multiplicative ℤ)) n) :=
    Nat.finite_of_card_ne_zero (by rw [card_H0_int]; exact hn)
  haveI : Finite (H1 (MulEquiv.refl (Multiplicative ℤ)) n) :=
    Nat.finite_of_card_ne_zero (by rw [card_H1_int n hn]; exact one_ne_zero)
  have hg' : ∀ b, g (σB b) = (MulEquiv.refl (Multiplicative ℤ)) (g b) := fun b => hg b
  have hfinB := finite_of_exact (σA := σA) (σB := σB)
    (σC := MulEquiv.refl (Multiplicative ℤ)) hσB
    (f := f) (g := g) hf hg' hinj hsurj hexact
  haveI := hfinB.1
  haveI := hfinB.2
  have hcard := card_identity_of_exact (σA := σA) (σB := σB)
    (σC := MulEquiv.refl (Multiplicative ℤ)) hσA hσB
    (f := f) (g := g) hf hg' hinj hsurj hexact
  rw [card_H1_int n hn, card_H0_int n, hAeq, h1B, mul_one, mul_one] at hcard
  have hpos : 0 < Nat.card (H1 σA n) := Nat.card_pos
  rw [mul_comm (Nat.card (H1 σA n)) n] at hcard
  exact Nat.eq_of_mul_eq_mul_right hpos hcard

end ExactWithInt

/-- **The norm index of a cyclic extension is its degree** — the class field axiom of
local class field theory, at a generator of the Galois group:
`h(Lˣ) = h(U_L) · h(ℤ) = n` with `Ĥ¹(Lˣ)` trivial, so `#Ĥ⁰(Lˣ) = #(Kˣ ⧸ N Lˣ) = n`
([Milne 2020, Chap. III, Lemma 2.5, pp.104–105][MilneCFT];
[Yamaguchi 2026, `LocalClassFieldTheory/ClassFormation/Main.lean:92`, stated there as the
Tate-cohomology count][Yamaguchi2026]). -/
theorem normIndexCyclic (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) :
    Nat.card (Kˣ ⧸ (Units.map (Algebra.norm K : L →* K)).range) = Module.finrank K L := by
  haveI : NeZero (orderOf σ) := ⟨(orderOf_pos σ).ne'⟩
  have hval : ∀ (τ : L ≃ₐ[K] L) (u : Lˣ),
      normalizedValuationHom L (galUnits (K := K) τ u) = normalizedValuationHom L u := by
    intro τ u
    have h := normalizedValuation_algEquiv (K := K) (L := L) τ u
    have heq : Units.map ((τ : L ≃ₐ[K] L) : L →* L) u = galUnits (K := K) τ u :=
      Units.ext rfl
    calc normalizedValuationHom L (galUnits (K := K) τ u)
        = Multiplicative.ofAdd (normalizedValuation L (galUnits (K := K) τ u)) := rfl
    _ = Multiplicative.ofAdd (normalizedValuation L u) := by rw [← heq, h]
    _ = normalizedValuationHom L u := rfl
  have hsymm : (galUnits (K := K) σ).symm = galUnits (K := K) σ.symm := rfl
  have hk : ∀ u ∈ (normalizedValuationHom L).ker,
      galUnits (K := K) σ u ∈ (normalizedValuationHom L).ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [hval σ u]
    exact hu
  have hk' : ∀ u ∈ (normalizedValuationHom L).ker,
      (galUnits (K := K) σ).symm u ∈ (normalizedValuationHom L).ker := by
    intro u hu
    rw [MonoidHom.mem_ker] at hu ⊢
    rw [hsymm, hval σ.symm u]
    exact hu
  obtain ⟨hKeq, hKf0, hKf1⟩ := card_units_ker σ hgen hk hk'
  haveI := hKf0
  haveI := hKf1
  have hσBn := galUnits_pow_orderOf (K := K) σ
  have hσAn := stableRestrict_pow (galUnits σ) hσBn (normalizedValuationHom L).ker hk hk'
  have hsurj : Function.Surjective (normalizedValuationHom L) := by
    intro z
    obtain ⟨x, hx⟩ := normalizedValuation_surjective L (Multiplicative.toAdd z)
    refine ⟨x, ?_⟩
    calc normalizedValuationHom L x
        = Multiplicative.ofAdd (normalizedValuation L x) := rfl
    _ = Multiplicative.ofAdd (Multiplicative.toAdd z) := by rw [hx]
    _ = z := by simp
  have hexact : (normalizedValuationHom L).ker =
      ((normalizedValuationHom L).ker.subtype).range := (Subgroup.range_subtype _).symm
  have hcount := card_of_exact_with_int hσAn hσBn (NeZero.ne (orderOf σ))
    (f := ((normalizedValuationHom L).ker).subtype) (g := normalizedValuationHom L)
    (fun x => rfl) (fun b => hval σ b)
    (Subgroup.subtype_injective _) hsurj hexact hKeq (card_H1_galUnits σ hgen)
  rw [card_H0_galUnits σ hgen] at hcount
  rw [hcount]
  have htop : Subgroup.zpowers σ = ⊤ := (Subgroup.eq_top_iff' _).mpr hgen
  have hcard := Nat.card_zpowers σ
  rw [htop, Subgroup.card_top] at hcard
  rw [← hcard]
  exact IsGalois.card_aut_eq_finrank K L

end Atlas.Knowledge
