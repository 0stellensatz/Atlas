import Mathlib
import Atlas.Knowledge.HerbrandQuotient
import Atlas.Knowledge.HilbertNinety

/-!
# the unit action of a cyclic Galois group, and its graded pieces

The action of a finite cyclic Galois group on the units of the extension, at a chosen
generator, read into the Herbrand vocabulary of `Atlas.Knowledge.herbrandQuotient`: the
Herbrand norm at the generator is the field norm, the odd graded piece is trivial — Hilbert
90 — and the even graded piece counts the norm quotient `Kˣ ⧸ N Lˣ` of the base, through
the explicit identification of the difference kernel with the base units. These are the two
outer readings the class field axiom's norm-index count consumes: with them, the counted
hexagon along the valuation sequence turns `#Ĥ⁰(Lˣ)` into the norm index itself.

## Main definitions

* `galUnits` — the unit-level action of a Galois element.
* `baseUnitsToKerDiff` — the base units inside the difference kernel.

## Main statements

* `herbrandNorm_galUnits` — the Herbrand norm at a generator is the field norm; proved.
* `galUnits_ker_norm_le_range_diff` — `Ĥ¹` of the unit action is trivial: Hilbert 90 in the
  graded vocabulary; proved.
* `card_H0_galUnits` — `#Ĥ⁰` of the unit action is the norm index `#(Kˣ ⧸ N Lˣ)`; proved.

## Implementation notes

The generator is carried as an element with the generation hypothesis, and the graded
pieces are taken at `n = orderOf σ` — the reading under which
`Atlas.Knowledge.HerbrandQuotient.H0` is Serre's `A^G/NA`, since the powers below the order
enumerate the group (`Atlas.Knowledge.prod_pow_apply_eq_norm`). The surjectivity of the
base-units map is where Galois theory enters: a unit fixed by the generator is fixed by
everything, hence lies in the bottom intermediate field. The `Ĥ⁰` count is stated as a
`Nat.card` equality rather than a bundled isomorphism: the consumer is a counting argument,
and the isomorphism it rides is rebuilt inside the proof from `QuotientGroup.congr`.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsGalois K L]

section UnitsBridge


/-- The **unit-level action** of a Galois element: `σ` on `Lˣ`
([Serre 1979, Chap. X, §1, p.150][Serre1979]). -/
noncomputable def galUnits (σ : L ≃ₐ[K] L) : Lˣ ≃* Lˣ :=
  Units.mapEquiv σ.toMulEquiv

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The unit action, pointwise. -/
theorem galUnits_coe (σ : L ≃ₐ[K] L) (u : Lˣ) :
    ((galUnits σ u : Lˣ) : L) = σ (u : L) := rfl

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The unit action's powers, pointwise. -/
theorem galUnits_pow_coe (σ : L ≃ₐ[K] L) (i : ℕ) :
    ∀ u : Lˣ, (((galUnits σ ^ i) u : Lˣ) : L) = (σ ^ i) (u : L) := by
  induction i with
  | zero => intro u; rfl
  | succ m ih =>
    intro u
    have h1 : (galUnits σ ^ (m + 1)) u = (galUnits σ ^ m) (galUnits σ u) := by
      rw [pow_succ]
      rfl
    have h2 : (σ ^ (m + 1)) (u : L) = (σ ^ m) (σ (u : L)) := by
      rw [pow_succ]
      rfl
    rw [h1, h2, ih (galUnits σ u), galUnits_coe]

/-- The Herbrand norm of the unit action is the field norm on units — the bridge between
`Atlas.Knowledge.HerbrandQuotient.norm` at a generator and `Algebra.norm`
([Serre 1979, Chap. X, §1, p.150][Serre1979]). -/
theorem herbrandNorm_galUnits (σ : L ≃ₐ[K] L) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) (u : Lˣ) :
    ((HerbrandQuotient.norm (galUnits σ) (orderOf σ) u : Lˣ) : L) =
      algebraMap K L (Algebra.norm K (u : L)) := by
  rw [Algebra.norm_eq_prod_automorphisms]
  have hcoe : ((HerbrandQuotient.norm (galUnits σ) (orderOf σ) u : Lˣ) : L) =
      ∏ i ∈ Finset.range (orderOf σ), (σ ^ i) (u : L) := by
    rw [HerbrandQuotient.norm_apply]
    rw [show ((∏ i ∈ Finset.range (orderOf σ), ((galUnits σ ^ i) u) : Lˣ) : L) =
      ∏ i ∈ Finset.range (orderOf σ), (((galUnits σ ^ i) u : Lˣ) : L) from
        map_prod (Units.coeHom L) _ _]
    exact Finset.prod_congr rfl fun i _ => galUnits_pow_coe σ i u
  rw [hcoe]
  -- the powers of a generator enumerate the group
  have hfin : IsOfFinOrder σ := isOfFinOrder_of_finite σ
  have hbij : Function.Bijective (fun i : Fin (orderOf σ) => σ ^ (i : ℕ)) := by
    constructor
    · intro i j hij
      exact Fin.ext (pow_injOn_Iio_orderOf (Set.mem_Iio.mpr i.2) (Set.mem_Iio.mpr j.2) hij)
    · intro τ
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
      have hpos : 0 < (orderOf σ : ℤ) := by
        exact_mod_cast hfin.orderOf_pos
      set m := (k % (orderOf σ : ℤ)).toNat with hm
      have hmlt : m < orderOf σ := by
        have h1 : k % (orderOf σ : ℤ) < (orderOf σ : ℤ) := Int.emod_lt_of_pos k hpos
        have h2 : 0 ≤ k % (orderOf σ : ℤ) := Int.emod_nonneg k hpos.ne'
        omega
      refine ⟨⟨m, hmlt⟩, ?_⟩
      have h3 : σ ^ (m : ℕ) = σ ^ ((m : ℕ) : ℤ) := (zpow_natCast σ m).symm
      have h4 : ((m : ℕ) : ℤ) = k % (orderOf σ : ℤ) := by
        rw [hm]
        exact Int.toNat_of_nonneg (Int.emod_nonneg k hpos.ne')
      calc σ ^ (m : ℕ) = σ ^ (k % (orderOf σ : ℤ)) := by rw [h3, h4]
        _ = σ ^ k := zpow_mod_orderOf σ k
        _ = τ := hk
  let e : Fin (orderOf σ) ≃ (L ≃ₐ[K] L) := Equiv.ofBijective _ hbij
  rw [← Fin.prod_univ_eq_prod_range (fun i => (σ ^ i) (u : L)) (orderOf σ)]
  exact Fintype.prod_equiv e (fun i => (σ ^ (i : ℕ)) (u : L)) (fun τ => τ (u : L))
    (fun i => rfl)

/-- **Hilbert 90 in the graded vocabulary**: on the unit action of a generator, the norm
kernel lies inside the difference range — `Ĥ¹ (Lˣ)` of
`Atlas.Knowledge.HerbrandQuotient.H1` is trivial
([Serre 1979, Chap. X, §1, Prop. 2, p.150, and Cor., p.151][Serre1979];
[Yamaguchi 2026, `LocalClassFieldTheory/ClassFormation/Hilbert90.lean:17`]
[Yamaguchi2026]). -/
theorem galUnits_ker_norm_le_range_diff (σ : L ≃ₐ[K] L) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    (HerbrandQuotient.norm (galUnits σ) (orderOf σ)).ker ≤
      (HerbrandQuotient.diff (galUnits σ)).range := by
  intro u hu
  rw [MonoidHom.mem_ker] at hu
  have hnorm1 : Algebra.norm K (u : L) = 1 := by
    have h1 := herbrandNorm_galUnits σ hgen u
    rw [hu] at h1
    refine (algebraMap K L).injective ?_
    rw [map_one]
    exact h1.symm
  obtain ⟨y, hy⟩ := hilbertNinety hgen hnorm1
  refine ⟨y⁻¹, ?_⟩
  ext
  rw [HerbrandQuotient.diff_apply, Units.val_mul, inv_inv,
    show ((galUnits σ y⁻¹ : Lˣ) : L) = σ ((y⁻¹ : Lˣ) : L) from rfl,
    Units.val_inv_eq_inv_val, map_inv₀]
  rw [div_eq_mul_inv] at hy
  rw [← hy]
  ring

end UnitsBridge

section FixedPoints

/-- The unit image of the base field, as a homomorphism into the difference kernel of the
unit action ([Serre 1979, Chap. VIII, §4, p.133][Serre1979]). -/
noncomputable def baseUnitsToKerDiff (σ : L ≃ₐ[K] L) :
    Kˣ →* (HerbrandQuotient.diff (galUnits σ)).ker :=
  MonoidHom.codRestrict (Units.map (algebraMap K L : K →* L)) _ (by
    intro x
    rw [MonoidHom.mem_ker]
    ext
    rw [HerbrandQuotient.diff_apply, Units.val_mul, Units.val_inv_eq_inv_val]
    have h1 : ((galUnits σ (Units.map (algebraMap K L : K →* L) x) : Lˣ) : L) =
        σ (algebraMap K L (x : K)) := rfl
    rw [h1, σ.commutes]
    have h2 : ((Units.map (algebraMap K L : K →* L) x : Lˣ) : L) = algebraMap K L (x : K) :=
      rfl
    rw [h2, Units.val_one]
    exact mul_inv_cancel₀ ((map_ne_zero _).mpr (Units.ne_zero x)))

omit [FiniteDimensional K L] in
/-- The base units embed. -/
theorem baseUnitsToKerDiff_injective (σ : L ≃ₐ[K] L) :
    Function.Injective (baseUnitsToKerDiff (K := K) (L := L) σ) := by
  intro a b hab
  have h1 : Units.map (algebraMap K L : K →* L) a = Units.map (algebraMap K L : K →* L) b :=
    congrArg Subtype.val hab
  ext
  exact (algebraMap K L).injective (by
    have := congrArg Units.val h1
    simpa using this)

/-- At a generator, every unit fixed by the action comes from the base: the fixed field of
the whole group is the bottom ([Serre 1979, Chap. VIII, §4, p.133][Serre1979]). -/
theorem baseUnitsToKerDiff_surjective (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Function.Surjective (baseUnitsToKerDiff (K := K) (L := L) σ) := by
  rintro ⟨u, hu⟩
  rw [MonoidHom.mem_ker] at hu
  -- the unit is fixed by the generator, hence by everything, hence lies in the base
  have hfix : σ (u : L) = (u : L) := by
    have h1 := congrArg (fun w : Lˣ => (w : L) * (u : L)) hu
    simpa [HerbrandQuotient.diff_apply, galUnits] using h1
  have hfixall : ∀ τ : L ≃ₐ[K] L, τ (u : L) = (u : L) := by
    intro τ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen τ)
    subst hk
    induction k using Int.induction_on with
    | zero => rfl
    | succ m ih =>
      rw [zpow_add_one]
      change (σ ^ (m : ℤ)) (σ (u : L)) = (u : L)
      rw [hfix]
      exact ih
    | pred m ih =>
      rw [zpow_sub_one]
      have hinv : σ⁻¹ (u : L) = (u : L) := by
        have := congrArg (⇑σ⁻¹) hfix
        rw [show σ⁻¹ (σ (u : L)) = (u : L) from σ.symm_apply_apply (u : L)] at this
        exact this.symm
      change (σ ^ (-(m : ℤ))) (σ⁻¹ (u : L)) = (u : L)
      rw [hinv]
      exact ih
  have hbot : (u : L) ∈ (⊥ : IntermediateField K L) :=
    (IsGalois.mem_bot_iff_fixed (u : L)).mpr hfixall
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.mp hbot
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [map_zero] at hk
    exact (Units.ne_zero u) hk.symm
  refine ⟨Units.mk0 k hk0, ?_⟩
  refine Subtype.ext (Units.ext ?_)
  exact hk


/-- The Herbrand norm range corresponds to the unit-norm range under the base-units
identification ([Serre 1979, Chap. VIII, §4, p.133][Serre1979]). -/
theorem baseUnitsToKerDiff_map_norm_range (σ : L ≃ₐ[K] L)
    (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    ((Units.map (Algebra.norm K : L →* K)).range).map
        (baseUnitsToKerDiff (K := K) (L := L) σ) =
      (HerbrandQuotient.norm (galUnits σ) (orderOf σ)).range.subgroupOf
        (HerbrandQuotient.diff (galUnits σ)).ker := by
  ext z
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨w, ?_⟩
    ext
    rw [herbrandNorm_galUnits σ hgen w]
    rfl
  · rintro ⟨w, hw⟩
    refine ⟨Units.map (Algebra.norm K : L →* K) w, ⟨w, rfl⟩, ?_⟩
    refine Subtype.ext (Units.ext ?_)
    have h1 := herbrandNorm_galUnits σ hgen w
    rw [hw] at h1
    exact h1.symm

/-- **`Ĥ⁰` of the unit action counts the norm quotient of the base**:
`#Ĥ⁰(Gal, Lˣ) = #(Kˣ ⧸ N Lˣ)`, through the explicit isomorphism of the difference kernel
with `Kˣ` matching the norm parts
([Serre 1979, Chap. VIII, §4, p.133][Serre1979];
[Yamaguchi 2026, `LocalClassFieldTheory/ClassFormation/Main.lean:92`, the `Ĥ⁰` half]
[Yamaguchi2026]). -/
theorem card_H0_galUnits (σ : L ≃ₐ[K] L) (hgen : ∀ τ, τ ∈ Subgroup.zpowers σ) :
    Nat.card (HerbrandQuotient.H0 (galUnits σ) (orderOf σ)) =
      Nat.card (Kˣ ⧸ (Units.map (Algebra.norm K : L →* K)).range) := by
  have hbij : Function.Bijective (baseUnitsToKerDiff (K := K) (L := L) σ) :=
    ⟨baseUnitsToKerDiff_injective σ, baseUnitsToKerDiff_surjective σ hgen⟩
  refine (Nat.card_congr (QuotientGroup.congr _ _
    (MulEquiv.ofBijective _ hbij) ?_).toEquiv).symm
  rw [show ((MulEquiv.ofBijective _ hbij : Kˣ ≃* _) :
    Kˣ →* (HerbrandQuotient.diff (galUnits σ)).ker) =
    baseUnitsToKerDiff (K := K) (L := L) σ from MonoidHom.ext fun x => rfl]
  exact baseUnitsToKerDiff_map_norm_range σ hgen

end FixedPoints


end Atlas.Knowledge
