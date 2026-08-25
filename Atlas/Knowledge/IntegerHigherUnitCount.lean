import Mathlib
import Atlas.Knowledge.StandardLubinTateGaloisDescription

/-!
# integer higher unit count

The unit-parameter count of the level filtration: the quotient of the integer units by
the `m`-th higher unit group `1 + 𝔪^m` is the unit group of `𝒪/𝔪^m`, of cardinality
`(q − 1) · q ^ (m − 1)`. The computation is the graded filtration read off in one pass —
`𝒪/𝔪^m` has `q ^ m` elements because each step of the tower is a residue-field's worth,
by multiplication with `π ^ m`; the units of that finite local ring are the complement of
its maximal ideal; and the reduction of units is surjective with kernel exactly `1 + 𝔪^m`.
This is the group the Galois description of the standard level fields counts against.

## Main definitions

* `integerHigherUnitGroupQuotientEquiv` — `𝒪ˣ/U^(m) ≃* (𝒪/𝔪^m)ˣ`.

## Main statements

* `card_quotient_maximalIdeal_pow` — `|A/𝔪^m| = q^m` for a discrete valuation ring;
  proved.
* `card_units_quotient_maximalIdeal_pow` — `|(A/𝔪^m)ˣ| = (q − 1) · q^(m−1)`; proved.
* `integerHigherUnitCount` — `|𝒪[K]ˣ/U^(m)| = (q − 1) · q^(m−1)`; proved.
* `finite_integerHigherUnitGroup_quotient` — the quotient is finite; proved.

## Implementation notes

The ring-side count needs no finiteness hypothesis: with an infinite residue field both
sides of `|A/𝔪^m| = q^m` vanish under `Nat.card`'s junk value, so the statement holds of
every discrete valuation ring and the finite-residue instance enters only at the units.
The graded step is an additive-group first-isomorphism argument — multiplication by
`π ^ m` maps `A` onto `𝔪^m/𝔪^{m+1}` with kernel `𝔪` — rather than a valuation
computation, and the units complement is counted by `Fintype.card_subtype_compl` after
identifying the residue field of `𝒪/𝔪^m` with that of `𝒪` through
`IsLocalRing.ResidueField.map`, which avoids identifying the quotient's maximal ideal
with the image ideal.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section AbstractCount

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)]

omit [Finite (IsLocalRing.ResidueField A)] in
/-- **The quotient by the `m`-th power of the maximal ideal has cardinality `q ^ m`**:
each step of the tower is one residue field, by multiplication with `π ^ m`
([Serre 1979, Chap. IV, §2, Prop. 6 (b), p.66][Serre1979]). -/
theorem card_quotient_maximalIdeal_pow (m : ℕ) :
    Nat.card (A ⧸ IsLocalRing.maximalIdeal A ^ m) =
      Nat.card (IsLocalRing.ResidueField A) ^ m := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  induction m with
  | zero =>
    rw [pow_zero, pow_zero, Ideal.one_eq_top]
    have : Subsingleton (A ⧸ (⊤ : Ideal A)) :=
      Submodule.Quotient.subsingleton_iff.mpr rfl
    exact Nat.card_of_subsingleton (Submodule.Quotient.mk 0)
  | succ m IH =>
    have hle : IsLocalRing.maximalIdeal A ^ (m + 1) ≤ IsLocalRing.maximalIdeal A ^ m :=
      Ideal.pow_le_pow_right (Nat.le_succ m)
    set I : Ideal A := IsLocalRing.maximalIdeal A ^ (m + 1) with hI
    set J : Ideal A := IsLocalRing.maximalIdeal A ^ m with hJ
    have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      ((J.map (Ideal.Quotient.mk I)).toAddSubgroup)
    have hquot : Nat.card
        ((A ⧸ I) ⧸ (J.map (Ideal.Quotient.mk I)).toAddSubgroup) =
        Nat.card (A ⧸ J) :=
      Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hle).toEquiv
    have hsub : Nat.card ((J.map (Ideal.Quotient.mk I)).toAddSubgroup) =
        Nat.card (IsLocalRing.ResidueField A) := by
      let ψ : A →+ A ⧸ I :=
        (Ideal.Quotient.mk I).toAddMonoidHom.comp (AddMonoidHom.mulLeft (π ^ m))
      have hψ : ∀ x : A, ψ x = Ideal.Quotient.mk I (π ^ m * x) := fun x => rfl
      have hrange : ψ.range = (J.map (Ideal.Quotient.mk I)).toAddSubgroup := by
        ext y
        constructor
        · rintro ⟨x, rfl⟩
          rw [Submodule.mem_toAddSubgroup, hψ]
          refine Ideal.mem_map_of_mem _ ?_
          rw [hJ, hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
          exact Dvd.intro x rfl
        · intro hy
          rw [Submodule.mem_toAddSubgroup] at hy
          obtain ⟨z, hz, rfl⟩ :=
            (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).mp hy
          rw [hJ, hπ.maximalIdeal_eq, Ideal.span_singleton_pow,
            Ideal.mem_span_singleton] at hz
          obtain ⟨c, rfl⟩ := hz
          exact ⟨c, rfl⟩
      have hker : ψ.ker = (IsLocalRing.maximalIdeal A).toAddSubgroup := by
        ext x
        rw [AddMonoidHom.mem_ker, Submodule.mem_toAddSubgroup, hπ.maximalIdeal_eq,
          Ideal.mem_span_singleton, hψ,
          show (Ideal.Quotient.mk I (π ^ m * x) = 0) ↔ π ^ m * x ∈ I from
            Ideal.Quotient.eq_zero_iff_mem,
          hI, hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        constructor
        · intro hdvd
          exact (mul_dvd_mul_iff_left (pow_ne_zero m hπ.ne_zero)).mp
            (by rwa [pow_succ] at hdvd)
        · intro hdvd
          rw [pow_succ]
          exact mul_dvd_mul_left _ hdvd
      calc Nat.card ((J.map (Ideal.Quotient.mk I)).toAddSubgroup)
          = Nat.card ψ.range := by rw [hrange]
        _ = Nat.card (A ⧸ ψ.ker) :=
            (Nat.card_congr (QuotientAddGroup.quotientKerEquivRange ψ).toEquiv).symm
        _ = Nat.card (IsLocalRing.ResidueField A) := by rw [hker]; rfl
    calc Nat.card (A ⧸ I)
        = Nat.card ((A ⧸ I) ⧸ (J.map (Ideal.Quotient.mk I)).toAddSubgroup) *
            Nat.card ((J.map (Ideal.Quotient.mk I)).toAddSubgroup) := hcard
      _ = Nat.card (A ⧸ J) * Nat.card (IsLocalRing.ResidueField A) := by
          rw [hquot, hsub]
      _ = Nat.card (IsLocalRing.ResidueField A) ^ m *
            Nat.card (IsLocalRing.ResidueField A) := by rw [IH]
      _ = Nat.card (IsLocalRing.ResidueField A) ^ (m + 1) := (pow_succ _ _).symm

/-- **The unit count of the quotient ring**: `(q − 1) · q ^ (m − 1)` units — the
complement of the maximal ideal of a finite local ring
([Serre 1979, Chap. IV, §2, Prop. 6, p.66][Serre1979]). -/
theorem card_units_quotient_maximalIdeal_pow (m : ℕ) (hm : m ≠ 0) :
    Nat.card (A ⧸ IsLocalRing.maximalIdeal A ^ m)ˣ =
      (Nat.card (IsLocalRing.ResidueField A) - 1) *
        Nat.card (IsLocalRing.ResidueField A) ^ (m - 1) := by
  set I : Ideal A := IsLocalRing.maximalIdeal A ^ m with hI
  set R := A ⧸ I with hR
  have hproper : I ≠ ⊤ := by
    intro htop
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (top_le_iff.mp (htop ▸ Ideal.pow_le_self hm))
  haveI : Nontrivial R := Ideal.Quotient.nontrivial_iff.mpr hproper
  haveI : IsLocalRing R :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  haveI : Finite R := IsLocalRing.finite_quotient_iff.mpr ⟨m, le_refl _⟩
  -- the residue field of the quotient is the residue field downstairs
  have hres : Nat.card (IsLocalRing.ResidueField R) =
      Nat.card (IsLocalRing.ResidueField A) := by
    have hsurj : Function.Surjective
        (IsLocalRing.ResidueField.map (Ideal.Quotient.mk I)) := by
      intro y
      obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
      exact ⟨IsLocalRing.residue A r, IsLocalRing.ResidueField.map_residue _ r⟩
    have hinj : Function.Injective
        (IsLocalRing.ResidueField.map (Ideal.Quotient.mk I)) :=
      RingHom.injective _
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm
  have hcardR : Nat.card R = Nat.card (IsLocalRing.ResidueField A) ^ m :=
    card_quotient_maximalIdeal_pow m
  have hformula := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((IsLocalRing.maximalIdeal R).toAddSubgroup)
  have hqres : Nat.card (R ⧸ (IsLocalRing.maximalIdeal R).toAddSubgroup) =
      Nat.card (IsLocalRing.ResidueField R) := rfl
  have hq : 1 < Nat.card (IsLocalRing.ResidueField A) :=
    Finite.one_lt_card (α := IsLocalRing.ResidueField A)
  have hmR : Nat.card (IsLocalRing.maximalIdeal R) =
      Nat.card (IsLocalRing.ResidueField A) ^ (m - 1) := by
    have h1 : Nat.card (IsLocalRing.ResidueField A) ^ m =
        Nat.card (IsLocalRing.ResidueField A) *
          Nat.card (IsLocalRing.maximalIdeal R) := by
      rw [← hcardR, hformula, hqres, hres]
      rfl
    have h2 : Nat.card (IsLocalRing.ResidueField A) ^ m =
        Nat.card (IsLocalRing.ResidueField A) *
          Nat.card (IsLocalRing.ResidueField A) ^ (m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    exact Nat.eq_of_mul_eq_mul_left
      (by omega : 0 < Nat.card (IsLocalRing.ResidueField A))
      (h1.symm.trans h2)
  classical
  letI : Fintype R := Fintype.ofFinite R
  have hcompl : Nat.card Rˣ =
      Nat.card R - Nat.card (IsLocalRing.maximalIdeal R) := by
    have e1 : Rˣ ≃ {x : R // IsUnit x} :=
      { toFun := fun u => ⟨u, u.isUnit⟩
        invFun := fun x => x.2.unit
        left_inv := fun u => Units.ext u.isUnit.unit_spec
        right_inv := fun x => Subtype.ext x.2.unit_spec }
    have e2 : {x : R // IsUnit x} ≃ {x : R // ¬x ∈ IsLocalRing.maximalIdeal R} :=
      Equiv.subtypeEquivRight fun x => by
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
    rw [Nat.card_congr (e1.trans e2), Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_subtype_compl _
  rw [hcompl, hcardR, hmR, Nat.sub_one_mul, ← pow_succ',
    Nat.sub_add_cancel (by omega : 1 ≤ m)]

end AbstractCount

section LocalField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- The integer higher unit group is the kernel of the reduction on units. -/
private theorem integerHigherUnitGroup_eq_ker (m : ℕ) :
    integerHigherUnitGroup K m =
      (Units.map (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal ↥𝒪[K] ^ m)).toMonoidHom).ker := by
  ext u
  rw [MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one]
  change ((u : ↥𝒪[K]) - 1 ∈ IsLocalRing.maximalIdeal ↥𝒪[K] ^ m) ↔ _
  rw [show (1 : ↥𝒪[K] ⧸ IsLocalRing.maximalIdeal ↥𝒪[K] ^ m) =
      Ideal.Quotient.mk _ 1 from rfl]
  exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).symm

/-- The reduction on units is surjective: any lift of a quotient unit is a unit. -/
private theorem units_map_mk_surjective (m : ℕ) (hm : m ≠ 0) :
    Function.Surjective (Units.map (Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal ↥𝒪[K] ^ m)).toMonoidHom) := by
  set I : Ideal ↥𝒪[K] := IsLocalRing.maximalIdeal ↥𝒪[K] ^ m with hI
  have hproper : I ≠ ⊤ := by
    intro htop
    exact (IsLocalRing.maximalIdeal.isMaximal ↥𝒪[K]).ne_top
      (top_le_iff.mp (htop ▸ Ideal.pow_le_self hm))
  haveI : Nontrivial (↥𝒪[K] ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hproper
  haveI : IsLocalRing (↥𝒪[K] ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  intro y
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (y : ↥𝒪[K] ⧸ I)
  have haunit : IsUnit a := isUnit_of_map_unit (Ideal.Quotient.mk I) a (ha ▸ y.isUnit)
  obtain ⟨u, rfl⟩ := haunit
  refine ⟨u, Units.ext ?_⟩
  rw [Units.coe_map]
  exact ha

/-- **The unit-parameter quotient is the unit group of the level quotient ring**:
`𝒪ˣ/U^(m) ≃* (𝒪/𝔪^m)ˣ`, reduction with kernel exactly `1 + 𝔪^m`
([Serre 1979, Chap. IV, §2, Prop. 6, p.66][Serre1979]). -/
noncomputable def integerHigherUnitGroupQuotientEquiv (m : ℕ) (hm : m ≠ 0) :
    (𝒪[K]ˣ ⧸ integerHigherUnitGroup K m) ≃*
      (↥𝒪[K] ⧸ IsLocalRing.maximalIdeal ↥𝒪[K] ^ m)ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (integerHigherUnitGroup_eq_ker K m)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (units_map_mk_surjective K m hm))

/-- **The unit-parameter count**: `|𝒪ˣ/U^(m)| = (q − 1) · q ^ (m − 1)`
([Serre 1979, Chap. IV, §2, Prop. 6, p.66][Serre1979];
[Yamaguchi 2026, `LubinTate/FiniteLevel/FiniteParameters.lean:108`][Yamaguchi2026]). -/
theorem integerHigherUnitCount (m : ℕ) (hm : m ≠ 0) :
    Nat.card (𝒪[K]ˣ ⧸ integerHigherUnitGroup K m) =
      (Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) - 1) *
        Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) ^ (m - 1) := by
  rw [Nat.card_congr (integerHigherUnitGroupQuotientEquiv K m hm).toEquiv]
  exact card_units_quotient_maximalIdeal_pow m hm

/-- The unit-parameter quotient is **finite**
([Yamaguchi 2026, `LubinTate/FiniteLevel/FiniteParameters.lean:59`][Yamaguchi2026]). -/
theorem finite_integerHigherUnitGroup_quotient (m : ℕ) (hm : m ≠ 0) :
    Finite (𝒪[K]ˣ ⧸ integerHigherUnitGroup K m) := by
  refine Nat.finite_of_card_ne_zero ?_
  rw [integerHigherUnitCount K m hm]
  have hq : 1 < Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) :=
    Finite.one_lt_card (α := IsLocalRing.ResidueField ↥𝒪[K])
  exact Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))

end LocalField

end Atlas.Knowledge
