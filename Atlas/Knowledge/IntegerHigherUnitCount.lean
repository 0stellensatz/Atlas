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

The ring-side count is Mathlib's `cardQuot_pow_of_prime` read at the maximal ideal — the
Dedekind prime-power count, which unlike the `cardQuot` multiplicativity needs no
`ℤ`-basis — and it carries no finiteness hypothesis: with an infinite residue field both
sides of `|A/𝔪^m| = q^m` vanish under `Nat.card`'s junk value for `m ≥ 1` and are `1` at
`m = 0`, so the statement holds of every discrete valuation ring and the finite-residue
instance enters only at the units. The units complement is counted by
`Fintype.card_subtype_compl` after identifying the residue field of `𝒪/𝔪^m` with that
of `𝒪` through `IsLocalRing.ResidueField.map`, which avoids identifying the quotient's
maximal ideal with the image ideal. Of the neighboring items,
`Atlas.Knowledge.UnitLevelFiniteIndex` proves finiteness of the field-unit-side level
quotient by compactness where this file counts the integer-unit side exactly, and
`Atlas.Knowledge.AbsoluteInertiaDegree` reads the residue field itself.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
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
Mathlib's Dedekind prime-power count at the maximal ideal
([Serre 1979, Chap. IV, §2, Prop. 6 (b), p.66][Serre1979]). -/
theorem card_quotient_maximalIdeal_pow (m : ℕ) :
    Nat.card (A ⧸ IsLocalRing.maximalIdeal A ^ m) =
      Nat.card (IsLocalRing.ResidueField A) ^ m := by
  have h := cardQuot_pow_of_prime (S := A) (P := IsLocalRing.maximalIdeal A)
    (IsDiscreteValuationRing.not_a_field A) (i := m)
  rwa [Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h

/-- **The unit count of the quotient ring**: `(q − 1) · q ^ (m − 1)` units — the
complement of the maximal ideal of a finite local ring
([Milne 2020, Chap. I, §3, Prop. 3.4 and Thm. 3.6 (b), p.38][MilneCFT]). -/
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
        (𝓂[K] ^ m : Ideal ↥𝒪[K])).toMonoidHom).ker := by
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
([Milne 2020, Chap. I, §3, Prop. 3.4 and Thm. 3.6 (b), p.38][MilneCFT]). -/
noncomputable def integerHigherUnitGroupQuotientEquiv (m : ℕ) (hm : m ≠ 0) :
    (𝒪[K]ˣ ⧸ integerHigherUnitGroup K m) ≃*
      (↥𝒪[K] ⧸ (𝓂[K] ^ m : Ideal ↥𝒪[K]))ˣ :=
  (QuotientGroup.quotientMulEquivOfEq (integerHigherUnitGroup_eq_ker K m)).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (units_map_mk_surjective K m hm))

/-- **The unit-parameter count**: `|𝒪ˣ/U^(m)| = (q − 1) · q ^ (m − 1)`
([Serre 1979, Chap. IV, §2, Prop. 6, p.66][Serre1979];
[Yamaguchi 2026, `LubinTate/FiniteLevel/FiniteParameters.lean:108`][Yamaguchi2026]). -/
theorem integerHigherUnitCount (m : ℕ) (hm : m ≠ 0) :
    Nat.card (𝒪[K]ˣ ⧸ integerHigherUnitGroup K m) =
      (Nat.card 𝓀[K] - 1) * Nat.card 𝓀[K] ^ (m - 1) := by
  rw [Nat.card_congr (integerHigherUnitGroupQuotientEquiv K m hm).toEquiv]
  exact card_units_quotient_maximalIdeal_pow m hm

/-- The unit-parameter quotient is **finite**, at every level
([Yamaguchi 2026, `LubinTate/FiniteLevel/FiniteParameters.lean:59`][Yamaguchi2026]). -/
instance finite_integerHigherUnitGroup_quotient (m : ℕ) :
    Finite (𝒪[K]ˣ ⧸ integerHigherUnitGroup K m) := by
  match m with
  | 0 =>
    have htop : integerHigherUnitGroup K 0 = ⊤ := by
      ext u
      simp [integerHigherUnitGroup]
    rw [htop]
    infer_instance
  | (n + 1) =>
    refine Nat.finite_of_card_ne_zero ?_
    rw [integerHigherUnitCount K (n + 1) (Nat.succ_ne_zero n)]
    have hq : 1 < Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) :=
      Finite.one_lt_card (α := IsLocalRing.ResidueField ↥𝒪[K])
    exact Nat.mul_ne_zero (by omega) (pow_ne_zero _ (by omega))

end LocalField

end Atlas.Knowledge
