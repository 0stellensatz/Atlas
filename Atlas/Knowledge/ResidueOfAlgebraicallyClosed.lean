import Mathlib

/-!
# residues of algebraically closed valued fields

The residue field of a valuation subring of an algebraically closed field is
algebraically closed — a monic irreducible residue polynomial lifts monically
to the valuation ring, and a root in the ambient field is integral, so it lies
back in the ring and reduces. Alongside it, the residue comparison of a
pullback valuation ring: the pullback embeds locally, and a purely inseparable
ambient extension stays purely inseparable on residue fields. Together these
feed the algebraic closedness of the selected residue field in the reciprocity
engine's local-side instantiation (#104).

## Main definitions

* `valuationSubringComapResidueMap` — the residue-field embedding induced by
  pulling a valuation ring back along a field embedding.

## Main statements

* `valuationSubring_residueField_isAlgClosed` — the residue field of a
  valuation subring of an algebraically closed field is algebraically closed;
  proved.
* `valuationSubring_comap_residueField_isPurelyInseparable` — a purely
  inseparable ambient extension is purely inseparable on residue fields;
  proved.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

section AlgClosed

variable {Omega : Type u} [Field Omega] [IsAlgClosed Omega]

/-- **The residue field of a valuation subring of an algebraically closed
field is algebraically closed**: a monic irreducible residue polynomial is
lifted monically to the valuation ring, and a root in the ambient field is
integral, hence lies back in the valuation ring and reduces ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean:27`]
[Yamaguchi2026]). -/
theorem valuationSubring_residueField_isAlgClosed
    (A : ValuationSubring Omega) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro p hpmonic hpirreducible
  have hlifts : p ∈ Polynomial.lifts (IsLocalRing.residue A) := by
    rw [Polynomial.mem_lifts]
    exact (Polynomial.map_surjective
      (IsLocalRing.residue A) IsLocalRing.residue_surjective) p
  obtain ⟨q, hqmap, hqdegree, hqmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts hpmonic
  have hqmapSubtypeDegree :
      (q.map A.subtype).degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective A.subtype_injective q]
    rw [hqdegree]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hpirreducible)
  obtain ⟨x, hxroot⟩ :=
    IsAlgClosed.exists_root (q.map A.subtype) hqmapSubtypeDegree
  have hxIntegral : IsIntegral A x := by
    refine ⟨q, hqmonic, ?_⟩
    change Polynomial.eval₂ A.subtype x q = 0
    simpa [Polynomial.eval_map] using hxroot
  have hxA : x ∈ A := by
    let hAIntegers : A.valuation.Integers A :=
      { hom_inj := A.subtype_injective
        map_le_one := fun a =>
          (A.valuation_le_one_iff (a : Omega)).mpr a.property
        exists_of_le_one := fun {r} hr =>
          ⟨⟨r, (A.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
    have hxValuation : A.valuation x ≤ 1 :=
      (hAIntegers.isIntegral_iff_v_le_one).mp hxIntegral
    exact (A.valuation_le_one_iff x).mp hxValuation
  let xA : A := ⟨x, hxA⟩
  have hxrootEval₂ : Polynomial.eval₂ A.subtype x q = 0 := by
    rw [← Polynomial.eval_map]
    exact hxroot
  have hxrootA : q.eval xA = 0 := by
    apply A.subtype_injective
    rw [← Polynomial.eval₂_at_apply A.subtype xA]
    simpa [xA] using hxrootEval₂
  refine ⟨IsLocalRing.residue A xA, ?_⟩
  rw [← hqmap]
  simp [Polynomial.eval_map, hxrootA]

end AlgClosed

section PurelyInseparableComap

variable {F Omega : Type u} [Field F] [Field Omega] [Algebra F Omega]

/-- The inclusion from the pullback of a valuation ring to the ambient
valuation ring ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean:79`]
[Yamaguchi2026]). -/
def valuationSubringComapMap (A : ValuationSubring Omega) :
    A.comap (algebraMap F Omega) →+* A where
  toFun x := ⟨algebraMap F Omega x, x.property⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

/-- Pullback along a field embedding gives a local map of valuation rings
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean:88`]
[Yamaguchi2026]). -/
theorem valuationSubringComapMap_isLocalHom (A : ValuationSubring Omega) :
    IsLocalHom (valuationSubringComapMap (F := F) A) := by
  constructor
  intro x hx
  obtain ⟨u, hu⟩ := hx
  have hx0 : (x : F) ≠ 0 := by
    intro hzero
    have hmapZero : valuationSubringComapMap (F := F) A x = 0 := by
      apply Subtype.ext
      simp [valuationSubringComapMap, hzero]
    exact Units.ne_zero u (hu.trans hmapZero)
  let xinv : A.comap (algebraMap F Omega) :=
    ⟨(x : F)⁻¹, by
      change algebraMap F Omega ((x : F)⁻¹) ∈ A
      rw [map_inv₀]
      have hu' : algebraMap F Omega (x : F) = ((u : A) : Omega) := by
        have h := congrArg Subtype.val hu
        exact h.symm
      rw [hu']
      have hinv : (((u : A) : Omega))⁻¹ = (((u⁻¹ : Aˣ) : A) : Omega) := by
        have hprod :
            ((u : A) : Omega) * (((u⁻¹ : Aˣ) : A) : Omega) = 1 := by
          have hprodA : (u : A) * ((u⁻¹ : Aˣ) : A) = 1 := u.val_inv
          exact congrArg A.subtype hprodA
        exact (eq_inv_of_mul_eq_one_right hprod).symm
      rw [hinv]
      exact (u⁻¹ : Aˣ).val.property⟩
  let xu : (A.comap (algebraMap F Omega))ˣ :=
    { val := x
      inv := xinv
      val_inv := by apply Subtype.ext; simp [xinv, hx0]
      inv_val := by apply Subtype.ext; simp [xinv, hx0] }
  exact ⟨xu, rfl⟩

/-- **The residue-field embedding induced by pullback of a valuation ring**
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean:123`]
[Yamaguchi2026]). -/
def valuationSubringComapResidueMap
    (A : ValuationSubring Omega) :
    IsLocalRing.ResidueField (A.comap (algebraMap F Omega)) →+*
      IsLocalRing.ResidueField A := by
  letI : IsLocalHom (valuationSubringComapMap (F := F) A) :=
    valuationSubringComapMap_isLocalHom (F := F) A
  exact IsLocalRing.ResidueField.map (valuationSubringComapMap (F := F) A)

/-- The residue embedding computes on residues ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean:132`]
[Yamaguchi2026]). -/
@[simp] theorem valuationSubringComapResidueMap_residue
    (A : ValuationSubring Omega)
    (x : A.comap (algebraMap F Omega)) :
    valuationSubringComapResidueMap (F := F) A
        (IsLocalRing.residue (A.comap (algebraMap F Omega)) x) =
      IsLocalRing.residue A (valuationSubringComapMap (F := F) A x) :=
  rfl

/-- **A purely inseparable ambient extension is purely inseparable on residue
fields** — in positive characteristic by the same Frobenius-power argument, in
characteristic zero because the ambient extension is already trivial
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicallyClosed.lean:144`]
[Yamaguchi2026]). -/
theorem valuationSubring_comap_residueField_isPurelyInseparable
    [IsPurelyInseparable F Omega] (A : ValuationSubring Omega) :
    letI : Algebra
        (IsLocalRing.ResidueField (A.comap (algebraMap F Omega)))
        (IsLocalRing.ResidueField A) :=
      (valuationSubringComapResidueMap (F := F) A).toAlgebra
    IsPurelyInseparable
      (IsLocalRing.ResidueField (A.comap (algebraMap F Omega)))
      (IsLocalRing.ResidueField A) := by
  let B := A.comap (algebraMap F Omega)
  let barI := valuationSubringComapResidueMap (F := F) A
  letI : Algebra (IsLocalRing.ResidueField B)
      (IsLocalRing.ResidueField A) := barI.toAlgebra
  obtain ⟨q, hqF⟩ := ExpChar.exists F
  letI : ExpChar F q := hqF
  cases hqF with
  | zero =>
      letI : Algebra.IsSeparable F Omega := inferInstance
      rw [isPurelyInseparable_iff_pow_mem
        (IsLocalRing.ResidueField B)
        (ringExpChar (IsLocalRing.ResidueField B))]
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨z, hz⟩ :=
        IsPurelyInseparable.surjective_algebraMap_of_isSeparable F Omega
          (a : Omega)
      let zB : B := ⟨z, by
        change algebraMap F Omega z ∈ A
        rw [hz]
        exact a.property⟩
      refine ⟨0, IsLocalRing.residue B zB, ?_⟩
      simp only [pow_zero, pow_one]
      change barI (IsLocalRing.residue B zB) = IsLocalRing.residue A a
      dsimp only [barI, B]
      rw [valuationSubringComapResidueMap_residue]
      apply congrArg (IsLocalRing.residue A)
      apply Subtype.ext
      exact hz
  | prime hq =>
      letI : CharP Omega q :=
        charP_of_injective_algebraMap (algebraMap F Omega).injective q
      letI : CharP A q := A.subtype.charP A.subtype_injective q
      letI : CharP (IsLocalRing.ResidueField A) q :=
        CharP.of_ringHom_of_ne_zero (IsLocalRing.residue A) q hq.ne_zero
      letI : CharP (IsLocalRing.ResidueField B) q :=
        barI.charP barI.injective q
      letI : ExpChar (IsLocalRing.ResidueField B) q := ExpChar.prime hq
      rw [isPurelyInseparable_iff_pow_mem
        (IsLocalRing.ResidueField B) q]
      intro y
      obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
      obtain ⟨n, z, hz⟩ := IsPurelyInseparable.pow_mem F q (a : Omega)
      let zB : B := ⟨z, by
        change algebraMap F Omega z ∈ A
        rw [hz]
        exact pow_mem a.property _⟩
      refine ⟨n, IsLocalRing.residue B zB, ?_⟩
      change barI (IsLocalRing.residue B zB) =
        (IsLocalRing.residue A a) ^ q ^ n
      dsimp only [barI, B]
      rw [valuationSubringComapResidueMap_residue]
      rw [← map_pow]
      apply congrArg (IsLocalRing.residue A)
      apply Subtype.ext
      exact hz

end PurelyInseparableComap

end

end Atlas.Knowledge
