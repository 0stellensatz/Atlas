import Mathlib
import Atlas.Knowledge.DegreeData

/-!
# Frobenius coordinates on a finite residue extension

For a finite extension of a finite field, exponentiation of the arithmetic
Frobenius `x ↦ x^#k` identifies the Galois group with the cyclic quotient
`ℤ/[L:k]ℤ`, and a profinite integer acts through reduction modulo the degree —
the finite-level source of the reciprocity engine's degree map (#104). No
generator is chosen: the generator is the actual arithmetic Frobenius, and the
coordinates commute with restriction in towers, which is what lets them
assemble over the inverse limit.

## Main definitions

* `finiteResidueFrobeniusExponentHom` / `finiteResidueFrobeniusExponentEquiv` —
  `ℤ/[L:k]ℤ ≃* Gal(L/k)`, sending one to the arithmetic Frobenius.
* `finiteResidueFrobeniusFromZHat` — the continuous action of `ℤ̂` through
  reduction modulo the degree.

## Main statements

* `finiteResidueFrobeniusFromZHat_one` — `1 ∈ ℤ̂` acts as the arithmetic
  Frobenius; proved.
* `finiteResidueFrobeniusFromZHat_eq_one_iff` — the kernel is reduction zero;
  proved.
* `restrictNormalHom_finiteResidueFrobeniusFromZHat` — the `ℤ̂`-actions commute
  with restriction in finite towers; proved.

## Implementation notes

Everything rides Mathlib's `FiniteField.frobeniusAlgEquivOfAlgebraic` and its
order; bijectivity of the exponent map is surjectivity (every automorphism is a
Frobenius power) against the cardinality `IsGalois.card_aut_eq_finrank`. The
positive modulus is carried as a file-local `NeZero` instance on the degree —
local so that its overly general key never enters an importer's search — and
the transition to a subextension is the layer's
`Atlas.Knowledge.ProfiniteInteger.castHom_comp_reduction` read pointwise. The
restriction law for the plain Frobenius drops the `[Finite E]` the section
carries, one hypothesis fewer than the source's statement.

## References

* [MilneANT] J. S. Milne, *Algebraic number theory* (v3.08), available at
  www.jmilne.org/math/, 2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v w

variable (k : Type u) (L : Type v)
  [Field k] [Fintype k] [Field L] [Finite L] [Algebra k L]

local instance : NeZero (Module.finrank k L) := ⟨Module.finrank_pos.ne'⟩

/- Integer powers of the arithmetic Frobenius, written additively. -/
private def finiteResidueFrobeniusIntegerPowers :
    ℤ →+ Additive (L ≃ₐ[k] L) :=
  zmultiplesHom (Additive (L ≃ₐ[k] L)) (Additive.ofMul
    (FiniteField.frobeniusAlgEquivOfAlgebraic k L))

/- The degree annihilates the integer Frobenius powers. -/
private theorem finiteResidueFrobeniusIntegerPowers_degree_eq_zero :
    finiteResidueFrobeniusIntegerPowers k L (Module.finrank k L) = 0 := by
  apply Additive.ext
  change (FiniteField.frobeniusAlgEquivOfAlgebraic k L) ^
      (Module.finrank k L : ℤ) = 1
  rw [← FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic (K := k) (L := L)]
  rw [zpow_natCast, pow_orderOf_eq_one]

/-- **The finite-level exponent homomorphism** `ℤ/[L:k]ℤ → Gal(L/k)`, sending
one to the arithmetic Frobenius (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean:49`). -/
def finiteResidueFrobeniusExponentHom :
    Multiplicative (ZMod (Module.finrank k L)) →* (L ≃ₐ[k] L) :=
  AddMonoidHom.toMultiplicative
    (ZMod.lift (Module.finrank k L)
      ⟨finiteResidueFrobeniusIntegerPowers k L,
        finiteResidueFrobeniusIntegerPowers_degree_eq_zero k L⟩)

/-- An integer exponent maps to the corresponding Frobenius power. -/
@[simp]
theorem finiteResidueFrobeniusExponentHom_intCast (m : ℤ) :
    finiteResidueFrobeniusExponentHom k L
        (Multiplicative.ofAdd (m : ZMod (Module.finrank k L))) =
      (FiniteField.frobeniusAlgEquivOfAlgebraic k L) ^ m := by
  change
    (ZMod.lift (Module.finrank k L)
      ⟨finiteResidueFrobeniusIntegerPowers k L,
        finiteResidueFrobeniusIntegerPowers_degree_eq_zero k L⟩)
      (m : ZMod (Module.finrank k L)) =
        Additive.ofMul ((FiniteField.frobeniusAlgEquivOfAlgebraic k L) ^ m)
  rw [ZMod.lift_coe]
  rfl

/-- Exponent one maps to the arithmetic Frobenius. -/
@[simp]
theorem finiteResidueFrobeniusExponentHom_one :
    finiteResidueFrobeniusExponentHom k L
        (Multiplicative.ofAdd (1 : ZMod (Module.finrank k L))) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k L := by
  simpa using finiteResidueFrobeniusExponentHom_intCast k L 1

/-- **Every automorphism is a Frobenius power**: the exponent map is onto. -/
theorem finiteResidueFrobeniusExponentHom_surjective :
    Function.Surjective (finiteResidueFrobeniusExponentHom k L) := by
  intro sigma
  obtain ⟨m, hm⟩ :=
    (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).2 sigma
  refine ⟨Multiplicative.ofAdd
    ((m.1 : ℤ) : ZMod (Module.finrank k L)), ?_⟩
  rw [finiteResidueFrobeniusExponentHom_intCast]
  simpa [zpow_natCast] using hm

/-- The exponent map is injective: onto plus equal cardinalities. -/
theorem finiteResidueFrobeniusExponentHom_injective :
    Function.Injective (finiteResidueFrobeniusExponentHom k L) := by
  have hcard :
      Nat.card (Multiplicative (ZMod (Module.finrank k L))) =
        Nat.card (L ≃ₐ[k] L) := by
    rw [Nat.card_congr Multiplicative.toAdd,
      Nat.card_zmod, IsGalois.card_aut_eq_finrank]
  exact ((finiteResidueFrobeniusExponentHom_surjective k L).bijective_of_nat_card_le
    hcard.le).1

/-- **The Frobenius coordinates** `ℤ/[L:k]ℤ ≃* Gal(L/k)` — the Galois group of
a finite extension of a finite field is cyclic, generated by the arithmetic
Frobenius ([Milne 2020, Chap. 7, Example 7.54, p.129][MilneANT] — "The Galois
group `Gal(k_n/k)` is a cyclic group of order `n`, having as canonical
generator the Frobenius element `x ↦ x^q`"; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean:104`). -/
def finiteResidueFrobeniusExponentEquiv :
    Multiplicative (ZMod (Module.finrank k L)) ≃* (L ≃ₐ[k] L) :=
  MulEquiv.ofBijective (finiteResidueFrobeniusExponentHom k L)
    ⟨finiteResidueFrobeniusExponentHom_injective k L,
      finiteResidueFrobeniusExponentHom_surjective k L⟩

/-- The equivalence has the exponent map underneath. -/
@[simp]
theorem finiteResidueFrobeniusExponentEquiv_apply (z) :
    finiteResidueFrobeniusExponentEquiv k L z =
      finiteResidueFrobeniusExponentHom k L z :=
  rfl

/-- The equivalence sends one to the arithmetic Frobenius. -/
@[simp]
theorem finiteResidueFrobeniusExponentEquiv_one :
    finiteResidueFrobeniusExponentEquiv k L
        (Multiplicative.ofAdd (1 : ZMod (Module.finrank k L))) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k L :=
  finiteResidueFrobeniusExponentHom_one k L

/-- **A profinite integer acts through reduction modulo the degree**
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean:127`). -/
def finiteResidueFrobeniusFromZHat :
    ProfiniteIntegerMul →ₜ* (L ≃ₐ[k] L) where
  toFun z := finiteResidueFrobeniusExponentHom k L
    (Multiplicative.ofAdd
      (ProfiniteInteger.reduction (Module.finrank k L) z.toAdd))
  map_one' := by
    apply (finiteResidueFrobeniusExponentHom k L).map_one
  map_mul' x y := by
    apply (finiteResidueFrobeniusExponentHom k L).map_mul
  continuous_toFun := by
    apply continuous_of_discreteTopology.comp
    exact continuous_ofAdd.comp
      ((ProfiniteInteger.continuous_reduction (Module.finrank k L)).comp
        continuous_toAdd)

/-- The profinite action computes through reduction. -/
@[simp]
theorem finiteResidueFrobeniusFromZHat_apply (z : ProfiniteIntegerMul) :
    finiteResidueFrobeniusFromZHat k L z =
      finiteResidueFrobeniusExponentHom k L
        (Multiplicative.ofAdd
          (ProfiniteInteger.reduction (Module.finrank k L) z.toAdd)) :=
  rfl

/-- **The distinguished element `1 ∈ ℤ̂` acts as the arithmetic Frobenius**. -/
@[simp]
theorem finiteResidueFrobeniusFromZHat_one :
    finiteResidueFrobeniusFromZHat k L
        (Multiplicative.ofAdd (1 : ProfiniteInteger)) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k L := by
  rw [finiteResidueFrobeniusFromZHat_apply]
  exact finiteResidueFrobeniusExponentHom_one k L

/-- Every automorphism is induced by a profinite exponent. -/
theorem finiteResidueFrobeniusFromZHat_surjective :
    Function.Surjective (finiteResidueFrobeniusFromZHat k L) := by
  intro sigma
  obtain ⟨a, ha⟩ := finiteResidueFrobeniusExponentHom_surjective k L sigma
  obtain ⟨z, hz⟩ := ProfiniteInteger.reduction_surjective
    (Module.finrank k L) a.toAdd
  refine ⟨Multiplicative.ofAdd z, ?_⟩
  rw [finiteResidueFrobeniusFromZHat_apply]
  change finiteResidueFrobeniusExponentHom k L
      (Multiplicative.ofAdd
        (ProfiniteInteger.reduction (Module.finrank k L) z)) = sigma
  rw [hz]
  exact ha

/-- **The kernel is reduction zero**: a profinite exponent acts trivially
exactly when it vanishes modulo the degree. -/
theorem finiteResidueFrobeniusFromZHat_eq_one_iff (z : ProfiniteIntegerMul) :
    finiteResidueFrobeniusFromZHat k L z = 1 ↔
      ProfiniteInteger.reduction (Module.finrank k L) z.toAdd = 0 := by
  rw [finiteResidueFrobeniusFromZHat_apply]
  constructor
  · intro h
    have h' :
        Multiplicative.ofAdd
            (ProfiniteInteger.reduction (Module.finrank k L) z.toAdd) = 1 := by
      apply finiteResidueFrobeniusExponentHom_injective k L
      simpa using h
    exact congrArg Multiplicative.toAdd h'
  · intro h
    rw [h]
    exact (finiteResidueFrobeniusExponentHom k L).map_one

section Tower

variable {E : Type v} {F : Type w}
  [Field E] [Finite E] [Field F] [Finite F]
  [Algebra k E] [Algebra k F] [Algebra E F]
  [IsScalarTower k E F] [Normal k E]

omit [Finite E] in
/-- **The arithmetic Frobenius commutes with restriction** in a finite tower. -/
theorem restrictNormalHom_finiteResidueFrobenius :
    AlgEquiv.restrictNormalHom E
        (FiniteField.frobeniusAlgEquivOfAlgebraic k F) =
      FiniteField.frobeniusAlgEquivOfAlgebraic k E := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E F).injective
  calc
    (algebraMap E F)
        (((AlgEquiv.restrictNormalHom E)
          (FiniteField.frobeniusAlgEquivOfAlgebraic k F)) x) =
        FiniteField.frobeniusAlgEquivOfAlgebraic k F
          (algebraMap E F x) :=
      AlgEquiv.restrictNormal_commutes
        (FiniteField.frobeniusAlgEquivOfAlgebraic k F) E x
    _ = (algebraMap E F
        ((FiniteField.frobeniusAlgEquivOfAlgebraic k E) x) : F) := by
      simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
      exact (map_pow (algebraMap E F) x (Fintype.card k)).symm

/-- The exponent coordinates commute with restriction, the smaller exponent
obtained by the canonical reduction. -/
theorem restrictNormalHom_finiteResidueFrobeniusExponentHom
    (z : Multiplicative (ZMod (Module.finrank k F))) :
    AlgEquiv.restrictNormalHom E
        (finiteResidueFrobeniusExponentHom k F z) =
      finiteResidueFrobeniusExponentHom k E
        (Multiplicative.ofAdd
          (ZMod.castHom
            (show Module.finrank k E ∣ Module.finrank k F from
              ⟨Module.finrank E F,
                (Module.finrank_mul_finrank k E F).symm⟩)
            (ZMod (Module.finrank k E)) z.toAdd)) := by
  rcases ZMod.intCast_surjective z.toAdd with ⟨m, hm⟩
  have hz : z = Multiplicative.ofAdd
      (m : ZMod (Module.finrank k F)) := by
    apply Multiplicative.ext
    exact hm.symm
  subst hz
  apply AlgEquiv.ext
  intro x
  rw [finiteResidueFrobeniusExponentHom_intCast]
  simp only [toAdd_ofAdd]
  have hred :
      ZMod.castHom
          (show Module.finrank k E ∣ Module.finrank k F from
            ⟨Module.finrank E F,
              (Module.finrank_mul_finrank k E F).symm⟩)
          (ZMod (Module.finrank k E))
          (m : ZMod (Module.finrank k F)) =
        (m : ZMod (Module.finrank k E)) := by
    exact map_intCast _ m
  rw [hred, finiteResidueFrobeniusExponentHom_intCast]
  have hfrob := restrictNormalHom_finiteResidueFrobenius
    (k := k) (E := E) (F := F)
  have hpow := congrArg (fun sigma : E ≃ₐ[k] E => sigma ^ m) hfrob
  rw [map_zpow]
  exact DFunLike.congr_fun hpow x

/-- **The `ℤ̂`-actions commute with restriction** in finite towers
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean:266`). -/
theorem restrictNormalHom_finiteResidueFrobeniusFromZHat (z : ProfiniteIntegerMul) :
    AlgEquiv.restrictNormalHom E
        (finiteResidueFrobeniusFromZHat k F z) =
      finiteResidueFrobeniusFromZHat k E z := by
  rw [finiteResidueFrobeniusFromZHat_apply,
    restrictNormalHom_finiteResidueFrobeniusExponentHom,
    finiteResidueFrobeniusFromZHat_apply]
  congr 2
  apply Multiplicative.ext
  exact RingHom.congr_fun
    (ProfiniteInteger.castHom_comp_reduction
      (show Module.finrank k E ∣ Module.finrank k F from
        ⟨Module.finrank E F, (Module.finrank_mul_finrank k E F).symm⟩))
    z.toAdd

end Tower

end

end Atlas.Knowledge
