import Mathlib
import Atlas.Knowledge.OfIntermediateFieldInExtension
import Atlas.Knowledge.ResidueAbsoluteFrobenius
import Atlas.Knowledge.SemilinearConjugationContinuous

/-!
# intrinsic residue degree

The residue field carved out of a valuation ring in a separable closure is not
definitionally a chosen `AlgebraicClosure`, so the degree map must exist on any
algebraically closed algebraic extension `Ω` of the finite residue field. Here
the Frobenius-parameter homomorphism `ℤ̂ → Gal(Ω/k)` is an isomorphism —
injective because finite subextensions of every degree detect all coordinates,
surjective because its compact image fixes only the base field — and its
inverse is the intrinsic residue degree, sending the arithmetic Frobenius to
`1`, invariant under simultaneous semilinear equivalence, and scaling by the
degree under a finite change of base.

## Main definitions

* `finiteResidueGaloisIntermediateFieldIn` — a degree-`n` finite Galois
  subextension of `Ω`, for every positive `n`.
* `residueAbsoluteFrobeniusEquivIn` — `ℤ̂ ≃ₜ* Gal(Ω/k)`.
* `residueAbsoluteDegreeIn` — the inverse, the intrinsic degree map.

## Main statements

* `residueAbsoluteFrobenius_isAlgClosure_injective` /
  `residueAbsoluteFrobenius_isAlgClosure_surjective` — the two halves of the
  isomorphism; proved.
* `residueAbsoluteDegreeIn_semilinear_conjugation` — choice-independence of
  the degree map; proved.
* `mem_range_algebraMap_iff_frobenius_fixed_in` — the Frobenius-fixed points
  are the base field; proved.
* `residueAbsoluteFrobenius_restrictScalars` /
  `residueAbsoluteDegreeIn_restrictScalars` — the finite-base-change scaling;
  proved.
* `finiteResidueFrobeniusExponentEquiv_symm_restrict_in` — the
  finite-coordinate compatibility; proved.

## Implementation notes

Injectivity detects coordinates on the embedded images of Mathlib's
`FiniteField.Extension`; surjectivity is the fixed-field argument — the compact
Frobenius image is closed, its fixed field is the base by the `x^q = x`
splitting, and `InfiniteGalois.fixingSubgroup_fixedField` finishes.
Choice-independence and base change both compare two continuous homomorphisms
out of `ℤ̂` on the dense image of `ℤ` after checking the generator, riding
`Atlas.Knowledge.semilinear_conjugation_continuous` and
`Atlas.Knowledge.ofIntermediateFieldInExtension_continuous`. The semilinear comparison allows
independent universes for the two residue fields and their closures. The positive
degree rides the same file-local `NeZero` device as the finite coordinates; the
character-prime and closure instances are likewise local, never entering an
importer's search. The degree lemma of the level-`n` subextension carries the
algebraicity hypothesis the source omits — here the embedding chain references
it, so the omission is refused.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open Polynomial

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

set_option linter.unusedFintypeInType false in
local instance : Fact (ringChar k).Prime :=
  ⟨CharP.char_is_prime k (ringChar k)⟩

local instance : IsAlgClosure k Omega :=
  ⟨inferInstance, inferInstance⟩

local instance (L : Type v) [Field L] [Finite L] [Algebra k L] :
    NeZero (Module.finrank k L) := ⟨Module.finrank_pos.ne'⟩

/- Embed the degree-`n` finite extension of `k` into the given closure. -/
private def finiteResidueExtensionEmbeddingInto (n : ℕ) [NeZero n] :
    FiniteField.Extension k (ringChar k) n →ₐ[k] Omega :=
  IsAlgClosed.lift

/- The image of the degree-`n` extension in the given closure. -/
private def finiteResidueIntermediateFieldIn (n : ℕ) [NeZero n] :
    IntermediateField k Omega :=
  (⊤ : IntermediateField k
      (FiniteField.Extension k (ringChar k) n)).map
    (finiteResidueExtensionEmbeddingInto k Omega n)

/- The model extension is isomorphic to its image. -/
private def finiteResidueExtensionEquivIntermediateIn (n : ℕ) [NeZero n] :
    FiniteField.Extension k (ringChar k) n ≃ₐ[k]
      finiteResidueIntermediateFieldIn k Omega n :=
  IntermediateField.topEquiv.symm.trans
    (IntermediateField.equivMap ⊤
      (finiteResidueExtensionEmbeddingInto k Omega n))

/-- **A degree-`n` finite Galois subextension of any residue algebraic
closure**, for every positive `n` — the embedded image of Mathlib's
`FiniteField.Extension` (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean:75`). -/
def finiteResidueGaloisIntermediateFieldIn (n : ℕ) [NeZero n] :
    FiniteGaloisIntermediateField k Omega where
  toIntermediateField := finiteResidueIntermediateFieldIn k Omega n
  finiteDimensional := Module.Finite.equiv
    (finiteResidueExtensionEquivIntermediateIn k Omega n).toLinearEquiv
  isGalois := IsGalois.of_algEquiv
    (finiteResidueExtensionEquivIntermediateIn k Omega n)

/-- The level-`n` subextension has degree `n`. -/
@[simp]
theorem finrank_finiteResidueGaloisIntermediateFieldIn (n : ℕ) [NeZero n] :
    Module.finrank k
        (finiteResidueGaloisIntermediateFieldIn k Omega n) = n := by
  calc
    Module.finrank k
        (finiteResidueGaloisIntermediateFieldIn k Omega n) =
        Module.finrank k
          (FiniteField.Extension k (ringChar k) n) :=
      (finiteResidueExtensionEquivIntermediateIn
        k Omega n).toLinearEquiv.finrank_eq.symm
    _ = n := FiniteField.finrank_extension k (ringChar k) n

/-- **The Frobenius homomorphism is injective**: finite subextensions of every
positive degree detect every coordinate (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean:101`). -/
theorem residueAbsoluteFrobenius_isAlgClosure_injective :
    Function.Injective (residueAbsoluteFrobenius k Omega) := by
  intro z w hzw
  apply Multiplicative.ext
  apply ProfiniteInteger.ext
  intro n hn
  let E := finiteResidueGaloisIntermediateFieldIn k Omega n
  have hrestriction := congrArg (AlgEquiv.restrictNormalHom E) hzw
  rw [restrictNormalHom_residueAbsoluteFrobenius (z := z) (E := E),
    restrictNormalHom_residueAbsoluteFrobenius (z := w) (E := E)]
    at hrestriction
  letI : Finite E := Module.finite_of_finite k
  change finiteResidueFrobeniusFromZHat k E z =
    finiteResidueFrobeniusFromZHat k E w at hrestriction
  rw [finiteResidueFrobeniusFromZHat_apply,
    finiteResidueFrobeniusFromZHat_apply] at hrestriction
  have hcoordinate := congrArg Multiplicative.toAdd
    (finiteResidueFrobeniusExponentHom_injective k E hrestriction)
  have hdegree : Module.finrank k E = n :=
    finrank_finiteResidueGaloisIntermediateFieldIn k Omega n
  simp only [toAdd_ofAdd] at hcoordinate
  change ProfiniteInteger.reduction (Module.finrank k E) z.toAdd =
    ProfiniteInteger.reduction (Module.finrank k E) w.toAdd at hcoordinate
  have hdiv : n ∣ Module.finrank k E := by simp [hdegree]
  have hcast := congrArg (ZMod.castHom hdiv (ZMod n)) hcoordinate
  have htransz := RingHom.congr_fun
    (ProfiniteInteger.castHom_comp_reduction hdiv) z.toAdd
  have htransw := RingHom.congr_fun
    (ProfiniteInteger.castHom_comp_reduction hdiv) w.toAdd
  rw [RingHom.comp_apply] at htransz htransw
  rw [htransz, htransw] at hcast
  exact hcast

omit [IsAlgClosed Omega] in
/-- **The fixed points of the arithmetic Frobenius are the base field**: fixed
elements are roots of `X^q − X`, which splits over the base (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean:134`). -/
theorem mem_range_algebraMap_iff_frobenius_fixed_in (x : Omega) :
    x ∈ Set.range (algebraMap k Omega) ↔
      FiniteField.frobeniusAlgEquivOfAlgebraic k Omega x = x := by
  constructor
  · rintro ⟨a, rfl⟩
    simp only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic]
    rw [← map_pow, FiniteField.pow_card]
  · intro hx
    have hxpow : x ^ Fintype.card k = x := by
      simpa only [FiniteField.coe_frobeniusAlgEquivOfAlgebraic] using hx
    let p : k[X] := X ^ Fintype.card k - X
    have hpne : p ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero k Fintype.one_lt_card
    have hxroot : x ∈ p.rootSet Omega := by
      rw [Polynomial.mem_rootSet_of_ne hpne]
      simp [p, hxpow]
    have hsplits : (p.map (algebraMap k k)).Splits := by
      simpa only [p] using (FiniteField.isSplittingField_sub k k).splits
    have himage := hsplits.image_rootSet (Algebra.ofId k Omega)
    rw [← himage] at hxroot
    rcases hxroot with ⟨a, _ha, hax⟩
    exact ⟨a, hax⟩

/- The compact image of the Frobenius homomorphism. -/
private def residueAbsoluteFrobeniusRangeIn :
    ClosedSubgroup (Omega ≃ₐ[k] Omega) where
  toSubgroup := (residueAbsoluteFrobenius k Omega).toMonoidHom.range
  isClosed' := by
    change IsClosed (Set.range (residueAbsoluteFrobenius k Omega))
    exact (isCompact_range
      (residueAbsoluteFrobenius k Omega).continuous_toFun).isClosed

/- The compact Frobenius image fixes precisely the base field. -/
private theorem fixedField_residueAbsoluteFrobeniusRangeIn :
    IntermediateField.fixedField
        (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup = ⊥ := by
  apply le_antisymm
  · intro x hx
    have hfrobenius_mem :
        FiniteField.frobeniusAlgEquivOfAlgebraic k Omega ∈
          residueAbsoluteFrobeniusRangeIn k Omega := by
      change FiniteField.frobeniusAlgEquivOfAlgebraic k Omega ∈
        (residueAbsoluteFrobenius k Omega).toMonoidHom.range
      exact ⟨Multiplicative.ofAdd (1 : ProfiniteInteger),
        residueAbsoluteFrobenius_one k Omega⟩
    rw [IntermediateField.mem_fixedField_iff] at hx
    have hxFrobenius := hx
      (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)
      hfrobenius_mem
    rw [IntermediateField.mem_bot]
    exact (mem_range_algebraMap_iff_frobenius_fixed_in k Omega x).mpr
      hxFrobenius
  · exact bot_le

/-- **The Frobenius homomorphism is surjective**: its compact image is closed
and fixes only the base field, so the Galois correspondence makes it
everything (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean:199`). -/
theorem residueAbsoluteFrobenius_isAlgClosure_surjective :
    Function.Surjective (residueAbsoluteFrobenius k Omega) := by
  intro sigma
  have htop : (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup = ⊤ := by
    have hfixed := InfiniteGalois.fixingSubgroup_fixedField
      (residueAbsoluteFrobeniusRangeIn k Omega)
    rw [fixedField_residueAbsoluteFrobeniusRangeIn,
      IntermediateField.fixingSubgroup_bot] at hfixed
    exact hfixed.symm
  have hsigma : sigma ∈
      (residueAbsoluteFrobeniusRangeIn k Omega).toSubgroup := by
    rw [htop]
    exact Subgroup.mem_top sigma
  exact hsigma

/-- **The Frobenius parameter is a topological isomorphism**
`ℤ̂ ≃ₜ* Gal(Ω/k)` (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean:210`). -/
def residueAbsoluteFrobeniusEquivIn :
    ProfiniteIntegerMul ≃ₜ* (Omega ≃ₐ[k] Omega) where
  toMulEquiv := MulEquiv.ofBijective
    (residueAbsoluteFrobenius k Omega).toMonoidHom
    ⟨residueAbsoluteFrobenius_isAlgClosure_injective k Omega,
      residueAbsoluteFrobenius_isAlgClosure_surjective k Omega⟩
  continuous_toFun := (residueAbsoluteFrobenius k Omega).continuous_toFun
  continuous_invFun :=
    Continuous.continuous_symm_of_equiv_compact_to_t2
      (f := (MulEquiv.ofBijective
        (residueAbsoluteFrobenius k Omega).toMonoidHom
        ⟨residueAbsoluteFrobenius_isAlgClosure_injective k Omega,
          residueAbsoluteFrobenius_isAlgClosure_surjective k Omega⟩).toEquiv)
      (residueAbsoluteFrobenius k Omega).continuous_toFun

/-- **The intrinsic residue degree**: the inverse of the arithmetic Frobenius
coordinates on the actual residue algebraic closure (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean:227`). -/
def residueAbsoluteDegreeIn : (Omega ≃ₐ[k] Omega) →ₜ* ProfiniteIntegerMul :=
  ContinuousMonoidHom.toContinuousMonoidHom
    (residueAbsoluteFrobeniusEquivIn k Omega).symm

/-- **The intrinsic degree is invariant under simultaneous semilinear
equivalence** of the residue base and its closure — choice-independence of the
degree datum; the conjugate automorphism is written locally in the statement
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean:236`). -/
theorem residueAbsoluteDegreeIn_semilinear_conjugation
    {k' : Type*} {Omega' : Type*}
    [Field k'] [Fintype k']
    [Field Omega'] [Algebra k' Omega']
    [Algebra.IsAlgebraic k' Omega'] [IsAlgClosed Omega']
    (tau : k ≃+* k') (e : Omega ≃+* Omega')
    (he : ∀ x : k,
      e (algebraMap k Omega x) = algebraMap k' Omega' (tau x))
    (sigma : Omega ≃ₐ[k] Omega) :
    let sigma' : Omega' ≃ₐ[k'] Omega' :=
      { e.symm.trans (sigma.toRingEquiv.trans e) with
        commutes' := fun x => by
          change e (sigma (e.symm (algebraMap k' Omega' x))) =
            algebraMap k' Omega' x
          have hpre :
              e.symm (algebraMap k' Omega' x) =
                algebraMap k Omega (tau.symm x) := by
            apply e.injective
            rw [e.apply_symm_apply, he, tau.apply_symm_apply]
          rw [hpre, sigma.commutes, he, tau.apply_symm_apply] }
    residueAbsoluteDegreeIn k' Omega' sigma' =
      residueAbsoluteDegreeIn k Omega sigma := by
  let conjugate (g : Omega ≃ₐ[k] Omega) :
      Omega' ≃ₐ[k'] Omega' :=
    AlgEquiv.ofRingEquiv
      (f := e.symm.trans (g.toRingEquiv.trans e)) (fun x => by
        change e (g (e.symm (algebraMap k' Omega' x))) =
          algebraMap k' Omega' x
        have hpre :
            e.symm (algebraMap k' Omega' x) =
              algebraMap k Omega (tau.symm x) := by
          apply e.injective
          rw [e.apply_symm_apply, he, tau.apply_symm_apply]
        rw [hpre, g.commutes, he, tau.apply_symm_apply])
  have conjugate_one : conjugate 1 = 1 := by
    apply AlgEquiv.ext
    intro x
    simp [conjugate]
  have conjugate_mul (g h : Omega ≃ₐ[k] Omega) :
      conjugate (g * h) = conjugate g * conjugate h := by
    apply AlgEquiv.ext
    intro x
    simp [conjugate, AlgEquiv.mul_apply]
  let conjugation :
      (Omega ≃ₐ[k] Omega) →* (Omega' ≃ₐ[k'] Omega') :=
    { toFun := conjugate
      map_one' := conjugate_one
      map_mul' := conjugate_mul }
  let conjugationContinuous :
      (Omega ≃ₐ[k] Omega) →ₜ* (Omega' ≃ₐ[k'] Omega') :=
    { toMonoidHom := conjugation
      continuous_toFun :=
        semilinear_conjugation_continuous
          tau e he conjugation (fun _ => rfl) }
  let lhs : ProfiniteIntegerMul →ₜ* (Omega' ≃ₐ[k'] Omega') :=
    conjugationContinuous.comp (residueAbsoluteFrobenius k Omega)
  let rhs : ProfiniteIntegerMul →ₜ* (Omega' ≃ₐ[k'] Omega') :=
    residueAbsoluteFrobenius k' Omega'
  have hgenerator :
      lhs (Multiplicative.ofAdd (1 : ProfiniteInteger)) =
        rhs (Multiplicative.ofAdd (1 : ProfiniteInteger)) := by
    change conjugation
        (residueAbsoluteFrobenius k Omega
          (Multiplicative.ofAdd (1 : ProfiniteInteger))) =
      residueAbsoluteFrobenius k' Omega'
        (Multiplicative.ofAdd (1 : ProfiniteInteger))
    rw [residueAbsoluteFrobenius_one, residueAbsoluteFrobenius_one]
    apply AlgEquiv.ext
    intro x
    change e ((e.symm x) ^ Fintype.card k) =
      x ^ Fintype.card k'
    rw [map_pow, e.apply_symm_apply,
      Fintype.card_congr tau.toEquiv]
  let iota : Multiplicative ℤ →* ProfiniteIntegerMul :=
    AddMonoidHom.toMultiplicative
      (Int.castRingHom ProfiniteInteger).toAddMonoidHom
  have hiota : DenseRange iota := by
    have hOfAdd :
        DenseRange
          (Multiplicative.ofAdd : ProfiniteInteger → ProfiniteIntegerMul) :=
      (show Function.Surjective
          (Multiplicative.ofAdd : ProfiniteInteger → ProfiniteIntegerMul) from
        fun x => ⟨Multiplicative.toAdd x, rfl⟩).denseRange
    have hCast :
        DenseRange
          (Multiplicative.ofAdd ∘ fun a : ℤ => (a : ProfiniteInteger)) :=
      hOfAdd.comp ProfiniteInteger.denseRange_intCast continuous_id
    have hToAdd :
        DenseRange (Multiplicative.toAdd : Multiplicative ℤ → ℤ) :=
      (show Function.Surjective
          (Multiplicative.toAdd : Multiplicative ℤ → ℤ) from
        fun a => ⟨Multiplicative.ofAdd a, rfl⟩).denseRange
    simpa [iota, Function.comp_def] using
      hCast.comp hToAdd continuous_of_discreteTopology
  have hcomp :
      lhs.toMonoidHom.comp iota = rhs.toMonoidHom.comp iota := by
    apply MonoidHom.ext_mint
    simpa [iota] using hgenerator
  have heq (w : ProfiniteIntegerMul) : lhs w = rhs w := by
    have hfun :=
      hiota.equalizer lhs.continuous_toFun rhs.continuous_toFun <| by
        funext n
        exact DFunLike.congr_fun hcomp n
    exact congrFun hfun w
  let z := residueAbsoluteDegreeIn k Omega sigma
  have hz :
      conjugation (residueAbsoluteFrobenius k Omega z) =
        residueAbsoluteFrobenius k' Omega' z :=
    heq z
  apply (residueAbsoluteFrobeniusEquivIn k' Omega').injective
  change
    (residueAbsoluteFrobeniusEquivIn k' Omega')
        ((residueAbsoluteFrobeniusEquivIn k' Omega').symm
          (conjugation sigma)) =
      (residueAbsoluteFrobeniusEquivIn k' Omega')
        ((residueAbsoluteFrobeniusEquivIn k Omega).symm sigma)
  rw [(residueAbsoluteFrobeniusEquivIn k' Omega').apply_symm_apply]
  change conjugation sigma =
    residueAbsoluteFrobenius k' Omega' z
  have hsigma :
      sigma = residueAbsoluteFrobenius k Omega z := by
    change sigma =
      (residueAbsoluteFrobeniusEquivIn k Omega)
        ((residueAbsoluteFrobeniusEquivIn k Omega).symm sigma)
    exact
      ((residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply sigma).symm
  exact (congrArg conjugation hsigma).trans hz

/-- **Frobenius under a finite change of residue base**: forgetting the
`E`-linear structure multiplies the coordinate by `[E : k]`
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean:367`). -/
theorem residueAbsoluteFrobenius_restrictScalars
    (E : IntermediateField k Omega) [FiniteDimensional k E]
    (z : ProfiniteIntegerMul) :
    letI : Finite E := Module.finite_of_finite k
    letI : Fintype E := Fintype.ofFinite E
    (residueAbsoluteFrobenius E Omega z).restrictScalars k =
      residueAbsoluteFrobenius k Omega
        (Multiplicative.ofAdd
          ((Module.finrank k E) • z.toAdd)) := by
  letI : Finite E := Module.finite_of_finite k
  letI : Fintype E := Fintype.ofFinite E
  let scale : ProfiniteIntegerMul →ₜ* ProfiniteIntegerMul :=
    { toFun := fun w => Multiplicative.ofAdd
        ((Module.finrank k E) • w.toAdd)
      map_one' := by
        apply Multiplicative.ext
        simp
      map_mul' := fun x y => by
        apply Multiplicative.ext
        simp [smul_add]
      continuous_toFun := by
        exact continuous_ofAdd.comp
          ((continuous_const_smul (Module.finrank k E)).comp
            continuous_toAdd) }
  let inclusion : (Omega ≃ₐ[E] Omega) →ₜ* (Omega ≃ₐ[k] Omega) :=
    { toMonoidHom := ofIntermediateFieldInExtension E
      continuous_toFun := ofIntermediateFieldInExtension_continuous E }
  let lhs : ProfiniteIntegerMul →ₜ* (Omega ≃ₐ[k] Omega) :=
    inclusion.comp (residueAbsoluteFrobenius E Omega)
  let rhs : ProfiniteIntegerMul →ₜ* (Omega ≃ₐ[k] Omega) :=
    (residueAbsoluteFrobenius k Omega).comp scale
  have hgenerator :
      lhs (Multiplicative.ofAdd (1 : ProfiniteInteger)) =
        rhs (Multiplicative.ofAdd (1 : ProfiniteInteger)) := by
    change
      (residueAbsoluteFrobenius E Omega
          (Multiplicative.ofAdd (1 : ProfiniteInteger))).restrictScalars k =
        residueAbsoluteFrobenius k Omega
          (Multiplicative.ofAdd
            ((Module.finrank k E) • (1 : ProfiniteInteger)))
    rw [residueAbsoluteFrobenius_one]
    have hscale :
        Multiplicative.ofAdd
            ((Module.finrank k E) • (1 : ProfiniteInteger)) =
          (Multiplicative.ofAdd (1 : ProfiniteInteger)) ^
            Module.finrank k E := by
      apply Multiplicative.ext
      simp
    rw [hscale, map_pow, residueAbsoluteFrobenius_one]
    apply AlgEquiv.ext
    intro x
    change
      FiniteField.frobeniusAlgEquivOfAlgebraic E Omega x =
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega ^
          Module.finrank k E) x
    rw [FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
      AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate,
      Module.card_eq_pow_finrank (K := k) (V := E)]
  let iota : Multiplicative ℤ →* ProfiniteIntegerMul :=
    AddMonoidHom.toMultiplicative
      (Int.castRingHom ProfiniteInteger).toAddMonoidHom
  have hiota : DenseRange iota := by
    have hOfAdd :
        DenseRange
          (Multiplicative.ofAdd : ProfiniteInteger → ProfiniteIntegerMul) :=
      (show Function.Surjective
          (Multiplicative.ofAdd : ProfiniteInteger → ProfiniteIntegerMul) from
        fun x => ⟨Multiplicative.toAdd x, rfl⟩).denseRange
    have hCast :
        DenseRange
          (Multiplicative.ofAdd ∘ fun a : ℤ => (a : ProfiniteInteger)) :=
      hOfAdd.comp ProfiniteInteger.denseRange_intCast continuous_id
    have hToAdd :
        DenseRange (Multiplicative.toAdd : Multiplicative ℤ → ℤ) :=
      (show Function.Surjective
          (Multiplicative.toAdd : Multiplicative ℤ → ℤ) from
        fun a => ⟨Multiplicative.ofAdd a, rfl⟩).denseRange
    simpa [iota, Function.comp_def] using
      hCast.comp hToAdd continuous_of_discreteTopology
  have hcomp :
      lhs.toMonoidHom.comp iota = rhs.toMonoidHom.comp iota := by
    apply MonoidHom.ext_mint
    simpa [iota] using hgenerator
  have heq (w : ProfiniteIntegerMul) : lhs w = rhs w := by
    have hfun :=
      hiota.equalizer lhs.continuous_toFun rhs.continuous_toFun <| by
        funext n
        exact DFunLike.congr_fun hcomp n
    exact congrFun hfun w
  exact heq z

/-- **The intrinsic degree under a finite change of residue base** scales by
the degree (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean:455`). -/
theorem residueAbsoluteDegreeIn_restrictScalars
    (E : IntermediateField k Omega) [FiniteDimensional k E]
    (sigma : Omega ≃ₐ[E] Omega) :
    letI : Finite E := Module.finite_of_finite k
    letI : Fintype E := Fintype.ofFinite E
    residueAbsoluteDegreeIn k Omega (sigma.restrictScalars k) =
      Multiplicative.ofAdd
        ((Module.finrank k E) •
          (residueAbsoluteDegreeIn E Omega sigma).toAdd) := by
  letI : Finite E := Module.finite_of_finite k
  letI : Fintype E := Fintype.ofFinite E
  apply (residueAbsoluteFrobeniusEquivIn k Omega).injective
  change
    (residueAbsoluteFrobeniusEquivIn k Omega)
        ((residueAbsoluteFrobeniusEquivIn k Omega).symm
          (sigma.restrictScalars k)) =
      (residueAbsoluteFrobeniusEquivIn k Omega)
        (Multiplicative.ofAdd
          ((Module.finrank k E) •
            ((residueAbsoluteFrobeniusEquivIn E Omega).symm sigma).toAdd))
  rw [(residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply]
  change sigma.restrictScalars k =
    residueAbsoluteFrobenius k Omega
      (Multiplicative.ofAdd
        ((Module.finrank k E) •
          ((residueAbsoluteFrobeniusEquivIn E Omega).symm sigma).toAdd))
  rw [← residueAbsoluteFrobenius_restrictScalars]
  exact congrArg (fun g : Omega ≃ₐ[E] Omega => g.restrictScalars k)
    ((residueAbsoluteFrobeniusEquivIn E Omega).apply_symm_apply sigma).symm

/-- **The intrinsic degree sends the arithmetic Frobenius to `1`**. -/
@[simp]
theorem residueAbsoluteDegreeIn_frobenius :
    residueAbsoluteDegreeIn k Omega
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega) =
      Multiplicative.ofAdd (1 : ProfiniteInteger) := by
  apply (residueAbsoluteFrobeniusEquivIn k Omega).injective
  change (residueAbsoluteFrobeniusEquivIn k Omega)
      ((residueAbsoluteFrobeniusEquivIn k Omega).symm
        (FiniteField.frobeniusAlgEquivOfAlgebraic k Omega)) =
    (residueAbsoluteFrobeniusEquivIn k Omega)
      (Multiplicative.ofAdd (1 : ProfiniteInteger))
  rw [(residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply]
  exact (residueAbsoluteFrobenius_one k Omega).symm

/-- **Finite-coordinate compatibility**: the inverse finite Frobenius
coordinate of a restriction is the reduction of the intrinsic degree
(Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/ResidueAlgebraicClosureDegree.lean:501`). -/
theorem finiteResidueFrobeniusExponentEquiv_symm_restrict_in
    (sigma : Omega ≃ₐ[k] Omega)
    (E : FiniteGaloisIntermediateField k Omega) :
    letI : Finite E := Module.finite_of_finite k
    (finiteResidueFrobeniusExponentEquiv k E).symm
        (AlgEquiv.restrictNormalHom E sigma) =
      Multiplicative.ofAdd
        (ProfiniteInteger.reduction (Module.finrank k E)
          (residueAbsoluteDegreeIn k Omega sigma).toAdd) := by
  letI : Finite E := Module.finite_of_finite k
  apply (finiteResidueFrobeniusExponentEquiv k E).injective
  rw [(finiteResidueFrobeniusExponentEquiv k E).apply_symm_apply]
  change AlgEquiv.restrictNormalHom E sigma =
    finiteResidueFrobeniusIntermediate k Omega E
      (residueAbsoluteDegreeIn k Omega sigma)
  rw [← restrictNormalHom_residueAbsoluteFrobenius]
  congr 1
  exact ((residueAbsoluteFrobeniusEquivIn k Omega).apply_symm_apply
    sigma).symm

end

end Atlas.Knowledge
