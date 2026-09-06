import Mathlib
import Atlas.Knowledge.AbelianizedGaloisCyclotomicRigidity
import Atlas.Knowledge.AbsoluteAbelianOpenSubgroupField
import Atlas.Knowledge.ArtinNormKernelBaseChange
import Atlas.Knowledge.LocalReciprocityPowerAction
import Atlas.Knowledge.NormalizedValuationNormSeparable
import Atlas.Knowledge.TopologicalAbelianizationMap
import Atlas.Knowledge.UniformizerUnitsGenerate

/-!
# absolute local reciprocity and the norm

An Artin lift over a finite extension restricts, after identifying algebraic closures, to
an Artin lift of the field norm over the smaller base. The proof uses norm transitivity for
kernel containment and the residue degree for the Frobenius exponent.

## Main statements

* `IsLocalReciprocity.norm_lift` — the absolute norm square on representatives.

## Implementation notes

The proof works with any closure equivalence over the smaller base. It uses the defining
norm kernels and Frobenius normalization, through cyclotomic rigidity, so neither normality
of the base change nor an identification of intrinsic and induced class formations is needed.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

variable (K E : Type*) [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]
  [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  [ValuativeRel E] [TopologicalSpace E] [IsMixedCharLocalField E] [ValuativeExtension K E]

/-- Restriction of an upstairs Artin lift is an Artin lift of the norm
([Serre 1979, Chap. XIII, §4, Prop. 10 (a), p.197][Serre1979]). -/
theorem IsLocalReciprocity.norm_lift
    {φK : Kˣ →* Field.absoluteGaloisGroupAbelianization K}
    {φE : Eˣ →* Field.absoluteGaloisGroupAbelianization E}
    (hK : IsLocalReciprocity K φK) (hE : IsLocalReciprocity E φE)
    (e : AlgebraicClosure E ≃ₐ[K] AlgebraicClosure K)
    (x : Eˣ) (σ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E)
    (hσ : (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization E) = φE x) :
    (QuotientGroup.mk (AlgEquiv.autCongr e (σ.restrictScalars K)) :
      Field.absoluteGaloisGroupAbelianization K) = φK (normUnits K E x) := by
  let c : (AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) →*
      (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) :=
    (AlgEquiv.autCongr e).toMonoidHom.comp
      (AlgEquiv.restrictScalarsHom (S := E) (A := AlgebraicClosure E) K)
  have hc : Continuous c :=
    (semilinear_conjugation_continuous (RingEquiv.refl K) e.toRingEquiv
      e.commutes (AlgEquiv.autCongr e).toMonoidHom (fun _ => rfl)).comp
        (restrictScalarsHom_continuous K E (AlgebraicClosure E))
  let r : Field.absoluteGaloisGroupAbelianization E →*
      Field.absoluteGaloisGroupAbelianization K := topologicalAbelianizationMap c hc
  have key : ∀ (u : Eˣ) (hu : (u : E) ∈ 𝒪[E]),
      Irreducible (⟨(u : E), hu⟩ : 𝒪[E]) → r (φE u) = φK (normUnits K E u) := by
    intro u hu hirr
    obtain ⟨τ, hτ⟩ := QuotientGroup.mk_surjective (φE u)
    change AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E at τ
    have hτr : (QuotientGroup.mk (c τ) : Field.absoluteGaloisGroupAbelianization K) =
        r (φE u) := by rw [← hτ]; rfl
    refine abelianizedGalois_eq_of_cyclotomic K ?_ (Nat.card 𝓀[E])
      Finite.one_lt_card ?_ ?_
    · intro V hV huV
      obtain ⟨L, hfin, hgal, hcomm, hLV⟩ := absoluteAbelianOpenSubgroupField K hV
      letI := hfin
      letI := hgal
      letI : IsAbelianGalois K L := { is_comm := ⟨hcomm⟩ }
      rw [← hLV] at huV
      obtain ⟨ω, hω, hωu⟩ := huV
      have hquot : (QuotientGroup.mk (c τ) : Field.absoluteGaloisGroupAbelianization K) =
          QuotientGroup.mk ω := hτr.trans hωu.symm
      have hrestrict := congrArg (absoluteAbelianRestriction K L) hquot
      rw [absoluteAbelianRestriction_mk, absoluteAbelianRestriction_mk] at hrestrict
      have hωfix : AlgEquiv.restrictNormalHom L ω = 1 := by
        change ω ∈ (AlgEquiv.restrictNormalHom (F := K) L).ker
        rwa [IntermediateField.restrictNormalHom_ker]
      have hnorm := hE.norm_mem_normRange_of_restriction_eq_one K E e L u τ hτ
        (hrestrict.trans hωfix)
      have hn : normUnits K E u ∈ Subgroup.comap φK
          (Subgroup.map
            (QuotientGroup.mk' (commutator (Field.absoluteGaloisGroup K)).topologicalClosure)
            L.fixingSubgroup) := by
        rw [hK.normKernel L hcomm]
        exact hnorm
      rwa [hLV] at hn
    · intro m hm α hα ζ hζ
      have hm0 : m ≠ 0 := by
        rintro rfl
        have hq : 1 < Nat.card 𝓀[E] := Finite.one_lt_card
        rw [Nat.coprime_zero_left] at hm
        omega
      rw [abelianizedGalois_eq_on_roots_of_mk_eq K (hα.trans hτr.symm) hm0 hζ]
      change e ((τ : AlgebraicClosure E ≃ₐ[E] AlgebraicClosure E) (e.symm ζ)) =
        ζ ^ Nat.card 𝓀[E]
      have hroot : (e.symm ζ) ^ m = 1 := by rw [← map_pow, hζ, map_one]
      rw [hE.frobenius u hu hirr τ hτ m hm (e.symm ζ) hroot, map_pow,
        e.apply_symm_apply]
    · intro m hm α hα ζ hζ
      let f := Module.finrank 𝓀[K] 𝓀[E]
      have hf : 0 < f := Module.finrank_pos
      have hcard : Nat.card 𝓀[E] = Nat.card 𝓀[K] ^ f :=
        Module.natCard_eq_pow_finrank
      have hmK : Nat.Coprime m (Nat.card 𝓀[K]) :=
        hm.coprime_dvd_right (by rw [hcard]; exact dvd_pow_self _ hf.ne')
      have hval : normalizedValuation K (normUnits K E u) = (f : ℤ) := by
        change normalizedValuation K (Units.map (Algebra.norm K) u) = (f : ℤ)
        rw [normalizedValuation_norm_of_isSeparable K E,
          normalizedValuation_irreducible E ⟨(u : E), hu⟩ hirr u rfl, mul_one,
          inertiaDeg_eq_finrank_residueField K E]
      rw [hK.frobenius_of_normalizedValuation_eq_nat K (normUnits K E u) f hval
        α hα m hmK ζ hζ, ← hcard]
  have hmap : r.comp φE = φK.comp (normUnits K E) := by
    ext u
    have hu : u ∈ Subgroup.closure
        {v : Eˣ | ∃ hv : (v : E) ∈ 𝒪[E], Irreducible (⟨(v : E), hv⟩ : 𝒪[E])} := by
      rw [uniformizerUnits_generate E]
      trivial
    induction hu using Subgroup.closure_induction with
    | mem u hu => obtain ⟨hu, hirr⟩ := hu; exact key u hu hirr
    | one => simp only [map_one]
    | mul a b _ _ ha hb => simp only [map_mul, ha, hb]
    | inv a _ ha => simp only [map_inv, ha]
  calc
    (QuotientGroup.mk (c σ) : Field.absoluteGaloisGroupAbelianization K) =
        r (QuotientGroup.mk σ) := rfl
    _ = r (φE x) := congrArg r hσ
    _ = φK (normUnits K E x) := DFunLike.congr_fun hmap x

end

end Atlas.Knowledge
