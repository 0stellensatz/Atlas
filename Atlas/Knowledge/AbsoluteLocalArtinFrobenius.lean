import Mathlib
import Atlas.Knowledge.AbsoluteAbelianRestriction
import Atlas.Knowledge.AbsoluteLocalArtinRestriction
import Atlas.Knowledge.CycloField
import Atlas.Knowledge.CycloFieldLowerRamificationGroupEqBot
import Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField
import Atlas.Knowledge.IsArithmeticFrobeniusApplyOfPowEqOne
import Atlas.Knowledge.IsFrobeniusNormalizedAbelianLocalArtinMonoidHom
import Atlas.Knowledge.NormalizedValuation

/-!
# absolute local Artin Frobenius normalization

The arithmetic normalization of the absolute local Artin homomorphism:
every lift to the absolute Galois group of the absolute Artin image of
a uniformizer acts on the roots of unity of order prime to the residue
cardinality `q` by `ζ ↦ ζ ^ q`. This is the `frobenius` field of
`Atlas.Knowledge.IsLocalReciprocity` at
`Atlas.Knowledge.absoluteLocalArtinMonoidHom`, stated verbatim, and the
last of the three fields the reciprocity engine (#104) discharges.

## Main statements

* `absoluteLocalArtinMonoidHom_frobenius` — every lift of the absolute
  Artin image of a uniformizer is the `q`-power map on the prime-to-`q`
  roots of unity; proved.

## Implementation notes

The chain runs entirely through merged items. An irreducible integer
unit has normalized valuation one
(`Atlas.Knowledge.normalizedValuation_irreducible`, at the unit's own
coercion); coprimality with `q > 1` manufactures `NeZero m`, which the
cyclotomic floor's abelianness instance asks for; the floor
`cycloField K m` contains the root of unity and has trivial inertia
(`Atlas.Knowledge.cycloField_lowerRamificationGroup_eq_bot`); the
restriction kernel of the floor is an open normal subgroup whose
dictionary field `F` is the floor up to a propositional equality, along
which membership and trivial inertia are transported as propositions;
at `F` the restriction identity of
`Atlas.Knowledge.AbsoluteLocalArtinRestriction` reads the lift as the
finite Artin image, which
`Atlas.Knowledge.isArithmeticFrobenius_abelianLocalArtinMonoidHom`
makes an arithmetic Frobenius and
`Atlas.Knowledge.IsArithmeticFrobenius.apply_of_pow_eq_one` evaluates
on the root; Mathlib's `AlgEquiv.restrictNormal_commutes` returns to
the algebraic closure. The valuative pack of `F` that the
Frobenius-normalization theorem carries is discharged inside the proof
from `Atlas.Knowledge.exists_extension_isMixedCharLocalField` and is
inert in the statement, as the #218 review recorded. Layer-original:
the source states no Frobenius property of its absolute map —
`absoluteLocalArtinMap` is consumed only inside
`LocalClassFieldTheory/Infinite/`, and no arithmetic-Frobenius
statement exists at its infinite level — and the field-level
`ζ ↦ ζ ^ q` reading has been the layer's own since the cyclotomic floor
(#219).

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer
  New York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

open ValuativeRel

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- **Every lift of the absolute Artin image of a uniformizer is the
`q`-power map on the prime-to-`q` roots of unity**,
`q = Nat.card 𝓀[K]`: the `frobenius` field of
`Atlas.Knowledge.IsLocalReciprocity` at the absolute local Artin
homomorphism ([Serre 1979, Chap. XIII, §4, pp.195–197][Serre1979];
[Milne 2020, Chap. I, §1, Thm. 1.1, p.20][MilneCFT]). -/
theorem absoluteLocalArtinMonoidHom_frobenius
    (u : Kˣ) (hu : (u : K) ∈ 𝒪[K]) (hirr : Irreducible (⟨(u : K), hu⟩ : 𝒪[K]))
    (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)
    (hσ : (QuotientGroup.mk (σ : Field.absoluteGaloisGroup K) :
        Field.absoluteGaloisGroupAbelianization K) = absoluteLocalArtinMonoidHom K u)
    (m : ℕ) (hm : Nat.Coprime m (Nat.card 𝓀[K]))
    (ζ : AlgebraicClosure K) (hζ : ζ ^ m = 1) : σ ζ = ζ ^ Nat.card 𝓀[K] := by
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hm
    omega
  haveI : NeZero m := ⟨hm0⟩
  have hval : normalizedValuation K u = 1 :=
    normalizedValuation_irreducible K ⟨(u : K), hu⟩ hirr u rfl
  set E := cycloField K m with hE
  set N := absoluteAbelianRestrictionKernel K E with hN
  set F := absoluteFiniteQuotientField K N with hF
  have hfield : F = E := absoluteFiniteQuotientField_restrictionKernel K E
  have hζE : ζ ∈ E := mem_cycloField K hm0 hζ
  have hζF : ζ ∈ F := hfield ▸ hζE
  have hbotE : lowerRamificationGroup K E 0 = ⊥ :=
    cycloField_lowerRamificationGroup_eq_bot K hm
  have hbotF : lowerRamificationGroup K F 0 = ⊥ := by
    rw [hfield]
    exact hbotE
  have hres : AlgEquiv.restrictNormalHom F σ = abelianLocalArtinMonoidHom K F u :=
    restrictNormalHom_absoluteLocalArtinMonoidHom_lift K N u σ hσ
  obtain ⟨vF, tF, hVF, _, hF'⟩ := exists_extension_isMixedCharLocalField K F
  letI := vF
  letI := tF
  letI := hVF
  letI := hF'
  have hfrob : IsArithmeticFrobenius K F (abelianLocalArtinMonoidHom K F u) :=
    isArithmeticFrobenius_abelianLocalArtinMonoidHom K F hbotF u hval
  have hζF' : (⟨ζ, hζF⟩ : F) ^ m = 1 := by
    ext
    simpa using hζ
  have hact : abelianLocalArtinMonoidHom K F u ⟨ζ, hζF⟩ = ⟨ζ, hζF⟩ ^ Nat.card 𝓀[K] :=
    hfrob.apply_of_pow_eq_one hm hζF'
  have hcomm :
      ((AlgEquiv.restrictNormalHom F σ ⟨ζ, hζF⟩ : F) : AlgebraicClosure K) = σ ζ :=
    AlgEquiv.restrictNormal_commutes σ F ⟨ζ, hζF⟩
  rw [← hcomm, hres, hact]
  simp

end

end Atlas.Knowledge
