import Mathlib
import Atlas.Knowledge.DecompositionResidueExactSequence
import Atlas.Knowledge.ExistsValuativeExtension
import Atlas.Knowledge.IntegerIsIntegralClosure
import Atlas.Knowledge.ResidueOfAlgebraicallyClosed

/-!
# absolute extension valuation of a local field

The canonical extension of a mixed-characteristic local field's valuation to
its algebraic closure, as a valuation subring: the integral closure of `𝒪[K]`.
On each finite subextension a Chevalley extension exists and its integer ring
is the integral closure of `𝒪[K]` there, so integrality is the valuation-ring
dichotomy in the limit — and it is manifestly Galois-stable, so the
decomposition group is the whole absolute Galois group with no uniqueness
theorem spent. The decomposition residue field is the finite residue field of
`K`, and the selected residue field is algebraically closed. This is the
extension-valuation choice `w | v` of the reciprocity engine's local-side
instantiation (#104).

## Main definitions

* `localAbsoluteValuationSubring` — the integral closure of `𝒪[K]` in the
  algebraic closure, as a valuation subring.
* `localBaseResidueEquivDecompositionResidue` — `𝓀[K]` is the decomposition
  residue field.

## Main statements

* `localAbsoluteDecompositionGroup_eq_top` — every automorphism preserves the
  valuation ring; proved.
* `localAbsoluteValuationSubring_pullback` — the pullback to `K` is `𝒪[K]`;
  proved.
* `localAbsoluteValuationSubring_restrict` — the restriction to any finite
  subextension is its canonical integer ring; proved.

## Implementation notes

The source chooses a Chevalley extension to the algebraic closure, pulls it
back to the separable closure, and pins the decomposition group by Henselian
uniqueness of the finite-level extension valuations. Atlas takes the integral
closure of `𝒪[K]` as the carrier instead: on a finite subextension
`Atlas.Knowledge.exists_valuativeExtension` supplies a compatible valuation
whose integers are the integral closure of `𝒪[K]` by
`Atlas.Knowledge.mem_integer_iff_isIntegral`, which gives the dichotomy — and
Galois stability is integrality transport, so
`localAbsoluteDecompositionGroup_eq_top` needs no uniqueness input, and the
source's `HasExtension` packaging of the chosen rings goes with it — Mathlib's
class serves at the finite level inside the dichotomy. Mixed characteristic
makes the separable closure the algebraic closure, so the source's purely
inseparable descent to the separable closure and its residue comparison
vanish, and the source's separable/absolute pair of chosen rings collapses to
the single absolute object. The subring-to-decomposition-field step is the
general `Atlas.Knowledge.residueFieldEquivDecompositionResidueOfEqTop` of the
exact-sequence item, specialized at the pullback identity — the source's
private plumbing has no local content; the naturality square stays public for
the fixed-field local data downstream, which reads residue degrees through
it.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

noncomputable section

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- **The absolute extension valuation ring** of a mixed-characteristic local
field: the integral closure of `𝒪[K]` in the algebraic closure, a valuation
subring because on each finite subextension it is the integer ring of a
Chevalley extension of the valuation ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:52` and `:80`]
[Yamaguchi2026]). -/
def localAbsoluteValuationSubring : ValuationSubring (AlgebraicClosure K) where
  toSubring := (integralClosure 𝒪[K] (AlgebraicClosure K)).toSubring
  mem_or_inv_mem' x := by
    let E : IntermediateField K (AlgebraicClosure K) :=
      IntermediateField.adjoin K {x}
    letI : FiniteDimensional K E :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
    obtain ⟨_, _⟩ := exists_valuativeExtension K E
    letI : IsScalarTower 𝒪[K] E (AlgebraicClosure K) :=
      IsScalarTower.of_algebraMap_eq fun r => rfl
    have hup : ∀ z : E, IsIntegral 𝒪[K] z →
        (z : AlgebraicClosure K) ∈ integralClosure 𝒪[K] (AlgebraicClosure K) :=
      fun z hz =>
        IsIntegral.map (IsScalarTower.toAlgHom 𝒪[K] E (AlgebraicClosure K)) hz
    let xE : E := ⟨x, IntermediateField.mem_adjoin_simple_self K x⟩
    rcases le_total (valuation E xE) 1 with h | h
    · exact Or.inl (hup xE ((mem_integer_iff_isIntegral K E).mp h))
    · refine Or.inr ?_
      have hinv : xE⁻¹ ∈ 𝒪[E] := by
        change valuation E xE⁻¹ ≤ 1
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ h
      have := hup xE⁻¹ ((mem_integer_iff_isIntegral K E).mp hinv)
      simpa using this

/-- Membership in the absolute valuation ring is integrality over `𝒪[K]`. -/
theorem mem_localAbsoluteValuationSubring_iff {x : AlgebraicClosure K} :
    x ∈ localAbsoluteValuationSubring K ↔ IsIntegral 𝒪[K] x :=
  Iff.rfl

/-- **The restriction to any finite subextension is its canonical integer
ring**, for every compatible valuative structure — the choice-independence the
source obtains from Henselian uniqueness, here the integrality reading of the
carrier ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:108`]
[Yamaguchi2026]). -/
theorem localAbsoluteValuationSubring_restrict
    (E : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K E]
    [ValuativeRel E] [ValuativeExtension K E] (z : E) :
    (z : AlgebraicClosure K) ∈ localAbsoluteValuationSubring K ↔ z ∈ 𝒪[E] := by
  letI : IsScalarTower 𝒪[K] E (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  rw [mem_localAbsoluteValuationSubring_iff, mem_integer_iff_isIntegral K E]
  exact isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[K] E (AlgebraicClosure K))
    (IntermediateField.val E).injective (x := z)

/-- **The pullback of the absolute valuation ring to `K` is `𝒪[K]`**: an
element of `K` integral over `𝒪[K]` already lies in it ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:60`]
[Yamaguchi2026]). -/
theorem localAbsoluteValuationSubring_pullback (x : K) :
    algebraMap K (AlgebraicClosure K) x ∈ localAbsoluteValuationSubring K ↔
      x ∈ 𝒪[K] := by
  rw [mem_localAbsoluteValuationSubring_iff]
  constructor
  · intro h
    exact (Valuation.integer.integers (valuation K)).mem_of_integral
      ((isIntegral_algHom_iff (IsScalarTower.toAlgHom 𝒪[K] K (AlgebraicClosure K))
        (algebraMap K (AlgebraicClosure K)).injective (x := x)).mp h)
  · intro h
    exact (isIntegral_algHom_iff
      (IsScalarTower.toAlgHom 𝒪[K] K (AlgebraicClosure K))
      (algebraMap K (AlgebraicClosure K)).injective (x := x)).mpr
        (isIntegral_algebraMap (x := (⟨x, h⟩ : 𝒪[K])))

/-- **Every automorphism preserves the absolute valuation ring**: integrality
over `𝒪[K]` is Galois-stable, so the decomposition group is everything — the
source pins this with Henselian uniqueness, Atlas reads it off the carrier
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:150`]
[Yamaguchi2026]). -/
theorem localAbsoluteDecompositionGroup_eq_top :
    decompositionGroup K (localAbsoluteValuationSubring K) = ⊤ := by
  apply top_unique
  intro sigma _hsigma
  rw [mem_decompositionGroup_iff_apply_mem]
  intro x
  rw [mem_localAbsoluteValuationSubring_iff, mem_localAbsoluteValuationSubring_iff]
  constructor
  · intro h
    simpa using
      IsIntegral.map (AlgEquiv.restrictScalars 𝒪[K] sigma.symm).toAlgHom h
  · intro h
    exact IsIntegral.map (AlgEquiv.restrictScalars 𝒪[K] sigma).toAlgHom h

/-- **The finite residue field of `K` is the decomposition residue field** of
the absolute valuation ring ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:214`]
[Yamaguchi2026]). -/
def localBaseResidueEquivDecompositionResidue :
    𝓀[K] ≃+*
      decompositionResidueField K (localAbsoluteValuationSubring K) :=
  residueFieldEquivDecompositionResidueOfEqTop K
    (localAbsoluteValuationSubring K)
    (ValuativeRel.valuation K).valuationSubring
    (by
      ext x
      exact localAbsoluteValuationSubring_pullback K x)
    (localAbsoluteDecompositionGroup_eq_top K)

/-- The base-residue comparison is the literal reduction into the selected
residue field on representatives — the scalar square used when transporting
residue degrees back to the residue fields of local extensions
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:226`]
[Yamaguchi2026]). -/
theorem localBaseResidueEquivDecompositionResidue_algebraMap (x : 𝒪[K]) :
    algebraMap
        (decompositionResidueField K (localAbsoluteValuationSubring K))
        (selectedResidueField (localAbsoluteValuationSubring K))
        (localBaseResidueEquivDecompositionResidue K
          (IsLocalRing.residue 𝒪[K] x)) =
      IsLocalRing.residue (localAbsoluteValuationSubring K)
        (⟨algebraMap K (AlgebraicClosure K) (x : K),
          (localAbsoluteValuationSubring_pullback K (x : K)).2
            x.property⟩ : localAbsoluteValuationSubring K) := by
  rfl

/-- **The decomposition residue field is finite** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:240`]
[Yamaguchi2026]). -/
instance localDecompositionResidueFinite :
    Finite (decompositionResidueField K (localAbsoluteValuationSubring K)) :=
  Finite.of_equiv 𝓀[K]
    (localBaseResidueEquivDecompositionResidue K).toEquiv

/-- The finite decomposition residue field, canonically enumerated
([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:250`]
[Yamaguchi2026]). -/
instance localDecompositionResidueFintype :
    Fintype (decompositionResidueField K (localAbsoluteValuationSubring K)) :=
  Fintype.ofFinite _

/-- **The selected residue field is algebraically closed** — in mixed
characteristic directly by `Atlas.Knowledge.valuationSubring_residueField_isAlgClosed`,
with the source's purely inseparable descent gone ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/LocalResidueDatum.lean:256`]
[Yamaguchi2026]). -/
instance localSelectedResidueIsAlgClosed :
    IsAlgClosed (selectedResidueField (localAbsoluteValuationSubring K)) :=
  valuationSubring_residueField_isAlgClosed (localAbsoluteValuationSubring K)

end

end Atlas.Knowledge
