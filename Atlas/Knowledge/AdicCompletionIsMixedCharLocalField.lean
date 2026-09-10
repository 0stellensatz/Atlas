import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# adic completion as mixed-characteristic local field

The completion of a number field at a finite place, carried into the local layer's signature: the
canonical valuative relation induced by the `v`-adic valuation is installed as an instance, pinned
to that valuation by its compatibility certificate, and the field is proved to be a
mixed-characteristic local field. The three obligations of the carrier — that the `Valued` topology
is the valuative one, that the valuation is nontrivial, and local compactness — are all discharged,
the last through Serre's Proposition 1: a complete discretely valued field is locally compact if and
only if its residue field is finite, and the residue field of the completion is that of `𝓞 K` at
`v`. This item is the junction the reciprocity phase crosses every time it evaluates a local notion
at a place of a global field; without it, `Atlas.Knowledge.IsLocalHilbertSymbol` cannot even be
stated at a completion. Everything here is proved.

## Main definitions

* `adicCompletionValuativeRel`, `adicCompletionValuedCompatible` — the canonical
  `ValuativeRel` on `v.adicCompletion K` and its pinning to `Valued.v`.
* `AdicCompletionIsMixedCharLocalField.integerEquiv` — the layer's integer ring of the
  completion is Mathlib's `adicCompletionIntegers`.

## Main statements

* `adicCompletion_charZero` — characteristic zero; proved.
* `adicCompletion_isValuativeTopology` — the `Valued` topology is the valuative one; proved.
* `adicCompletion_isNontrivial` — the valuation is nontrivial; proved.
* `AdicCompletionIsMixedCharLocalField.integer_eq`,
  `AdicCompletionIsMixedCharLocalField.mem_maximalIdeal_iff` — the layer's integers and their
  maximal ideal read in Mathlib's spelling; proved.
* `AdicCompletionIsMixedCharLocalField.finite_residueField_adicCompletionIntegers` — the residue
  map from `𝓞 K` is onto the residue field of the completion, which is therefore finite; proved.
* `AdicCompletionIsMixedCharLocalField.finite_residueField` — the same in the layer's spelling;
  proved.
* `adicCompletion_locallyCompactSpace` — local compactness; proved.
* `adicCompletion_isMixedCharLocalField` — the local-field certificate; proved.

## Implementation notes

The valuative relation is `ValuativeRel.ofValuation` applied to the completion's `Valued` structure,
and the `Valuation.Compatible` instance is what pins the relation to the `v`-adic valuation rather
than an arbitrary one — together they are the canonical bridge Mathlib's own
`Valued`-to-`ValuativeRel` migration uses, so no orphan structure is invented. At the pinned
Mathlib, `IsNonarchimedeanLocalField` ships with no instance at all — the `ℚ_[p]` model is Atlas's
own, `Atlas.Knowledge.PadicIsMixedCharLocalField` — and none of its three components synthesizes for
the completion; for `IsValuativeTopology`, Mathlib's own TODO at
`Mathlib/NumberTheory/Padics/HeightOneSpectrum.lean:51` says as much. The valuative topology is
nonetheless one line: the `Valued` axiom `Valued.mem_nhds_zero` is stated, at the pin, in exactly
the form `IsValuativeTopology.of_mem_nhds_zero_iff_vle` consumes, so the general
`Valued`-to-`IsValuativeTopology` bridge is not absent, only unregistered. Nontriviality reads a
uniformizer of `K` through `HeightOneSpectrum.adicCompletion.valued_coe`. Local compactness is
Serre's Proposition 1 in Mathlib's form,
`properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField` in the
`Valued.integer` namespace, whose three inputs are completeness and the discrete valuation ring,
both Mathlib instances, and the finiteness of the residue field, which is the content: the residue
map from `𝓞 K` to the residue field of the completion is surjective, because `K` is dense in the
completion, an element of `K` close to an integer of the completion is `v`-integral, hence `a / s`
with `s ∉ v.asIdeal` by Mathlib's `exists_primeCompl_mul_eq_of_integer`, and `s` is invertible
modulo `v.asIdeal` by `Ideal.IsMaximal.exists_inv`. The layer's `𝓀[v.adicCompletion K]` is
transported along `AdicCompletionIsMixedCharLocalField.integerEquiv`, an equality of subrings of the
completion read through `IsLocalRing.ResidueField.mapEquiv`. The source builds the same certificate
over its normed completion from its own machinery
(`GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/Construction.lean:294`, certificate at
`:305`); Atlas proves it on Mathlib's `Valued` completion instead.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open NumberField IsDedekindDomain ValuativeRel
open scoped WithZero Topology

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

/-- The canonical valuative relation on the completion at a finite place, induced by the
`v`-adic valuation ([Serre 1979, Chap. II, §1, p.27][Serre1979]; Yamaguchi 2026,
`GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/Construction.lean:294`). -/
noncomputable instance adicCompletionValuativeRel : ValuativeRel (v.adicCompletion K) :=
  ValuativeRel.ofValuation (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

/-- The valuative relation is the one of the `v`-adic valuation — the compatibility
certificate that keeps the instance canonical. -/
instance adicCompletionValuedCompatible :
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).Compatible :=
  Valuation.Compatible.ofValuation _

/-- The completion of a number field has characteristic zero, through the rational algebra
structure. -/
instance adicCompletion_charZero : CharZero (v.adicCompletion K) :=
  charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion K)).injective

/-- The `Valued` topology of the completion is the valuative one: the `Valued` axiom is the
constructor's hypothesis verbatim ([Serre 1979, Chap. II, §1, p.27][Serre1979]). -/
instance adicCompletion_isValuativeTopology : IsValuativeTopology (v.adicCompletion K) :=
  IsValuativeTopology.of_mem_nhds_zero_iff_vle (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
    fun {_} => Valued.mem_nhds_zero

/-- The valuation of the completion is nontrivial: a uniformizer of `K` has value
`WithZero.exp (-1)` ([Serre 1979, Chap. II, §1, p.27][Serre1979]). -/
instance adicCompletion_isNontrivial : ValuativeRel.IsNontrivial (v.adicCompletion K) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hv : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (π : v.adicCompletion K) =
      WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.adicCompletion.valued_coe, hπ]
  refine ⟨valuation (v.adicCompletion K) (π : v.adicCompletion K), ?_, ?_⟩
  · rw [Ne, (isEquiv (valuation _) (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).eq_zero, hv]
    exact WithZero.exp_ne_zero
  · intro h
    rw [(isEquiv (valuation _) (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).eq_one_iff_eq_one,
      hv] at h
    exact absurd h (by simp)

namespace AdicCompletionIsMixedCharLocalField

/-- The layer's integer ring of the completion is Mathlib's `adicCompletionIntegers`, as
subrings of the completion. -/
theorem integer_eq :
    (valuation (v.adicCompletion K)).integer = (v.adicCompletionIntegers K).toSubring := by
  ext x
  rw [Valuation.mem_integer_iff,
    (isEquiv (valuation _) (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)).le_one_iff_le_one]
  exact Iff.rfl

/-- The two integer rings of the completion, as one ring. -/
noncomputable def integerEquiv : 𝒪[v.adicCompletion K] ≃+* v.adicCompletionIntegers K :=
  RingEquiv.subringCongr (integer_eq K v)

/-- Membership in the maximal ideal of the completion's integers is valuation below one. -/
theorem mem_maximalIdeal_iff (x : v.adicCompletionIntegers K) :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (x : v.adicCompletion K) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
  exact Valuation.Integer.not_isUnit_iff_valuation_lt_one

/-- The residue field of the completion is finite: the residue map from `𝓞 K` is onto it,
because `K` is dense in the completion and a `v`-integral element of `K` is `a / s` with `s`
invertible modulo `v` ([Serre 1979, Chap. II, §1, p.27][Serre1979]). -/
theorem finite_residueField_adicCompletionIntegers :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  classical
  set A := v.adicCompletionIntegers K
  have hval : ∀ r : 𝓞 K, (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
      (algebraMap (𝓞 K) A r : v.adicCompletion K) = v.valuation K (algebraMap (𝓞 K) K r) := by
    intro r
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.adicCompletion.valued_coe]
  set φ : 𝓞 K →+* IsLocalRing.ResidueField A :=
    (IsLocalRing.residue A).comp (algebraMap (𝓞 K) A) with hφ
  have hker : ∀ r ∈ v.asIdeal, φ r = 0 := by
    intro r hr
    rw [hφ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff, hval,
      HeightOneSpectrum.valuation_lt_one_iff_mem]
    exact hr
  let ψ : 𝓞 K ⧸ v.asIdeal →+* IsLocalRing.ResidueField A := Ideal.Quotient.lift v.asIdeal φ hker
  refine Finite.of_surjective ψ ?_
  intro z
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
  -- approximate `y` by an element of `K`
  have hN : {w : v.adicCompletion K | (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (w - y) < 1}
      ∈ 𝓝 (y : v.adicCompletion K) := by
    rw [Valued.mem_nhds]
    exact ⟨1, fun w hw => by simpa using hw⟩
  have hy : (y : v.adicCompletion K) ∈ closure (Set.range (algebraMap K (v.adicCompletion K))) := by
    rw [(HeightOneSpectrum.denseRange_algebraMap K v).closure_range]
    exact Set.mem_univ _
  obtain ⟨w, hw, k, rfl⟩ := mem_closure_iff_nhds.mp hy _ hN
  have hk : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) ((k : v.adicCompletion K) - y) < 1 := by
    simpa [HeightOneSpectrum.algebraMap_adicCompletion] using hw
  -- `k` is integral at `v`
  have hk1 : v.valuation K k ≤ 1 := by
    have h1 : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (k : v.adicCompletion K) ≤ 1 := by
      have := Valuation.map_add_le (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)
        hk.le (y.2 : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰) (y : v.adicCompletion K) ≤ 1)
      simpa using this
    rwa [HeightOneSpectrum.adicCompletion.valued_coe] at h1
  -- write `k = a / s` with `s ∉ v`
  obtain ⟨a, s, hs⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer (K := K) v k hk1
  -- invert `s` modulo `v`
  obtain ⟨s', i, hi, hsi⟩ := v.isMaximal.exists_inv s.2
  have hs' : (s : 𝓞 K) * s' - 1 ∈ v.asIdeal := by
    have h : (s : 𝓞 K) * s' - 1 = -i := by rw [← hsi]; ring
    rw [h]
    exact v.asIdeal.neg_mem hi
  refine ⟨Ideal.Quotient.mk v.asIdeal (a * s'), ?_⟩
  change φ (a * s') = IsLocalRing.residue A y
  rw [hφ, RingHom.comp_apply, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    mem_maximalIdeal_iff]
  -- `k - a s' = k (1 - s s')` has valuation below one
  have hkc : v.valuation K (k - algebraMap (𝓞 K) K (a * s')) < 1 := by
    have heq : k - algebraMap (𝓞 K) K (a * s') = k * algebraMap (𝓞 K) K (1 - (s : 𝓞 K) * s') := by
      rw [map_sub, map_one, map_mul, map_mul, ← hs]
      ring
    rw [heq, map_mul]
    have h1 : v.valuation K (algebraMap (𝓞 K) K (1 - (s : 𝓞 K) * s')) < 1 := by
      rw [HeightOneSpectrum.valuation_lt_one_iff_mem]
      have := v.asIdeal.neg_mem hs'
      rwa [neg_sub] at this
    calc v.valuation K k * v.valuation K (algebraMap (𝓞 K) K (1 - (s : 𝓞 K) * s'))
        ≤ 1 * v.valuation K (algebraMap (𝓞 K) K (1 - (s : 𝓞 K) * s')) :=
          mul_le_mul' hk1 le_rfl
      _ < 1 := by rw [one_mul]; exact h1
  have hcoe : ∀ x : K, algebraMap K (v.adicCompletion K) x = (x : v.adicCompletion K) := by
    intro x
    rw [HeightOneSpectrum.algebraMap_adicCompletion]
    rfl
  have hsplit : ((algebraMap (𝓞 K) A (a * s') - y : A) : v.adicCompletion K) =
      -(algebraMap K (v.adicCompletion K) (k - algebraMap (𝓞 K) K (a * s'))) +
        ((k : v.adicCompletion K) - y) := by
    rw [map_sub, hcoe, hcoe]
    change ((algebraMap (𝓞 K) A (a * s') : A) : v.adicCompletion K) - (y : v.adicCompletion K) = _
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
    ring
  rw [hsplit]
  refine Valuation.map_add_lt _ ?_ hk
  rw [Valuation.map_neg, hcoe, HeightOneSpectrum.adicCompletion.valued_coe]
  exact hkc

/-- The residue field of the completion, in the layer's spelling, is finite
([Serre 1979, Chap. II, §1, p.27][Serre1979]). -/
theorem finite_residueField : Finite 𝓀[v.adicCompletion K] := by
  haveI := finite_residueField_adicCompletionIntegers K v
  exact Finite.of_equiv _ (IsLocalRing.ResidueField.mapEquiv (integerEquiv K v)).symm.toEquiv

end AdicCompletionIsMixedCharLocalField

open Valued.integer in
/-- The completion of a number field at a finite place is locally compact: it is complete,
its integers form a discrete valuation ring, and its residue field is finite
([Serre 1979, Chap. II, §1, Prop. 1, p.27][Serre1979]). -/
instance adicCompletion_locallyCompactSpace : LocallyCompactSpace (v.adicCompletion K) := by
  haveI : Finite (IsLocalRing.ResidueField
      (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).integer) :=
    AdicCompletionIsMixedCharLocalField.finite_residueField_adicCompletionIntegers K v
  haveI : IsDiscreteValuationRing (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).integer :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  have hproper : ProperSpace (v.adicCompletion K) :=
    (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
      (K := v.adicCompletion K)).mpr ⟨inferInstance, inferInstance, inferInstance⟩
  infer_instance

/-- The completion of a number field at a finite place is a mixed-characteristic local field: the
`Valued` topology is the valuative one, the valuation is nontrivial, and the field is locally
compact by Serre's Proposition 1 — a complete discretely valued field is locally compact iff its
residue field is finite — with that residue field the finite one of `𝓞 K` at `v`
([Serre 1979, Chap. II, §1, Prop. 1, p.27][Serre1979]; Yamaguchi 2026,
`GlobalClassFieldTheory/Reciprocity/FinitePlaceArtin/Construction.lean:305`). -/
theorem adicCompletion_isMixedCharLocalField :
    IsMixedCharLocalField (v.adicCompletion K) := by
  exact {}

/-- The certificate, registered as an instance, so that local notions synthesize at every
finite place of a number field. -/
instance : IsMixedCharLocalField (v.adicCompletion K) :=
  adicCompletion_isMixedCharLocalField K v

end Atlas.Knowledge
