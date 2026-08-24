import Mathlib
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.DeepUnitGroup
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.ResidueCharacteristic

/-!
# finite-index subgroups of the unit group

Every finite-index subgroup of the multiplicative group of a mixed-characteristic local field
is open. This is the characteristic-zero half of a dichotomy — in equal characteristic `Kˣ`
has finite-index subgroups that are not even closed — and it is load-bearing for the
reciprocity phase: it is what identifies Mathlib's profinite completion of `Kˣ`, taken
against all finite-index normal subgroups, with the completion against the open ones that
the classical statement of `Atlas.Knowledge.IsLocalReciprocity.unitsCompletion_continuousMulEquiv`
means. The repository read alongside does not prove it: its completion comparison takes
exactly this statement as an undischarged hypothesis
(`LocalClassFieldTheory/Infinite/AbstractProfiniteCompletionComparison.lean:298`).

## Main statements

* `unitsFiniteIndexOpen` — a finite-index subgroup of `Kˣ` is open; proved.

## Implementation notes

A finite-index subgroup of the abelian group `Kˣ` contains the power subgroup `(Kˣ) ^ n` for
`n` its index, so the theorem reduces to the `n`-th powers of some open subgroup filling an
open subgroup. Milne reaches this through Newton's lemma applied to `X ^ m - a`; the proof
here instead runs through the layer's own deep unit groups: on a deep level
`Atlas.Knowledge.deepUnitGroup_continuousMulEquiv` identifies `U i (K)` with
`(ℤ_p) ^ d` topologically, where the `n`-th powers are the sublattice `n ⬝ (ℤ_p) ^ d` — a
span of nonzero elements in each coordinate, open because nonzero ideals of `ℤ_[p]` are
ideal powers of `p`, hence closed balls of nonzero radius. The image of that sublattice in
`Kˣ` is then an open subgroup inside `(Kˣ) ^ n`, and a subgroup above an open subgroup is
open. The openness of the levels `U i (K)` themselves, proved here privately, is the
ultrametric fact that closed balls are open; it stays private until a second consumer
appears.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/- Closed balls about the origin of nonzero radius are open: the ultrametric inequality keeps
the basic neighborhood of any member inside the ball. -/
private theorem isOpen_valuation_le {γ : ValueGroupWithZero K} (hγ : γ ≠ 0) :
    IsOpen {y : K | valuation K y ≤ γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  refine (IsValuativeTopology.hasBasis_nhds' x).mem_iff.mpr ⟨γ, hγ, fun y hy => ?_⟩
  calc valuation K y = valuation K ((y - x) + x) := by rw [sub_add_cancel]
  _ ≤ max (valuation K (y - x)) (valuation K x) := Valuation.map_add _ _ _
  _ ≤ γ := max_le (le_of_lt hy) hx

/- The higher unit group is the preimage in `Kˣ` of a translated closed ball, hence open:
its members are the units congruent to `1` modulo the `i`-th ideal power, and that congruence
reads as a valuation inequality on `x - 1`. -/
private theorem higherUnitGroup_isOpen (i : ℕ+) :
    IsOpen (higherUnitGroup K i : Set Kˣ) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[K])
  have hϖ0 : (ϖ : K) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  have hγ : valuation K ((ϖ : K) ^ (i : ℕ)) ≠ 0 := by
    simp [hϖ0]
  have hmem : ∀ y : K, (∃ m : (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]), (m : K) = y) ↔
      valuation K y ≤ valuation K ((ϖ : K) ^ (i : ℕ)) := by
    intro y
    constructor
    · rintro ⟨⟨m, hm⟩, rfl⟩
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hm
      obtain ⟨c, hc⟩ := hm
      calc valuation K (m : K) = valuation K ((ϖ ^ (i : ℕ) * c : ↥𝒪[K]) : K) := by rw [hc]
      _ = valuation K ((ϖ : K) ^ (i : ℕ)) * valuation K (c : K) := by push_cast; rw [map_mul]
      _ ≤ valuation K ((ϖ : K) ^ (i : ℕ)) :=
          mul_le_of_le_one_right' ((Valuation.mem_integer_iff _ _).mp c.2)
    · intro hy
      have hy1 : valuation K y ≤ 1 := by
        refine hy.trans ?_
        rw [show ((ϖ : K) ^ (i : ℕ)) = (((ϖ ^ (i : ℕ) : ↥𝒪[K])) : K) by push_cast; rfl]
        exact (Valuation.mem_integer_iff _ _).mp (ϖ ^ (i : ℕ)).2
      have hdvd : (ϖ ^ (i : ℕ)) ∣ (⟨y, (Valuation.mem_integer_iff _ _).mpr hy1⟩ : ↥𝒪[K]) := by
        refine (Valuation.integer.integers (v := valuation K)).le_iff_dvd.mp ?_
        have h1 : (algebraMap ↥𝒪[K] K)
            (⟨y, (Valuation.mem_integer_iff _ _).mpr hy1⟩ : ↥𝒪[K]) = y := rfl
        have h2 : (algebraMap ↥𝒪[K] K) (ϖ ^ (i : ℕ)) = (ϖ : K) ^ (i : ℕ) := by
          rfl
        rw [h1, h2]
        exact hy
      refine ⟨⟨(⟨y, (Valuation.mem_integer_iff _ _).mpr hy1⟩ : ↥𝒪[K]), ?_⟩, rfl⟩
      rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
        Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hdvd
  have hset : (higherUnitGroup K i : Set Kˣ) =
      (Units.val : Kˣ → K) ⁻¹' {y : K | valuation K (y - 1) ≤
        valuation K ((ϖ : K) ^ (i : ℕ))} := by
    ext x
    constructor
    · rintro ⟨m, hm⟩
      simp only [Set.mem_preimage, Set.mem_setOf_eq]
      rw [← hm]
      exact (hmem _).mp ⟨m, by ring⟩
    · intro hx
      obtain ⟨m, hm⟩ := (hmem ((x : K) - 1)).mpr hx
      exact ⟨m, by rw [hm]; ring⟩
  rw [hset]
  refine IsOpen.preimage Units.continuous_val ?_
  have : {y : K | valuation K (y - 1) ≤ valuation K ((ϖ : K) ^ (i : ℕ))} =
      (fun y : K => y - 1) ⁻¹' {y : K | valuation K y ≤ valuation K ((ϖ : K) ^ (i : ℕ))} :=
    rfl
  rw [this]
  exact IsOpen.preimage (by fun_prop) (isOpen_valuation_le K hγ)

/- Nonzero natural spans in `ℤ_[p]` are open: every nonzero ideal is a power of `p`, and the
power spans are closed balls of nonzero radius. -/
private theorem isOpen_span_natCast (p : ℕ) [Fact p.Prime] {n : ℕ} (hn : n ≠ 0) :
    IsOpen ((Ideal.span {(n : ℤ_[p])} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
  have hne : (Ideal.span {(n : ℤ_[p])} : Ideal ℤ_[p]) ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  obtain ⟨k, hk⟩ := PadicInt.ideal_eq_span_pow_p hne
  rw [hk]
  have hball : ((Ideal.span {(p : ℤ_[p]) ^ k} : Ideal ℤ_[p]) : Set ℤ_[p]) =
      Metric.closedBall 0 ((p : ℝ) ^ (-(k : ℤ))) := by
    ext x
    rw [Metric.mem_closedBall, dist_zero_right, SetLike.mem_coe,
      ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [hball]
  refine IsUltrametricDist.isOpen_closedBall _ ?_
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  positivity

/- The `n`-multiples of the free additive model fill an open set: coordinatewise they are
the span of `n`, and a finite product of opens is open. -/
private theorem isOpen_nsmul_range (p : ℕ) [Fact p.Prime] (d : ℕ) {n : ℕ} (hn : n ≠ 0) :
    IsOpen (Set.range fun f : Fin d → ℤ_[p] => n • f) := by
  have hset : Set.range (fun f : Fin d → ℤ_[p] => n • f) =
      Set.pi Set.univ fun _ : Fin d =>
        ((Ideal.span {(n : ℤ_[p])} : Ideal ℤ_[p]) : Set ℤ_[p]) := by
    ext g
    rw [Set.mem_univ_pi]
    constructor
    · rintro ⟨f, rfl⟩ j
      exact SetLike.mem_coe.mpr (Ideal.mem_span_singleton.mpr
        ⟨f j, by simp [nsmul_eq_mul]⟩)
    · intro h
      choose c hc using fun j => Ideal.mem_span_singleton.mp (SetLike.mem_coe.mp (h j))
      exact ⟨c, funext fun j => by simp [nsmul_eq_mul, hc j]⟩
  rw [hset]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_span_natCast p hn

/- The `n`-th powers of the free model fill an open set: they are the preimage under the
additive reading of the `n`-multiples. -/
private theorem isOpen_powRange (p : ℕ) [Fact p.Prime] (d : ℕ) {n : ℕ} (hn : n ≠ 0) :
    IsOpen (((powMonoidHom n :
        Multiplicative (Fin d → ℤ_[p]) →* Multiplicative (Fin d → ℤ_[p])).range :
      Subgroup (Multiplicative (Fin d → ℤ_[p]))) : Set (Multiplicative (Fin d → ℤ_[p]))) := by
  have hset : (((powMonoidHom n :
        Multiplicative (Fin d → ℤ_[p]) →* Multiplicative (Fin d → ℤ_[p])).range :
      Subgroup (Multiplicative (Fin d → ℤ_[p]))) : Set (Multiplicative (Fin d → ℤ_[p]))) =
      ⇑Multiplicative.toAdd ⁻¹' (Set.range fun f : Fin d → ℤ_[p] => n • f) := by
    ext z
    simp only [SetLike.mem_coe, MonoidHom.mem_range, powMonoidHom_apply, Set.mem_preimage,
      Set.mem_range]
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨Multiplicative.toAdd w, (toAdd_pow w n).symm⟩
    · rintro ⟨f, hf⟩
      refine ⟨Multiplicative.ofAdd f, Multiplicative.toAdd.injective ?_⟩
      rw [toAdd_pow, toAdd_ofAdd]
      exact hf
  rw [hset]
  exact (isOpen_nsmul_range p d hn).preimage continuous_toAdd

/-- **Finite-index subgroups of the unit group are open**: in mixed characteristic, a
subgroup of `Kˣ` of finite index `n` contains the `n`-th powers, and already the `n`-th
powers of a deep unit level fill an open subgroup — on the free `ℤ_p`-model of
`Atlas.Knowledge.deepUnitGroup_continuousMulEquiv` they are a coordinatewise span, open
because nonzero ideals of `ℤ_[p]` are closed balls. False in equal characteristic, which is
why the mixed-characteristic carrier is load-bearing
([Milne 2020, Chap. I, §1, 1.7, p.22][MilneCFT];
hypothesized and left undischarged by the source at
[Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbstractProfiniteCompletionComparison.lean:298`]
[Yamaguchi2026]). -/
theorem unitsFiniteIndexOpen (U : Subgroup Kˣ) (hU : U.FiniteIndex) :
    IsOpen (U : Set Kˣ) := by
  set n := U.index with hndef
  have hn : n ≠ 0 := hU.index_ne_zero
  -- a deep level for the free model
  set p := residueCharacteristic K with hpdef
  haveI : Fact p.Prime := ⟨residueCharacteristic_prime K⟩
  set i : ℕ+ := ⟨absoluteRamificationIndex K + 1, Nat.succ_pos _⟩ with hidef
  have hi : absoluteRamificationIndex K < (p - 1) * (i : ℕ) := by
    have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
    have h1 : (i : ℕ) = absoluteRamificationIndex K + 1 := rfl
    calc absoluteRamificationIndex K < (i : ℕ) := by omega
    _ = 1 * (i : ℕ) := (one_mul _).symm
    _ ≤ (p - 1) * (i : ℕ) := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨e⟩ := deepUnitGroup_continuousMulEquiv K p rfl i hi
  -- the `n`-th powers of the deep level, as a subgroup of `Kˣ`
  set S : Subgroup ↥(higherUnitGroup K i) :=
    (powMonoidHom n : ↥(higherUnitGroup K i) →* ↥(higherUnitGroup K i)).range with hSdef
  set T : Subgroup Kˣ := Subgroup.map (higherUnitGroup K i).subtype S with hTdef
  -- they land in `U`, whose index divides every exponent
  have hTle : T ≤ U := by
    rintro x hx
    rw [hTdef, Subgroup.mem_map] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    rw [hSdef, MonoidHom.mem_range] at hs
    obtain ⟨y, rfl⟩ := hs
    rw [powMonoidHom_apply]
    have : ((higherUnitGroup K i).subtype (y ^ n) : Kˣ) = ((y : Kˣ)) ^ n := rfl
    rw [this]
    exact Subgroup.pow_index_mem U (y : Kˣ)
  -- and they are open: the free model's power range pulled back along the level's topology
  have hSopen : IsOpen (S : Set ↥(higherUnitGroup K i)) := by
    have hpre : (S : Set ↥(higherUnitGroup K i)) =
        ⇑e ⁻¹' (((powMonoidHom n : Multiplicative (Fin (absoluteDegree K) → ℤ_[p]) →*
            Multiplicative (Fin (absoluteDegree K) → ℤ_[p])).range :
          Subgroup (Multiplicative (Fin (absoluteDegree K) → ℤ_[p]))) :
            Set (Multiplicative (Fin (absoluteDegree K) → ℤ_[p]))) := by
      ext x
      simp only [SetLike.mem_coe, MonoidHom.mem_range, powMonoidHom_apply, Set.mem_preimage,
        hSdef]
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨e y, (map_pow e y n).symm⟩
      · rintro ⟨z, hz⟩
        refine ⟨e.symm z, ?_⟩
        have := congrArg e.symm hz
        rwa [map_pow e.symm z n, ContinuousMulEquiv.symm_apply_apply] at this
    rw [hpre]
    exact (isOpen_powRange p (absoluteDegree K) hn).preimage e.continuous
  have hTopen : IsOpen (T : Set Kˣ) := by
    have himg : (T : Set Kˣ) = Subtype.val '' (S : Set ↥(higherUnitGroup K i)) := by
      rw [hTdef, Subgroup.coe_map, Subgroup.coe_subtype]
    rw [himg]
    exact ((higherUnitGroup_isOpen K i).isOpenEmbedding_subtypeVal).isOpenMap _ hSopen
  exact Subgroup.isOpen_mono hTle hTopen

end Atlas.Knowledge
