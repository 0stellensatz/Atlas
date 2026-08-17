import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# integral closure as discrete valuation ring

The integral closure of the ring of integers of a mixed-characteristic local field in a finite
extension `L`—Serre's `A_L`, the ring the whole ramification theory of
`Atlas.Knowledge.LowerRamificationGroup` filters—is a discrete valuation ring. This file proves
that the closure is local, that it is a discrete valuation ring, and that its Jacobson
radical—the ideal the lower numbering is written in—is its maximal ideal, so the powers
filtering the ramification groups are the powers of the maximal ideal.

## Main statements

* `integralClosure_isLocalRing` — the integral closure of `𝒪[K]` in `L` is a local ring.
* `integralClosureDVR` — the integral closure of `𝒪[K]` in `L` is a discrete valuation ring.
* `integralClosure_jacobson_bot_eq_maximalIdeal` — its Jacobson radical is its maximal
  ideal.

## Implementation notes

The route is the spectral norm. For `K` complete under a rank-one valuation the spectral norm
on an algebraic extension is multiplicative and nonarchimedean, and the integral closure of
`𝒪[K]` is exactly its closed unit ball: an element is integral over `𝒪[K]` precisely when its
minimal polynomial has coefficients of norm at most one, which is the bound on the spectral
value. Locality then comes from the unit-ball description, not from Hensel's lemma: a unit of
the ball has norm exactly one by multiplicativity, so the nonunits are the open ball, which the
ultrametric inequality closes under addition. The statements mention no norm and no
uniformity—`K` carries its valuative relation and the topology of the local-field class,
nothing more, and the normed structure is rebuilt inside the proofs from the local-field
hypotheses, so the auxiliary uniformity never escapes. The discrete valuation property is
Dedekind plus local: the closure is a Dedekind domain because `𝒪[K]` is one and the extension
is finite and separable—separability free in characteristic zero—and a local Dedekind domain
that is not a field is a discrete valuation ring. The source's remaining clauses—`B` free of
rank `n` over `𝒪[K]`, completeness of `L`—are not stated here.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

namespace IntegralClosureDVR

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [ValuativeRel K]
  {L : Type*} [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/- The integral closure of `𝒪[K]` in `L` is the closed unit ball of the spectral norm: the
minimal polynomial over `K` of an integral element is the image of its minimal polynomial over
the integrally closed `𝒪[K]`, and conversely a monic polynomial with coefficients of norm at
most one lifts to `𝒪[K]`. -/
omit [IsUltrametricDist K] in
private theorem mem_integralClosure_iff_spectralNorm_le_one [IsIntegrallyClosed 𝒪[K]]
    (hc : ∀ x : K, ‖x‖ ≤ 1 ↔ valuation K x ≤ 1) {y : L} :
    y ∈ integralClosure 𝒪[K] L ↔ spectralNorm K L y ≤ 1 := by
  have hyK : IsIntegral K y := (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
  rw [mem_integralClosure_iff, show spectralNorm K L y = spectralValue (minpoly K y) from rfl]
  constructor
  · intro hy
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hy,
      spectralValue_le_one_iff ((minpoly.monic hy).map _)]
    intro n
    rw [Polynomial.coeff_map]
    exact (hc _).mpr ((minpoly 𝒪[K] y).coeff n).2
  · intro hy
    rw [spectralValue_le_one_iff (minpoly.monic hyK)] at hy
    obtain ⟨q, hq, -, hq_monic⟩ :=
      Polynomial.lifts_and_degree_eq_and_monic
        ((Polynomial.lifts_iff_coeff_lifts (f := algebraMap 𝒪[K] K) _).mpr fun n =>
          ⟨(⟨(minpoly K y).coeff n, (hc _).mp (hy n)⟩ : 𝒪[K]), rfl⟩)
        (minpoly.monic hyK)
    refine ⟨q, hq_monic, ?_⟩
    have h0 : Polynomial.aeval y (q.map (algebraMap 𝒪[K] K)) = 0 := by
      rw [hq]; exact minpoly.aeval K y
    rwa [Polynomial.aeval_map_algebraMap, Polynomial.aeval_def] at h0

/- Units of the integral closure are exactly the elements of spectral norm one, by
multiplicativity of the spectral norm over a complete base. -/
private theorem isUnit_iff_spectralNorm_eq_one [CompleteSpace K] [IsIntegrallyClosed 𝒪[K]]
    (hc : ∀ x : K, ‖x‖ ≤ 1 ↔ valuation K x ≤ 1) {x : integralClosure 𝒪[K] L} :
    IsUnit x ↔ spectralNorm K L (x : L) = 1 := by
  constructor
  · rintro ⟨u, rfl⟩
    have hcoe : ((u : integralClosure 𝒪[K] L) : L) *
        ((↑u⁻¹ : integralClosure 𝒪[K] L) : L) = 1 := by
      rw [← MulMemClass.coe_mul, u.mul_inv, OneMemClass.coe_one]
    have hmul : spectralNorm K L
          (((u : integralClosure 𝒪[K] L) : L) * ((↑u⁻¹ : integralClosure 𝒪[K] L) : L)) =
        spectralNorm K L ((u : integralClosure 𝒪[K] L) : L) *
          spectralNorm K L ((↑u⁻¹ : integralClosure 𝒪[K] L) : L) :=
      spectralAlgNorm_mul _ _
    rw [hcoe, spectralNorm_one] at hmul
    refine le_antisymm
      ((mem_integralClosure_iff_spectralNorm_le_one hc).mp (SetLike.coe_mem _)) ?_
    calc (1 : ℝ) = _ := hmul
      _ ≤ spectralNorm K L ((u : integralClosure 𝒪[K] L) : L) :=
        mul_le_of_le_one_right (spectralNorm_nonneg _)
          ((mem_integralClosure_iff_spectralNorm_le_one hc).mp (SetLike.coe_mem _))
  · intro hx
    have hx0 : (x : L) ≠ 0 := fun h => by simp [h, spectralNorm_zero] at hx
    have hmul : spectralNorm K L ((x : L) * (x : L)⁻¹) =
        spectralNorm K L (x : L) * spectralNorm K L (x : L)⁻¹ := spectralAlgNorm_mul _ _
    rw [mul_inv_cancel₀ hx0, spectralNorm_one, hx, one_mul] at hmul
    refine IsUnit.of_mul_eq_one
      ⟨(x : L)⁻¹, (mem_integralClosure_iff_spectralNorm_le_one hc).mpr hmul.symm.le⟩ ?_
    exact Subtype.ext (by push_cast; exact mul_inv_cancel₀ hx0)

/- Locality of the unit ball: nonunits are the elements of norm strictly below one, and the
ultrametric inequality keeps their sum below one. -/
private theorem isLocalRing [CompleteSpace K] [IsIntegrallyClosed 𝒪[K]]
    (hc : ∀ x : K, ‖x‖ ≤ 1 ↔ valuation K x ≤ 1) :
    IsLocalRing (integralClosure 𝒪[K] L) := by
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  rw [mem_nonunits_iff] at ha hb ⊢
  have hlt : ∀ z : integralClosure 𝒪[K] L, ¬IsUnit z → spectralNorm K L (z : L) < 1 :=
    fun z hz =>
      lt_of_le_of_ne ((mem_integralClosure_iff_spectralNorm_le_one hc).mp (SetLike.coe_mem _))
        fun h => hz ((isUnit_iff_spectralNorm_eq_one hc).mpr h)
  intro hab
  have h1 : spectralNorm K L ((a : L) + (b : L)) = 1 := by
    have := (isUnit_iff_spectralNorm_eq_one hc).mp hab
    rwa [AddMemClass.coe_add] at this
  have hle : spectralNorm K L ((a : L) + (b : L)) ≤
      max (spectralNorm K L (a : L)) (spectralNorm K L (b : L)) :=
    isNonarchimedean_spectralNorm _ _
  exact absurd (h1 ▸ hle) (not_le.mpr (max_lt (hlt a ha) (hlt b hb)))

/- The unit ball is not a field: any scalar of norm strictly between zero and one is a nonzero
nonunit. -/
private theorem not_isField [CompleteSpace K] [IsIntegrallyClosed 𝒪[K]]
    (hc : ∀ x : K, ‖x‖ ≤ 1 ↔ valuation K x ≤ 1) :
    ¬IsField (integralClosure 𝒪[K] L) := by
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt_one K
  have hcy : spectralNorm K L (algebraMap K L c) = ‖c‖ := spectralNorm_extends c
  have hmem : algebraMap K L c ∈ integralClosure 𝒪[K] L :=
    (mem_integralClosure_iff_spectralNorm_le_one hc).mpr (hcy ▸ hc1.le)
  intro hf
  have hne : (⟨algebraMap K L c, hmem⟩ : integralClosure 𝒪[K] L) ≠ 0 := by
    intro h
    have h0 : algebraMap K L c = 0 := congrArg Subtype.val h
    rw [map_eq_zero_iff _ (algebraMap K L).injective] at h0
    rw [h0, norm_zero] at hc0
    exact lt_irrefl 0 hc0
  obtain ⟨u, hu⟩ := hf.mul_inv_cancel hne
  have h1 := (isUnit_iff_spectralNorm_eq_one hc).mp (IsUnit.of_mul_eq_one u hu)
  rw [show ((⟨algebraMap K L c, hmem⟩ : integralClosure 𝒪[K] L) : L) = algebraMap K L c
    from rfl, hcy] at h1
  exact absurd h1 (ne_of_lt hc1)

end IntegralClosureDVR

variable (K : Type*) [Field K] [ValuativeRel K] (L : Type*) [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L]

/-- The two unit-ball conclusions at the public hypotheses, the normed structure rebuilt
once. -/
private theorem IntegralClosureDVR.isLocalRing_and_not_isField [TopologicalSpace K]
    [IsMixedCharLocalField K] [FiniteDimensional K L] :
    IsLocalRing (integralClosure 𝒪[K] L) ∧ ¬IsField (integralClosure 𝒪[K] L) := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : IsUltrametricDist K := inferInstance
  haveI : CompleteSpace K := inferInstance
  exact ⟨IntegralClosureDVR.isLocalRing fun x => Valued.toNormedField.norm_le_one_iff,
    IntegralClosureDVR.not_isField fun x => Valued.toNormedField.norm_le_one_iff⟩

/-- The integral closure of the ring of integers of a mixed-characteristic local field in a
finite extension is a local ring: it is the closed unit ball of the spectral norm, whose
nonunits—the open ball—absorb addition
([Serre 1979, Chap. II, §2, Prop. 3, p.28][Serre1979]). -/
instance integralClosure_isLocalRing [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] : IsLocalRing (integralClosure 𝒪[K] L) :=
  (IntegralClosureDVR.isLocalRing_and_not_isField K L).1

/-- The integral closure of the ring of integers of a mixed-characteristic local field in a
finite extension is a discrete valuation ring—the discrete-valuation-ring clause of the
source's proposition, whose other clauses the Implementation notes leave unstated
([Serre 1979, Chap. II, §2, Prop. 3, p.28][Serre1979]). -/
instance integralClosureDVR [TopologicalSpace K] [IsMixedCharLocalField K]
    [FiniteDimensional K L] : IsDiscreteValuationRing (integralClosure 𝒪[K] L) := by
  haveI : IsDedekindDomain (integralClosure 𝒪[K] L) :=
    IsIntegralClosure.isDedekindDomain 𝒪[K] K L (integralClosure 𝒪[K] L)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure 𝒪[K] L)
    (IntegralClosureDVR.isLocalRing_and_not_isField K L).2).out 2 0).mp
    ‹IsDedekindDomain (integralClosure 𝒪[K] L)›

/-- The Jacobson radical of the integral closure—the ideal the lower numbering of
`Atlas.Knowledge.LowerRamificationGroup` is written in—is its maximal ideal
([Serre 1979, Chap. II, §2, Prop. 3, p.28][Serre1979]). -/
theorem integralClosure_jacobson_bot_eq_maximalIdeal [TopologicalSpace K]
    [IsMixedCharLocalField K] [FiniteDimensional K L] :
    Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) =
      IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L) :=
  IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top

end Atlas.Knowledge
