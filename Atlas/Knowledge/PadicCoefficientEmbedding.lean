import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.PadicExpConvergence
import Atlas.Knowledge.RationalIntegerValuation
import Atlas.Knowledge.ResidueCharacteristic

/-!
# coefficient embedding of the p-adic integers

The canonical embedding of the `p`-adic integers into the valuation ring of a
mixed-characteristic local field of residue characteristic `p`, together with its extension to
`ℚ_[p]`: Serre introduces the coefficient ring by observing that "the injection Z → A extends
by continuity to an injection of the ring Z_p of p-adic integers into A"
([Serre 1979, Chap. II, §5, p.36][Serre1979]). Through the embedding the `ℤ_p`-module structure
that `Atlas.Knowledge.DeepUnitGroup` reads off the deep unit groups becomes a structure carried
by `K` itself: the scalars act inside `𝒪[K]`, not through an auxiliary coefficient ring.

## Main definitions

* `padicCoefficientEmbedding` — the ring morphism `ℤ_[p] →+* 𝒪[K]`, sending a `p`-adic integer
  to the limit of its integer approximations.
* `padicFieldEmbedding` — the extension `ℚ_[p] →+* K`, through the universal property of the
  fraction field.

## Main statements

* `PadicCoefficientEmbedding.sub_appr_mem` — the defining congruences: the image of `c` agrees
  with the approximation `c.appr n` modulo `𝓂[K] ^ n`.
* `PadicFieldEmbedding.coe_padicCoefficientEmbedding` — the field-level morphism extends the
  integral one, which is what makes it an extension at all.
* `PadicCoefficientEmbedding.continuous`, `PadicCoefficientEmbedding.injective`, and
  `PadicFieldEmbedding.continuous` — both embeddings are continuous, and the integral one is
  recorded injective.

## Implementation notes

The construction is successive approximation. Mathlib's local-field theory provides
`IsAdicComplete 𝓂[K] ↥𝒪[K]`, whose `IsPrecomplete` half turns the compatible sequence
`n ↦ c.appr n` into a limit and whose `IsHausdorff` half makes the limit unique; the morphism
laws, the defining congruences, and both continuity statements are each one application of that
uniqueness principle to a congruence between approximations, carried from `ℤ_[p]` into `𝒪[K]`
by the divisibility bridge `PadicInt.norm_int_le_pow_iff_dvd`. The prime enters as a variable
`p` pinned to the invariant by the equation `hp : residueCharacteristic K = p`, because the
notation `ℤ_[p]` requires a `Fact p.Prime` instance that a projection like
`residueCharacteristic K` cannot carry by itself—the pattern of
`Atlas.Knowledge.DeepUnitGroup`. The statements mention no norm and no uniformity: the
adic-completeness instances live over a uniform structure, and the continuity arguments need a
rank-one norm, so the proofs rebuild both from the local-field hypotheses as in
`Atlas.Knowledge.PadicExpConvergence`, and nothing auxiliary escapes into a statement.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
variable (p : ℕ) [Fact p.Prime] (hp : residueCharacteristic K = p)

namespace PadicCoefficientEmbedding

/-! ### The limit of the approximations -/

private theorem smodeq_iff {R : Type*} [CommRing R] {I : Ideal R} {x y : R} {n : ℕ} :
    x ≡ y [SMOD (I ^ n • ⊤ : Submodule R R)] ↔ x - y ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

set_option synthInstance.maxHeartbeats 80000 in
-- `IsLocalRing ↥𝒪[K]`, which the maximal-ideal rewrites go through, does not fit the default
-- instance budget.
include hp in
omit [Fact p.Prime] in
private theorem natCast_mem_maximalIdeal : ((p : ℕ) : ↥𝒪[K]) ∈ 𝓂[K] := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_natCast_iff, hp]
  exact not_not_intro dvd_rfl

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
include hp in
private theorem intCast_mem_pow {z : ℤ} {n : ℕ}
    (hz : ((z : ℤ_[p])) ∈ Ideal.span {(p : ℤ_[p]) ^ n}) :
    ((z : ↥𝒪[K])) ∈ (𝓂[K] ^ n : Ideal ↥𝒪[K]) := by
  obtain ⟨t, rfl⟩ : (p : ℤ) ^ n ∣ z :=
    PadicInt.norm_int_le_pow_iff_dvd.mp ((PadicInt.norm_le_pow_iff_mem_span_pow _ n).mpr hz)
  push_cast
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (natCast_mem_maximalIdeal K p hp) n)

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
include hp in
private theorem appr_sub_appr_mem {c c' : ℤ_[p]} {m n n' : ℕ} (hn : m ≤ n) (hn' : m ≤ n')
    (h : c - c' ∈ Ideal.span {(p : ℤ_[p]) ^ m}) :
    (c.appr n : ↥𝒪[K]) - (c'.appr n' : ↥𝒪[K]) ∈ (𝓂[K] ^ m : Ideal ↥𝒪[K]) := by
  have h1 : c - (c.appr n : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ m} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hn) (PadicInt.appr_spec n c)
  have h2 : c' - (c'.appr n' : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ m} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ hn') (PadicInt.appr_spec n' c')
  have key : (((c.appr n : ℤ) - (c'.appr n' : ℤ) : ℤ) : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ m} := by
    push_cast
    have e : ((c.appr n : ℤ_[p])) - ((c'.appr n' : ℤ_[p]))
        = ((c - c') - (c - (c.appr n : ℤ_[p]))) + (c' - (c'.appr n' : ℤ_[p])) := by ring
    rw [e]
    exact Ideal.add_mem _ (Ideal.sub_mem _ h h1) h2
  have hmem := intCast_mem_pow K p hp key
  push_cast at hmem
  exact hmem

set_option synthInstance.maxHeartbeats 400000 in
-- The adic-completeness instances unfold through `IsLocalRing ↥𝒪[K]` and the rebuilt uniform
-- structure, which does not fit the default instance budget.
include hp in
private theorem exists_limit (c : ℤ_[p]) :
    ∃ L : ↥𝒪[K], ∀ n : ℕ,
      (c.appr n : ↥𝒪[K]) ≡ L [SMOD (𝓂[K] ^ n • ⊤ : Submodule ↥𝒪[K] ↥𝒪[K])] := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  refine IsPrecomplete.prec (inferInstance : IsPrecomplete 𝓂[K] ↥𝒪[K]) fun {m n} hmn => ?_
  rw [smodeq_iff]
  exact appr_sub_appr_mem K p hp le_rfl hmn (by rw [sub_self]; exact Ideal.zero_mem _)

set_option synthInstance.maxHeartbeats 400000 in
-- The adic-completeness instances unfold through `IsLocalRing ↥𝒪[K]` and the rebuilt uniform
-- structure, which does not fit the default instance budget.
private theorem limit_unique {f : ℕ → ↥𝒪[K]} {L L' : ↥𝒪[K]}
    (hL : ∀ n : ℕ, f n ≡ L [SMOD (𝓂[K] ^ n • ⊤ : Submodule ↥𝒪[K] ↥𝒪[K])])
    (hL' : ∀ n : ℕ, f n ≡ L' [SMOD (𝓂[K] ^ n • ⊤ : Submodule ↥𝒪[K] ↥𝒪[K])]) : L = L' := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  refine sub_eq_zero.mp
    (IsHausdorff.haus (inferInstance : IsHausdorff 𝓂[K] ↥𝒪[K]) (L - L') fun n => ?_)
  rw [smodeq_iff, sub_zero]
  exact smodeq_iff.mp ((hL n).symm.trans (hL' n))

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
private theorem choose_spec_mem (c : ℤ_[p]) (n : ℕ) :
    (c.appr n : ↥𝒪[K]) - (exists_limit K p hp c).choose ∈ (𝓂[K] ^ n : Ideal ↥𝒪[K]) :=
  smodeq_iff.mp ((exists_limit K p hp c).choose_spec n)

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
private theorem choose_eq (c : ℤ_[p]) {L : ↥𝒪[K]}
    (hL : ∀ n : ℕ, (c.appr n : ↥𝒪[K]) - L ∈ (𝓂[K] ^ n : Ideal ↥𝒪[K])) :
    (exists_limit K p hp c).choose = L :=
  limit_unique K ((exists_limit K p hp c).choose_spec) fun n => smodeq_iff.mpr (hL n)

/-! ### The morphism laws -/

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
private theorem limit_one : (exists_limit K p hp 1).choose = 1 := by
  refine choose_eq K p hp 1 fun n => ?_
  have key : ((((1 : ℤ_[p]).appr n : ℤ) - 1 : ℤ) : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
    push_cast
    have e : (((1 : ℤ_[p]).appr n : ℤ_[p])) - 1
        = -((1 : ℤ_[p]) - ((1 : ℤ_[p]).appr n : ℤ_[p])) := by ring
    rw [e]
    exact neg_mem (PadicInt.appr_spec n 1)
  have hmem := intCast_mem_pow K p hp key
  push_cast at hmem
  exact hmem

private theorem appr_zero_eq (n : ℕ) : (0 : ℤ_[p]).appr n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [PadicInt.appr, ih]

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
private theorem limit_zero : (exists_limit K p hp 0).choose = 0 := by
  refine choose_eq K p hp 0 fun n => ?_
  rw [appr_zero_eq]
  simp

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
private theorem limit_add (c c' : ℤ_[p]) :
    (exists_limit K p hp (c + c')).choose
      = (exists_limit K p hp c).choose + (exists_limit K p hp c').choose := by
  refine choose_eq K p hp _ fun n => ?_
  have key : ((((c + c').appr n : ℤ) - ((c.appr n : ℤ) + (c'.appr n : ℤ)) : ℤ) : ℤ_[p])
      ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
    push_cast
    have e : (((c + c').appr n : ℤ_[p])) - (((c.appr n : ℤ_[p])) + ((c'.appr n : ℤ_[p])))
        = ((c - ((c.appr n : ℤ_[p]))) + (c' - ((c'.appr n : ℤ_[p]))))
          - ((c + c') - (((c + c').appr n : ℤ_[p]))) := by ring
    rw [e]
    exact Ideal.sub_mem _
      (Ideal.add_mem _ (PadicInt.appr_spec n c) (PadicInt.appr_spec n c'))
      (PadicInt.appr_spec n (c + c'))
  have h1 := intCast_mem_pow K p hp key
  push_cast at h1
  have e2 : (((c + c').appr n : ↥𝒪[K]))
      - ((exists_limit K p hp c).choose + (exists_limit K p hp c').choose)
      = ((((c + c').appr n : ↥𝒪[K])) - (((c.appr n : ↥𝒪[K])) + ((c'.appr n : ↥𝒪[K]))))
        + ((((c.appr n : ↥𝒪[K])) - (exists_limit K p hp c).choose)
          + (((c'.appr n : ↥𝒪[K])) - (exists_limit K p hp c').choose)) := by ring
  rw [e2]
  exact Ideal.add_mem _ h1
    (Ideal.add_mem _ (choose_spec_mem K p hp c n) (choose_spec_mem K p hp c' n))

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
private theorem limit_mul (c c' : ℤ_[p]) :
    (exists_limit K p hp (c * c')).choose
      = (exists_limit K p hp c).choose * (exists_limit K p hp c').choose := by
  refine choose_eq K p hp _ fun n => ?_
  have key : ((((c * c').appr n : ℤ) - ((c.appr n : ℤ) * (c'.appr n : ℤ)) : ℤ) : ℤ_[p])
      ∈ Ideal.span {(p : ℤ_[p]) ^ n} := by
    push_cast
    have e : (((c * c').appr n : ℤ_[p])) - (((c.appr n : ℤ_[p])) * ((c'.appr n : ℤ_[p])))
        = (c * (c' - ((c'.appr n : ℤ_[p])))
            + (c - ((c.appr n : ℤ_[p]))) * ((c'.appr n : ℤ_[p])))
          - ((c * c') - (((c * c').appr n : ℤ_[p]))) := by ring
    rw [e]
    exact Ideal.sub_mem _
      (Ideal.add_mem _ (Ideal.mul_mem_left _ c (PadicInt.appr_spec n c'))
        (Ideal.mul_mem_right _ _ (PadicInt.appr_spec n c)))
      (PadicInt.appr_spec n (c * c'))
  have h1 := intCast_mem_pow K p hp key
  push_cast at h1
  set B := ((c.appr n : ↥𝒪[K])) with hB
  set B' := ((c'.appr n : ↥𝒪[K])) with hB'
  set L := (exists_limit K p hp c).choose with hL
  set L' := (exists_limit K p hp c').choose with hL'
  have e2 : (((c * c').appr n : ↥𝒪[K])) - L * L'
      = ((((c * c').appr n : ↥𝒪[K])) - B * B') + (B * (B' - L') + (B - L) * L') := by ring
  rw [e2]
  exact Ideal.add_mem _ h1
    (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (choose_spec_mem K p hp c' n))
      (Ideal.mul_mem_right _ _ (choose_spec_mem K p hp c n)))

end PadicCoefficientEmbedding

/-- The **coefficient embedding**: the canonical ring morphism `ℤ_[p] →+* 𝒪[K]` into the
valuation ring of a mixed-characteristic local field of residue characteristic `p`, sending a
`p`-adic integer to the limit of its integer approximations `PadicInt.appr` along the
maximal-adic filtration ([Serre 1979, Chap. II, §5, p.36][Serre1979], "the injection Z → A
extends by continuity to an injection of the ring Z_p of p-adic integers into A"). -/
noncomputable def padicCoefficientEmbedding : ℤ_[p] →+* ↥𝒪[K] where
  toFun c := (PadicCoefficientEmbedding.exists_limit K p hp c).choose
  map_one' := PadicCoefficientEmbedding.limit_one K p hp
  map_mul' := PadicCoefficientEmbedding.limit_mul K p hp
  map_zero' := PadicCoefficientEmbedding.limit_zero K p hp
  map_add' := PadicCoefficientEmbedding.limit_add K p hp

namespace PadicCoefficientEmbedding

private theorem coe_def (c : ℤ_[p]) :
    padicCoefficientEmbedding K p hp c = (exists_limit K p hp c).choose := rfl

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
/-- The defining congruences of the coefficient embedding: the image of `c` agrees with the
integer approximation `c.appr n` modulo the `n`-th power of the maximal ideal. -/
theorem sub_appr_mem (c : ℤ_[p]) (n : ℕ) :
    padicCoefficientEmbedding K p hp c - ((c.appr n : ℕ) : ↥𝒪[K])
      ∈ (𝓂[K] ^ n : Ideal ↥𝒪[K]) := by
  rw [coe_def, ← neg_sub]
  exact neg_mem (choose_spec_mem K p hp c n)

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
private theorem sub_mem_pow {c c' : ℤ_[p]} {n : ℕ}
    (h : c - c' ∈ Ideal.span {(p : ℤ_[p]) ^ n}) :
    padicCoefficientEmbedding K p hp c - padicCoefficientEmbedding K p hp c'
      ∈ (𝓂[K] ^ n : Ideal ↥𝒪[K]) := by
  simp only [coe_def]
  have e : (exists_limit K p hp c).choose - (exists_limit K p hp c').choose
      = (((c.appr n : ↥𝒪[K])) - ((c'.appr n : ↥𝒪[K])))
        - (((c.appr n : ↥𝒪[K])) - (exists_limit K p hp c).choose)
        + (((c'.appr n : ↥𝒪[K])) - (exists_limit K p hp c').choose) := by ring
  rw [e]
  exact Ideal.add_mem _
    (Ideal.sub_mem _ (appr_sub_appr_mem K p hp le_rfl le_rfl h) (choose_spec_mem K p hp c n))
    (choose_spec_mem K p hp c' n)

set_option synthInstance.maxHeartbeats 400000 in
-- The rebuilt uniform structure and the ideal arithmetic on `↥𝒪[K]` do not fit the default
-- instance budget.
/-- The coefficient embedding is continuous: it carries the `p`-adic filtration of `ℤ_[p]` into
the maximal-adic filtration of `𝒪[K]`
([Serre 1979, Chap. II, §5, p.36][Serre1979], "extends by continuity"). -/
protected theorem continuous : Continuous (padicCoefficientEmbedding K p hp) := by
  -- Rebuild the normed structure; its topology is the given one.
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  have hc : ∀ y : K, ‖y‖ ≤ 1 ↔ valuation K y ≤ 1 := fun y => Valued.toNormedField.norm_le_one_iff
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[K])
  have hϖ0 : 0 < ‖((ϖ : ↥𝒪[K]) : K)‖ := by rw [norm_pos_iff]; simpa using hϖ.ne_zero
  have hϖ1 : ‖((ϖ : ↥𝒪[K]) : K)‖ < 1 := by
    rw [RationalIntegerValuation.norm_lt_one_iff_valuation_lt_one hc]
    exact valuation_lt_one_of_mem_maximalIdeal _
      (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
  have key : Continuous fun c : ℤ_[p] =>
      ((padicCoefficientEmbedding K p hp c : ↥𝒪[K]) : K) := by
    refine Metric.continuous_iff.mpr fun c ε hε => ?_
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hϖ1
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
    refine ⟨(p : ℝ) ^ (-(m : ℤ)), zpow_pos hp0 _, fun c' hc' => ?_⟩
    have hmem : c' - c ∈ Ideal.span {(p : ℤ_[p]) ^ m} := by
      rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
      rw [dist_eq_norm] at hc'
      exact hc'.le
    have hnorm : ‖((padicCoefficientEmbedding K p hp c'
          - padicCoefficientEmbedding K p hp c : ↥𝒪[K]) : K)‖ ≤ ‖((ϖ : ↥𝒪[K]) : K)‖ ^ m :=
      (PadicExpConvergence.mem_pow_iff_norm_le hc hϖ hϖ0 hϖ1 _ m).mp (sub_mem_pow K p hp hmem)
    have hlt : ‖((padicCoefficientEmbedding K p hp c'
        - padicCoefficientEmbedding K p hp c : ↥𝒪[K]) : K)‖ < ε := lt_of_le_of_lt hnorm hm
    have ecast : ((padicCoefficientEmbedding K p hp c'
        - padicCoefficientEmbedding K p hp c : ↥𝒪[K]) : K)
        = ((padicCoefficientEmbedding K p hp c' : ↥𝒪[K]) : K)
          - ((padicCoefficientEmbedding K p hp c : ↥𝒪[K]) : K) := by
      push_cast
      rfl
    rw [ecast] at hlt
    refine (dist_eq_norm _ _).trans_lt ?_
    exact hlt
  exact continuous_induced_rng.mpr key

/-- The coefficient embedding is injective: writing a nonzero `c` as a unit times a power of
`p`, the image of the unit is a unit and `p` is nonzero in `𝒪[K]`, the field having
characteristic zero ([Serre 1979, Chap. II, §5, p.36][Serre1979], "an injection"). -/
protected theorem injective : Function.Injective (padicCoefficientEmbedding K p hp) := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc => ?_
  by_contra hc0
  rw [PadicInt.unitCoeff_spec hc0, map_mul, map_pow, map_natCast] at hc
  have hpne : ((p : ℕ) : ↥𝒪[K]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  exact mul_ne_zero
    (IsUnit.ne_zero ((PadicInt.unitCoeff hc0).isUnit.map (padicCoefficientEmbedding K p hp)))
    (pow_ne_zero _ hpne) hc

end PadicCoefficientEmbedding

/-- The **field-level coefficient embedding**: the canonical ring morphism `ℚ_[p] →+* K`,
extending `Atlas.Knowledge.padicCoefficientEmbedding` through the universal property of the
fraction field `ℚ_[p]` of `ℤ_[p]` ([Serre 1979, Chap. II, §5, p.36][Serre1979]). -/
noncomputable def padicFieldEmbedding : ℚ_[p] →+* K :=
  IsFractionRing.lift
    (g := (algebraMap (↥𝒪[K]) K).comp (padicCoefficientEmbedding K p hp))
    fun _ _ hab => PadicCoefficientEmbedding.injective K p hp (Subtype.coe_injective hab)

namespace PadicFieldEmbedding

/-- The field embedding restricts to the coefficient embedding on the `p`-adic integers. -/
theorem coe_padicCoefficientEmbedding (c : ℤ_[p]) :
    padicFieldEmbedding K p hp (c : ℚ_[p])
      = ((padicCoefficientEmbedding K p hp c : ↥𝒪[K]) : K) :=
  IsFractionRing.lift_algebraMap _ c

set_option synthInstance.maxHeartbeats 400000 in
-- The rebuilt uniform structure and the ideal arithmetic on `↥𝒪[K]` do not fit the default
-- instance budget.
/-- The field embedding is continuous: a difference of nearby arguments lies in `ℤ_[p]`, where
the contraction bound of `Atlas.Knowledge.padicCoefficientEmbedding` applies
([Serre 1979, Chap. II, §5, p.36][Serre1979], "extends by continuity"). -/
protected theorem continuous : Continuous (padicFieldEmbedding K p hp) := by
  -- Rebuild the normed structure; its topology is the given one.
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  have hc : ∀ y : K, ‖y‖ ≤ 1 ↔ valuation K y ≤ 1 := fun y => Valued.toNormedField.norm_le_one_iff
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[K])
  have hϖ0 : 0 < ‖((ϖ : ↥𝒪[K]) : K)‖ := by rw [norm_pos_iff]; simpa using hϖ.ne_zero
  have hϖ1 : ‖((ϖ : ↥𝒪[K]) : K)‖ < 1 := by
    rw [RationalIntegerValuation.norm_lt_one_iff_valuation_lt_one hc]
    exact valuation_lt_one_of_mem_maximalIdeal _
      (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
  refine Metric.continuous_iff.mpr fun b ε hε => ?_
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hε hϖ1
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  refine ⟨(p : ℝ) ^ (-(m : ℤ)), zpow_pos hp0 _, fun a hab => ?_⟩
  rw [dist_eq_norm] at hab
  have hab1 : ‖a - b‖ ≤ 1 :=
    hab.le.trans (zpow_le_one_of_nonpos₀ hp1 (neg_nonpos.mpr (Int.natCast_nonneg m)))
  obtain ⟨z, hz_eq⟩ : ∃ z : ℤ_[p], (z : ℚ_[p]) = a - b := ⟨⟨a - b, hab1⟩, rfl⟩
  have hmem : z - (0 : ℤ_[p]) ∈ Ideal.span {(p : ℤ_[p]) ^ m} := by
    rw [sub_zero, ← PadicInt.norm_le_pow_iff_mem_span_pow, PadicInt.norm_def, hz_eq]
    exact hab.le
  have hsub := PadicCoefficientEmbedding.sub_mem_pow K p hp hmem
  rw [map_zero, sub_zero] at hsub
  have hnorm : ‖((padicCoefficientEmbedding K p hp z : ↥𝒪[K]) : K)‖
      ≤ ‖((ϖ : ↥𝒪[K]) : K)‖ ^ m :=
    (PadicExpConvergence.mem_pow_iff_norm_le hc hϖ hϖ0 hϖ1 _ m).mp hsub
  have e : padicFieldEmbedding K p hp a - padicFieldEmbedding K p hp b
      = ((padicCoefficientEmbedding K p hp z : ↥𝒪[K]) : K) := by
    rw [← map_sub, ← hz_eq]
    exact coe_padicCoefficientEmbedding K p hp z
  refine (dist_eq_norm _ _).trans_lt ?_
  rw [e]
  exact lt_of_le_of_lt hnorm hm

end PadicFieldEmbedding

end Atlas.Knowledge
