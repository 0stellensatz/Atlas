import Mathlib
import Atlas.Knowledge.AbsoluteDegree
import Atlas.Knowledge.AbsoluteInertiaDegree
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.PadicCoefficientEmbedding
import Atlas.Knowledge.RationalIntegerValuation
import Atlas.Knowledge.ResidueCharacteristic

/-!
# free module structure of the valuation ring

The valuation ring of a mixed-characteristic local field is a free module of rank the absolute
degree over the `p`-adic integers, topologically: `𝒪[K]`, with the module structure of the
coefficient embedding `Atlas.Knowledge.padicCoefficientEmbedding`, is isomorphic to
`d = e_K * f_K` copies of `ℤ_[p]` as a topological additive group. This is the additive half
of the free-rank engine: `Atlas.Knowledge.DeepUnitGroup` reads the rank of a deep unit group
through the exponential of `Atlas.Knowledge.PadicExpTopologicalIso` and then through this
item.

## Main statements

* `padicIntegerFreeModule` — `Fin (absoluteDegree K) → ℤ_[p]` is topologically isomorphic to
  `𝒪[K]` as an additive group.

## Implementation notes

The generators are lifts of the residue classes modulo `p`, of which there are finitely many
because `p 𝒪[K] = 𝓂[K] ^ e` has finite index. That they span topologically is a finite
approximation—every integer is a `ℤ_[p]`-combination of the lifts to within `p ^ n` for every
`n`, by induction—together with one compactness observation that replaces the usual limit
argument: the span of finitely many elements is the image of a compact product of copies of
`ℤ_[p]` under a continuous map, hence closed, and a closed set at distance zero from
everything is everything. Freeness is then Mathlib's `Module.free_of_finite_type_torsion_free`
over the discrete valuation ring `ℤ_[p]`, and the rank is counted on `𝒪[K] ⧸ p 𝒪[K]`: the
quotient has `p ^ (rank)` elements through the free structure, and `(p ^ f) ^ e` elements
through the filtration `p 𝒪[K] = 𝓂[K] ^ e` of
`Atlas.Knowledge.span_residueCharacteristic_eq_maximalIdeal_pow`, the multiplicativity of
`Submodule.cardQuot` on powers of the maximal ideal, and the count `#𝓀[K] = p ^ f` of
`Atlas.Knowledge.AbsoluteInertiaDegree.card_residueField_eq_pow`. The inverse of the final map is
continuous for free, the source being compact and the target Hausdorff.

The scaffolding takes the module structure as a variable together with the hypothesis `hsmul`
spelling its action through a ring morphism `φ`, the same discipline as the norm-variable
scaffolding of `Atlas.Knowledge.RationalIntegerValuation`, and like that item's it stays
public: `φ` and `hsmul` are the reusable seam, and a later consumer of the spanning or
closedness lemmas plugs in its own morphism. The public statement instantiates `φ` with the
coefficient embedding, whose action is definitionally multiplication. The headline records
the additive topological isomorphism only—its sole consumer needs no more—and the free-module
structure that the proof manufactures on the way is deliberately not re-exported.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel
open scoped Pointwise

namespace Atlas.Knowledge

namespace PadicIntegerFreeModule

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
variable {p : ℕ} [Fact p.Prime] (hp : residueCharacteristic K = p)
variable [Module ℤ_[p] ↥𝒪[K]] (φ : ℤ_[p] →+* ↥𝒪[K])
variable (hsmul : ∀ (c : ℤ_[p]) (z : ↥𝒪[K]), c • z = φ c * z)

omit [Fact p.Prime] in
include hp in
/-- The residue classes modulo `p` are finitely many, and lifts of them approximate every
integer to within `p`. -/
theorem exists_residue_lift : ∃ (N : ℕ) (x : Fin N → ↥𝒪[K]), ∀ z : ↥𝒪[K],
    ∃ j : Fin N, z - x j ∈ Ideal.span {(p : ↥𝒪[K])} := by
  have hpe := span_residueCharacteristic_eq_maximalIdeal_pow K
  rw [hp] at hpe
  have hprime : (𝓂[K] : Ideal ↥𝒪[K]).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  have hbot : (𝓂[K] : Ideal ↥𝒪[K]) ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField ↥𝒪[K]
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h)
  have hcard : Nat.card (↥𝒪[K] ⧸ Ideal.span {(p : ↥𝒪[K])}) ≠ 0 := by
    rw [← Submodule.cardQuot_apply, hpe, cardQuot_pow_of_prime hbot,
      Submodule.cardQuot_apply]
    have hfin : Finite 𝓀[K] := inferInstance
    have h𝓀 : Nat.card (↥𝒪[K] ⧸ (𝓂[K] : Ideal ↥𝒪[K])) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨⟨0⟩, hfin⟩
    positivity
  obtain ⟨hne, hfin⟩ := Nat.card_ne_zero.mp hcard
  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (↥𝒪[K] ⧸ Ideal.span {(p : ↥𝒪[K])})
  refine ⟨N, fun j => (e.symm j).out, fun z => ⟨e (Submodule.Quotient.mk z), ?_⟩⟩
  rw [← Submodule.Quotient.eq]
  have hout : Submodule.Quotient.mk (e.symm (e (Submodule.Quotient.mk z))).out
      = e.symm (e (Submodule.Quotient.mk z)) := Quotient.out_eq _
  rw [hout, Equiv.symm_apply_apply]

omit [TopologicalSpace K] [IsMixedCharLocalField K] in
include hsmul in
/-- Every integer is a span combination of the residue lifts to within `p ^ n`, by finite
approximation. -/
theorem exists_approx {N : ℕ} (x : Fin N → ↥𝒪[K])
    (hx : ∀ z : ↥𝒪[K], ∃ j : Fin N, z - x j ∈ Ideal.span {(p : ↥𝒪[K])})
    (z : ↥𝒪[K]) (n : ℕ) :
    ∃ s ∈ Submodule.span ℤ_[p] (Set.range x), z - s ∈ Ideal.span {(p : ↥𝒪[K]) ^ n} := by
  induction n with
  | zero =>
      exact ⟨0, Submodule.zero_mem _, by simp⟩
  | succ n ih =>
      obtain ⟨s, hs, hmem⟩ := ih
      obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hmem
      obtain ⟨j, hj⟩ := hx w
      obtain ⟨w', hw'⟩ := Ideal.mem_span_singleton.mp hj
      refine ⟨s + ((p : ℤ_[p]) ^ n) • x j, Submodule.add_mem _ hs
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)), ?_⟩
      rw [Ideal.mem_span_singleton]
      refine ⟨w', ?_⟩
      have hφp : φ ((p : ℤ_[p]) ^ n) = (p : ↥𝒪[K]) ^ n := by
        rw [map_pow, map_natCast]
      calc z - (s + ((p : ℤ_[p]) ^ n) • x j)
          = (z - s) - φ ((p : ℤ_[p]) ^ n) * x j := by rw [hsmul]; ring
        _ = (p : ↥𝒪[K]) ^ n * w - (p : ↥𝒪[K]) ^ n * x j := by rw [hw, hφp]
        _ = (p : ↥𝒪[K]) ^ n * (w - x j) := by ring
        _ = (p : ↥𝒪[K]) ^ (n + 1) * w' := by rw [hw', pow_succ]; ring

include hsmul in
/-- The span of finitely many integers is closed: it is the continuous image of a compact
product of copies of `ℤ_[p]`. -/
theorem isClosed_span (hφc : Continuous φ) {N : ℕ} (x : Fin N → ↥𝒪[K]) :
    IsClosed ((Submodule.span ℤ_[p] (Set.range x) : Submodule ℤ_[p] ↥𝒪[K]) : Set ↥𝒪[K]) := by
  have hset : ((Submodule.span ℤ_[p] (Set.range x) : Submodule ℤ_[p] ↥𝒪[K]) : Set ↥𝒪[K])
      = Set.range fun c : Fin N → ℤ_[p] => ∑ i, c i • x i := by
    ext z
    simp only [SetLike.mem_coe, Set.mem_range]
    rw [Submodule.mem_span_range_iff_exists_fun ℤ_[p]]
  rw [hset]
  -- Rebuild the normed structure to reach a `T2Space` instance for the carrier topology.
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : T2Space K := inferInstance
  have hcont : Continuous fun c : Fin N → ℤ_[p] => ∑ i, c i • x i := by
    refine continuous_finsetSum _ fun i _ => ?_
    have : (fun c : Fin N → ℤ_[p] => c i • x i) = fun c => φ (c i) * x i := by
      funext c
      rw [hsmul]
    rw [this]
    exact ((hφc.comp (continuous_apply i)).mul continuous_const)
  exact (isCompact_range hcont).isClosed

include hp hsmul in
/-- Lifts of the residue classes span topologically: their span is closed and reaches every
integer to within every power of `p`. -/
theorem span_eq_top (hφc : Continuous φ) {N : ℕ} (x : Fin N → ↥𝒪[K])
    (hx : ∀ z : ↥𝒪[K], ∃ j : Fin N, z - x j ∈ Ideal.span {(p : ↥𝒪[K])}) :
    Submodule.span ℤ_[p] (Set.range x) = ⊤ := by
  have hclosed := isClosed_span φ hsmul hφc x
  -- Rebuild the normed structure; its topology is the given one.
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  have hc : ∀ y : K, ‖y‖ ≤ 1 ↔ valuation K y ≤ 1 := fun y => Valued.toNormedField.norm_le_one_iff
  refine Submodule.eq_top_iff'.mpr fun z => ?_
  have hmem : z ∈ closure
      ((Submodule.span ℤ_[p] (Set.range x) : Submodule ℤ_[p] ↥𝒪[K]) : Set ↥𝒪[K]) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    have hp1 : ‖((p : ℕ) : K)‖ < 1 := by
      rw [RationalIntegerValuation.norm_lt_one_iff_valuation_lt_one hc, ← hp]
      exact valuation_residueCharacteristic_lt_one
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hp1
    obtain ⟨s, hs, hsmem⟩ := exists_approx φ hsmul x hx z n
    refine ⟨s, hs, ?_⟩
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton.mp hsmem
    have hdist : dist z s = ‖((z : ↥𝒪[K]) : K) - ((s : ↥𝒪[K]) : K)‖ := by
      rw [Subtype.dist_eq, dist_eq_norm]
    have hcoe : ((z : ↥𝒪[K]) : K) - ((s : ↥𝒪[K]) : K)
        = (((p : ↥𝒪[K]) ^ n * w : ↥𝒪[K]) : K) := by
      rw [← hw]
      push_cast
      ring
    calc dist z s = ‖(((p : ↥𝒪[K]) ^ n * w : ↥𝒪[K]) : K)‖ := by rw [hdist, hcoe]
      _ ≤ ‖((p : ℕ) : K)‖ ^ n := by
          push_cast
          rw [norm_mul, norm_pow]
          exact mul_le_of_le_one_right (by positivity) ((hc _).mpr w.2)
      _ < ε := hn
  rwa [hclosed.closure_eq] at hmem

end PadicIntegerFreeModule

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
open PadicIntegerFreeModule in
/-- **The valuation ring is `d` copies of the `p`-adic integers as a topological additive
group**, `d = e * f` the absolute degree: the additive shadow of Serre's free-module
statement, which is all the composition of `Atlas.Knowledge.DeepUnitGroup` consumes; the
`ℤ_[p]`-linearity of the witness lives inside the proof
([Serre 1979, Chap. II, §5, p.36][Serre1979], "prop. 5 shows that A is a free Z_p-module of
rank n = ef"; [Hyeon 2025, §3, pp.9–10][Hyeon2025]). -/
theorem padicIntegerFreeModule (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (p : ℕ) [Fact p.Prime] (hp : residueCharacteristic K = p) :
    Nonempty ((Fin (absoluteDegree K) → ℤ_[p]) ≃ₜ+ ↥𝒪[K]) := by
  letI : Module ℤ_[p] ↥𝒪[K] := (padicCoefficientEmbedding K p hp).toModule
  have hsmul : ∀ (c : ℤ_[p]) (z : ↥𝒪[K]), c • z = padicCoefficientEmbedding K p hp c * z :=
    fun _ _ => rfl
  obtain ⟨N, x, hx⟩ := exists_residue_lift (p := p) hp
  have hspan := span_eq_top hp (padicCoefficientEmbedding K p hp) hsmul
    (PadicCoefficientEmbedding.continuous K p hp) x hx
  haveI : NoZeroSMulDivisors ℤ_[p] ↥𝒪[K] := by
    refine ⟨fun {c z} hcz => ?_⟩
    rw [hsmul] at hcz
    rcases mul_eq_zero.mp hcz with h | h
    · exact Or.inl ((injective_iff_map_eq_zero _).mp
        (PadicCoefficientEmbedding.injective K p hp) c h)
    · exact Or.inr h
  haveI hfree : Module.Free ℤ_[p] ↥𝒪[K] :=
    Module.free_of_finite_type_torsion_free (s := x) hspan
  haveI := Classical.decEq ↥𝒪[K]
  haveI hfin : Module.Finite ℤ_[p] ↥𝒪[K] := ⟨⟨Finset.univ.image x, by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
    exact hspan⟩⟩
  set ι := Module.Free.ChooseBasisIndex ℤ_[p] ↥𝒪[K] with hι
  let b : Module.Basis ι ℤ_[p] ↥𝒪[K] := Module.Free.chooseBasis ℤ_[p] ↥𝒪[K]
  -- count `𝒪[K] ⧸ p 𝒪[K]` through the filtration
  have hpe := span_residueCharacteristic_eq_maximalIdeal_pow K
  rw [hp] at hpe
  haveI hprime : (𝓂[K] : Ideal ↥𝒪[K]).IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal _).isPrime
  have hbot : (𝓂[K] : Ideal ↥𝒪[K]) ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField ↥𝒪[K]
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h)
  have hA : Submodule.cardQuot (Ideal.span {(p : ↥𝒪[K])})
      = (p ^ absoluteInertiaDegree K) ^ absoluteRamificationIndex K := by
    rw [hpe, cardQuot_pow_of_prime hbot, Submodule.cardQuot_apply]
    congr 1
    rw [show Nat.card (↥𝒪[K] ⧸ (𝓂[K] : Ideal ↥𝒪[K])) = Nat.card 𝓀[K] from rfl,
      AbsoluteInertiaDegree.card_residueField_eq_pow K, hp]
  -- the same count through the free structure
  haveI : IsScalarTower ℤ_[p] ↥𝒪[K] ↥𝒪[K] :=
    ⟨fun c y z => by simp only [smul_eq_mul, hsmul]; ring⟩
  have hBset : ((p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] ↥𝒪[K]))
      = (Ideal.span {(p : ↥𝒪[K])}).restrictScalars ℤ_[p] := by
    ext z
    rw [Submodule.mem_smul_pointwise_iff_exists, Submodule.restrictScalars_mem,
      Ideal.mem_span_singleton]
    constructor
    · rintro ⟨w, -, rfl⟩
      exact ⟨w, by rw [hsmul, map_natCast]⟩
    · rintro ⟨w, rfl⟩
      exact ⟨w, trivial, by rw [hsmul, map_natCast]⟩
  have hmap : Submodule.map (b.equivFun : ↥𝒪[K] →ₗ[ℤ_[p]] (ι → ℤ_[p]))
      ((p : ℤ_[p]) • ⊤) = (p : ℤ_[p]) • ⊤ := by
    rw [Submodule.map_pointwise_smul, Submodule.map_top]
    congr 1
    exact LinearMap.range_eq_top.mpr b.equivFun.surjective
  have hpi : ((p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] (ι → ℤ_[p])))
      = Submodule.pi Set.univ (fun _ : ι => (p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] ℤ_[p])) := by
    ext c
    rw [Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_pi]
    constructor
    · rintro ⟨w, -, rfl⟩ i -
      exact ⟨w i, trivial, rfl⟩
    · intro h
      choose w hw hww using fun i => h i trivial
      exact ⟨fun i => w i, trivial, funext fun i => hww i⟩
  have hfactor : Nat.card (ℤ_[p] ⧸ ((p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] ℤ_[p]))) = p := by
    have hsp : ((p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] ℤ_[p])) = Ideal.span {(p : ℤ_[p])} := by
      ext z
      rw [Submodule.mem_smul_pointwise_iff_exists, Ideal.mem_span_singleton]
      constructor
      · rintro ⟨w, -, rfl⟩
        exact ⟨w, (smul_eq_mul _ _).symm⟩
      · rintro ⟨w, rfl⟩
        exact ⟨w, trivial, smul_eq_mul _ _⟩
    have hker : RingHom.ker (PadicInt.toZModPow (p := p) 1) = Ideal.span {(p : ℤ_[p])} := by
      rw [PadicInt.ker_toZModPow]
      norm_num
    have he := RingHom.quotientKerEquivOfSurjective
      (ZMod.ringHom_surjective (PadicInt.toZModPow (p := p) 1))
    have he2 : (ℤ_[p] ⧸ Ideal.span {(p : ℤ_[p])}) ≃+* ZMod (p ^ 1) :=
      (Ideal.quotEquivOfEq hker.symm).trans he
    rw [hsp, Nat.card_congr he2.toEquiv, Nat.card_zmod, pow_one]
  have hC : Submodule.cardQuot ((p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] ↥𝒪[K]))
      = p ^ Fintype.card ι := by
    have hq := Submodule.Quotient.equiv ((p : ℤ_[p]) • ⊤) ((p : ℤ_[p]) • ⊤)
      b.equivFun hmap
    rw [Submodule.cardQuot_apply, Nat.card_congr hq.toEquiv, hpi,
      Nat.card_congr (Submodule.quotientPi _).toEquiv, Nat.card_pi]
    simp [hfactor]
  have hBcard : Submodule.cardQuot ((p : ℤ_[p]) • (⊤ : Submodule ℤ_[p] ↥𝒪[K]))
      = Submodule.cardQuot (Ideal.span {(p : ↥𝒪[K])}) := by
    rw [hBset]
    rfl
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hcardι : Fintype.card ι = absoluteDegree K := by
    have hpow : p ^ Fintype.card ι
        = p ^ (absoluteInertiaDegree K * absoluteRamificationIndex K) := by
      rw [← hC, hBcard, hA, ← pow_mul]
    have := Nat.pow_right_injective hp2 hpow
    rw [this, absoluteDegree, Nat.mul_comm]
  -- assemble the topological isomorphism
  let er : (Fin (absoluteDegree K) → ℤ_[p]) ≃+ (ι → ℤ_[p]) :=
    { Equiv.arrowCongr (Fintype.equivFinOfCardEq hcardι).symm (Equiv.refl ℤ_[p]) with
      map_add' := fun _ _ => rfl }
  let E : (Fin (absoluteDegree K) → ℤ_[p]) ≃+ ↥𝒪[K] := er.trans b.equivFun.symm.toAddEquiv
  have hEcont : Continuous E := by
    have hE : ⇑E = fun c : Fin (absoluteDegree K) → ℤ_[p] =>
        ∑ i : ι, c (Fintype.equivFinOfCardEq hcardι i) • b i := by
      funext c
      change b.equivFun.symm _ = _
      rw [Module.Basis.equivFun_symm_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
    rw [hE]
    refine continuous_finsetSum _ fun i _ => ?_
    have hterm : (fun c : Fin (absoluteDegree K) → ℤ_[p] =>
        c (Fintype.equivFinOfCardEq hcardι i) • b i)
        = fun c => padicCoefficientEmbedding K p hp (c (Fintype.equivFinOfCardEq hcardι i))
            * b i := by
      funext c
      rw [hsmul]
    rw [hterm]
    exact ((PadicCoefficientEmbedding.continuous K p hp).comp
      (continuous_apply (Fintype.equivFinOfCardEq hcardι i))).mul continuous_const
  -- the inverse is continuous for free: compact source, Hausdorff target
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : T2Space K := inferInstance
  let h : (Fin (absoluteDegree K) → ℤ_[p]) ≃ₜ ↥𝒪[K] :=
    Continuous.homeoOfEquivCompactToT2 (f := E.toEquiv) hEcont
  exact ⟨{ E with continuous_toFun := hEcont, continuous_invFun := h.symm.continuous }⟩

end Atlas.Knowledge
