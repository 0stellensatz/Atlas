import Mathlib
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.PadicExpConvergence
import Atlas.Knowledge.PadicExpIsomorphism
import Atlas.Knowledge.ResidueCharacteristic

/-!
# topological exp isomorphism above the threshold

Above the threshold `e / (p - 1)`, the exponential bundles into an isomorphism of topological
groups: for `(p - 1) * i > e`, the additive group of the ideal power `𝓂 ^ i`, written
multiplicatively, is `≃ₜ*` to the higher unit group `U i (K)` of
`Atlas.Knowledge.HigherUnitGroup` in its subspace topology from `Kˣ`. This is the bundled form
of the unbundled exp/log package `Atlas.Knowledge.PadicExpIsomorphism`, and the shape its
consumers want: `Atlas.Knowledge.DeepUnitGroup` composes this isomorphism with the free
`ℤ_p`-module structure of the ideal power to make a deep unit group a free `ℤ_p`-module of rank
the absolute degree.

## Main statements

* `padicExpTopologicalIso` — above the threshold, `Multiplicative (𝓂 ^ i) ≃ₜ* U i (K)` as
  topological groups.

## Implementation notes

The isomorphism is packaged inside `Nonempty` because its sole consumer,
`Atlas.Knowledge.deepUnitGroup_continuousMulEquiv`, destructures the existence immediately and
composes the witness away; a consumer that needs the identity of the underlying map—it is the
exponential—takes it from `Atlas.Knowledge.padicExpIsomorphism`, where the bijection is
recorded on `NormedSpace.exp` by name. The witness
is assembled from `Atlas.Knowledge.padicExpIsomorphism`: `Set.BijOn.equiv` turns the bijection
into an equivalence between the ideal power and the higher unit group,
`Atlas.Knowledge.PadicExpIsomorphism.exp_add`—pulled from the convergence ideal down to level
`i` by inclusion—makes it multiplicative, and forward continuity is the norm preservation
`‖exp a - exp b‖ = ‖a - b‖`: above the threshold the exponential is an isometry, a consequence
of `exp_add` together with the estimate `‖exp x - 1‖ = ‖x‖` of
`Atlas.Knowledge.PadicExpIsomorphism.norm_exp_estimates`. The inverse is continuous for free:
`𝓂 ^ i` is a closed norm ball in the compact ring `𝒪[K]`, so the source is compact, the target
lives in the Hausdorff group `Kˣ`, and `Continuous.homeoOfEquivCompactToT2` upgrades the
continuous bijection to a homeomorphism. The statement is about the carrier topology; the proof
rebuilds the norm through `Valued.toNontriviallyNormedField`, whose topology is definitionally
the carrier's—the same discipline as the rest of this tranche.

## References

* [Koblitz1984] N. Koblitz, *p-adic numbers, p-adic analysis, and zeta-functions*, Graduate
  Texts in Mathematics **58**, Springer New York, 1984.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
/-- Above the threshold `e / (p - 1)`, the exponential is an isomorphism of topological groups
from the ideal power onto the higher unit group: for `(p - 1) * i > e`, the additive group
`𝓂 ^ i`, written multiplicatively, is `≃ₜ*` to `U i (K)`, both in their subspace topologies
([Koblitz 1984, Chap. IV, §1, Prop., p.81][Koblitz1984] for exp/log as mutually inverse
isomorphisms between the disc about `0` and the disc about `1`;
[Hyeon 2025, §4, p.17][Hyeon2025] for the isomorphism at a level). -/
theorem padicExpTopologicalIso (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsMixedCharLocalField K] (i : ℕ+)
    (hi : absoluteRamificationIndex K < (residueCharacteristic K - 1) * (i : ℕ)) :
    Nonempty (Multiplicative ↥(𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) ≃ₜ* ↥(higherUnitGroup K i)) := by
  have hp : (residueCharacteristic K).Prime := residueCharacteristic_prime K
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[K])
  have hbij := padicExpIsomorphism K i hi
  -- the per-level guard clears the convergence threshold, so `exp_add` applies at level `i`
  have hth : ∀ {z : ↥𝒪[K]}, z ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) →
      z ∈ (𝓂[K] ^ (absoluteRamificationIndex K / (residueCharacteristic K - 1) + 1) :
        Ideal ↥𝒪[K]) := by
    intro z hz
    refine Ideal.pow_le_pow_right ?_ hz
    have hD : 0 < residueCharacteristic K - 1 := by have := hp.two_le; omega
    have := (Nat.div_lt_iff_lt_mul hD).mpr (by rw [Nat.mul_comm] at hi; exact hi)
    omega
  -- the bare equivalence: into the image, across the bijection, back out of the image
  let eL := Equiv.Set.image ((↑) : ↥𝒪[K] → K)
    ((𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) : Set ↥𝒪[K]) Subtype.coe_injective
  let eM := Set.BijOn.equiv NormedSpace.exp hbij
  let eR := Equiv.Set.image ((↑) : Kˣ → K) (higherUnitGroup K i : Set Kˣ) Units.val_injective
  let E : ↥(𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) ≃ ↥(higherUnitGroup K i) :=
    (eL.trans eM).trans eR.symm
  have hEcoe : ∀ z : ↥(𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]),
      ((E z : Kˣ) : K) = NormedSpace.exp ((z : ↥𝒪[K]) : K) :=
    fun z => congrArg Subtype.val (eR.apply_symm_apply (eM (eL z)))
  -- the multiplicative structure: addition goes to multiplication through `exp_add`
  let M : Multiplicative ↥(𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) ≃* ↥(higherUnitGroup K i) :=
    { toFun := fun x => E x.toAdd
      invFun := fun u => Multiplicative.ofAdd (E.symm u)
      left_inv := fun x => congrArg Multiplicative.ofAdd (E.symm_apply_apply x.toAdd)
      right_inv := fun u => E.apply_symm_apply u
      map_mul' := fun x y => by
        refine Subtype.ext (Units.ext ?_)
        push_cast
        rw [hEcoe, hEcoe, hEcoe, toAdd_mul]
        have h := PadicExpIsomorphism.exp_add K (x.toAdd : ↥𝒪[K]) (y.toAdd : ↥𝒪[K])
          (hth x.toAdd.2) (hth y.toAdd.2)
        rw [← h]
        norm_cast }
  -- Rebuild the normed structure; its topology is the given one.
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : CompleteSpace K := inferInstance
  haveI : IsUltrametricDist K := inferInstance
  have hc : ∀ z : K, ‖z‖ ≤ 1 ↔ valuation K z ≤ 1 := fun z => Valued.toNormedField.norm_le_one_iff
  have hpe := span_residueCharacteristic_eq_maximalIdeal_pow K
  have hc0 : 0 < ‖((ϖ : ↥𝒪[K]) : K)‖ := by
    rw [norm_pos_iff]; simpa using hϖ.ne_zero
  have hc1 : ‖((ϖ : ↥𝒪[K]) : K)‖ < 1 := by
    rw [RationalIntegerValuation.norm_lt_one_iff_valuation_lt_one hc]
    exact valuation_lt_one_of_mem_maximalIdeal _
      (by rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ)
  have hmn := PadicExpConvergence.mem_pow_iff_norm_le hc hϖ hc0 hc1
  have hkey : ∀ {z : ↥𝒪[K]}, z ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) →
      ‖NormedSpace.exp (z : K) - 1‖ = ‖(z : K)‖ :=
    fun {z} hz => (PadicExpIsomorphism.norm_exp_estimates hc hp hpe hϖ hi hz).2
  have hlt1 : ∀ {z : ↥𝒪[K]}, z ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) → ‖(z : K)‖ < 1 := by
    intro z hz
    rw [RationalIntegerValuation.norm_lt_one_iff_valuation_lt_one hc]
    exact valuation_lt_one_of_mem_maximalIdeal _ (Ideal.pow_le_self i.pos.ne' hz)
  have hnormexp : ∀ {z : ↥𝒪[K]}, z ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) →
      ‖NormedSpace.exp (z : K)‖ = 1 := by
    intro z hz
    have h1 : NormedSpace.exp (z : K) = 1 + (NormedSpace.exp (z : K) - 1) := by ring
    rw [h1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by
      rw [norm_one, hkey hz]; exact fun h => absurd h.symm (hlt1 hz).ne)]
    simp [hkey hz, (hlt1 hz).le]
  -- the exponential moves points by exactly their distance
  have hdist : ∀ a b : ↥𝒪[K], a ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) →
      b ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) →
      ‖NormedSpace.exp (a : K) - NormedSpace.exp (b : K)‖ = ‖(a : K) - (b : K)‖ := by
    intro a b ha hb
    have hbne : NormedSpace.exp ((b : ↥𝒪[K]) : K) ≠ 0 := by
      intro h
      have := hnormexp hb
      rw [h, norm_zero] at this
      exact zero_ne_one this
    have hd : a - b ∈ (𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) := sub_mem ha hb
    have hsum : ((a - b : ↥𝒪[K]) : K) + ((b : ↥𝒪[K]) : K) = ((a : ↥𝒪[K]) : K) := by
      push_cast; ring
    have hs := PadicExpIsomorphism.exp_add K (a - b) b (hth hd) (hth hb)
    rw [hsum] at hs
    have heq : NormedSpace.exp ((a - b : ↥𝒪[K]) : K) - 1
        = (NormedSpace.exp ((a : ↥𝒪[K]) : K) - NormedSpace.exp ((b : ↥𝒪[K]) : K))
          * (NormedSpace.exp ((b : ↥𝒪[K]) : K))⁻¹ := by
      rw [eq_comm, ← div_eq_mul_inv, div_eq_iff hbne]
      linear_combination hs
    have hnd := hkey hd
    rw [heq, norm_mul, norm_inv, hnormexp hb, inv_one, mul_one] at hnd
    rw [hnd]
    push_cast
    ring_nf
  -- forward continuity: an isometry into the field, then through the units embedding
  have hiso : Isometry (fun z : ↥(𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) =>
      NormedSpace.exp ((z : ↥𝒪[K]) : K)) := by
    refine Isometry.of_dist_eq fun a b => ?_
    have hab : dist a b = ‖((a : ↥𝒪[K]) : K) - ((b : ↥𝒪[K]) : K)‖ := by
      rw [Subtype.dist_eq, Subtype.dist_eq, dist_eq_norm]
    rw [dist_eq_norm, hab]
    exact hdist a.1 b.1 a.2 b.2
  have hcont1 : Continuous fun z : ↥(𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) => ((E z : Kˣ) : K) :=
    hiso.continuous.congr fun z => (hEcoe z).symm
  have hcont2 : Continuous fun z : ↥(𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) => (E z : Kˣ) :=
    (Units.isEmbedding_val₀.continuous_iff).mpr hcont1
  have hEcont : Continuous fun z : ↥(𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) => E z :=
    hcont2.subtype_mk fun z => (E z).2
  have hMcont : Continuous fun x : Multiplicative ↥(𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) =>
      E x.toAdd := hEcont.comp continuous_toAdd
  -- the source is compact: the ideal power is a closed norm ball in the compact integer ring
  have hSclosed : IsClosed ((𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) : Set ↥𝒪[K]) := by
    have hset : ((𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) : Set ↥𝒪[K])
        = (fun z : ↥𝒪[K] => ‖(z : K)‖) ⁻¹' Set.Iic (‖((ϖ : ↥𝒪[K]) : K)‖ ^ (i : ℕ)) := by
      ext z
      simpa using hmn z (i : ℕ)
    rw [hset]
    exact isClosed_Iic.preimage (continuous_subtype_val.norm)
  haveI : CompactSpace ↥(𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) :=
    isCompact_iff_compactSpace.mp hSclosed.isCompact
  -- the target is Hausdorff: `K` is metric under the rebuilt norm, and `Kˣ` embeds into it
  haveI : T2Space K := by
    letI hm : MetricSpace K := inferInstance
    have h : @T2Space K hm.toUniformSpace.toTopologicalSpace := inferInstance
    exact h
  -- inverse continuity is free: a continuous bijection from a compact space to a Hausdorff one
  let homeo : Multiplicative ↥(𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) ≃ₜ ↥(higherUnitGroup K i) :=
    hMcont.homeoOfEquivCompactToT2 (f := M.toEquiv)
  exact ⟨{ toMulEquiv := M
           continuous_toFun := hMcont
           continuous_invFun := homeo.symm.continuous }⟩

end Atlas.Knowledge
