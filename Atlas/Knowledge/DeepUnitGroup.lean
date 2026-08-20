import Mathlib
import Atlas.Knowledge.AbsoluteDegree
import Atlas.Knowledge.AbsoluteRamificationIndex
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.PadicExpTopologicalIso
import Atlas.Knowledge.PadicIntegerFreeModule
import Atlas.Knowledge.ResidueCharacteristic

/-!
# deep unit group

The higher unit groups above the threshold `e / (p - 1)`—the deep unit groups—are free
`ℤ_p`-modules of rank the absolute degree: for `(p - 1) * i > e`, `U i (K)` of
`Atlas.Knowledge.HigherUnitGroup` is topologically isomorphic to `d` copies of `ℤ_[p]`, for
`d = e * f` the absolute degree `Atlas.Knowledge.AbsoluteDegree`. The exp/log pair of
`Atlas.Knowledge.PadicExpIsomorphism` does the work: it identifies `U i (K)` with the ideal
power `𝓂 ^ i`, a free module of rank `d` over `ℤ_p`. This is the free-rank engine of the
anabelian layer—reading the rank `d` off a deep open subgroup of the unit group is how the
absolute degree becomes group-theoretic, which is what the recovery claims of
`Atlas.Knowledge.AbsoluteGaloisInvariance` consume through local class field theory.

## Main statements

* `deepUnitGroup_continuousMulEquiv` — a deep unit group is topologically isomorphic to
  `Multiplicative (Fin d → ℤ_[p])`.
* `DeepUnitGroup.integer_continuousAddEquiv_ideal_pow` — multiplication by `ϖ ^ i` identifies
  the valuation ring with the `i`th power of its maximal ideal, topologically; the bridge the
  composition crosses between `Atlas.Knowledge.padicIntegerFreeModule` and the level.

## Implementation notes

The free `ℤ_p`-module structure is encoded as a topological group isomorphism onto
`Multiplicative (Fin d → ℤ_[p])`: on a pro-`p` abelian topological group the `ℤ_p`-action is the
continuous extension of the `ℤ`-power maps, so the topological group structure already
determines the module structure and a `≃ₜ*` carries the full statement without a module
instance on a subgroup of `Kˣ`. The prime enters as a variable `p` pinned to
`Atlas.Knowledge.ResidueCharacteristic` by an equation, because the notation `ℤ_[p]` requires a
`Fact p.Prime` instance that a projection like `residueCharacteristic K` cannot carry by
itself. Deepness is the same integer inequality `e < (p - 1) * i` as in
`Atlas.Knowledge.PadicExpIsomorphism`; it is also what makes the group torsion-free, a `p`-th
root of unity having valuation exactly the threshold and therefore lying in no deep level. The
structure of the full principal-unit group `U 1 (K)`—the free part of rank `d` against its
torsion—is the filtered-module business of the arithmetic tranche and is deliberately not
recorded here.

The proof is a composition of three isomorphisms built upstream: the exponential of
`Atlas.Knowledge.PadicExpTopologicalIso` identifies the deep level with the additive ideal
power; multiplication by `ϖ ^ i` identifies the ideal power with the whole valuation ring,
which is where the level ceases to matter; and `Atlas.Knowledge.padicIntegerFreeModule`
carries the valuation ring onto `Fin d → ℤ_[p]` through the coefficient embedding. Each leg's
inverse is continuous for free—compact source, Hausdorff target—so the composite is a `≃ₜ*`
with no open-mapping argument anywhere.

## References

* [FesenkoVostokov2002] I. B. Fesenko, S. V. Vostokov, *Local fields and their extensions*,
  Translations of Mathematical Monographs **121**, American Mathematical Society, second
  edition, 2002.
* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

namespace DeepUnitGroup

set_option synthInstance.maxHeartbeats 80000 in
-- The ideal arithmetic on `↥𝒪[K]` does not fit the default instance budget.
/-- Multiplication by `ϖ ^ i` identifies the valuation ring with the `i`th ideal power as
topological additive groups: injective because the ring is a domain, surjective because the
maximal ideal is principal, and inverse-continuous because the source is compact. -/
theorem integer_continuousAddEquiv_ideal_pow (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] (i : ℕ) :
    Nonempty (↥𝒪[K] ≃ₜ+ ↥(𝓂[K] ^ i : Ideal ↥𝒪[K])) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[K])
  have hspan : (𝓂[K] ^ i : Ideal ↥𝒪[K]) = Ideal.span {ϖ ^ i} := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  have hne : ϖ ^ i ≠ 0 := pow_ne_zero i hϖ.ne_zero
  have hmem : ∀ z : ↥𝒪[K], ϖ ^ i * z ∈ (𝓂[K] ^ i : Ideal ↥𝒪[K]) := fun z => by
    rw [hspan, Ideal.mem_span_singleton]
    exact Dvd.intro z rfl
  have hbij : Function.Bijective
      (fun z : ↥𝒪[K] => (⟨ϖ ^ i * z, hmem z⟩ : ↥(𝓂[K] ^ i : Ideal ↥𝒪[K]))) := by
    constructor
    · intro a b hab
      have := congrArg (Subtype.val) hab
      exact mul_left_cancel₀ hne this
    · rintro ⟨y, hy⟩
      rw [hspan, Ideal.mem_span_singleton] at hy
      obtain ⟨z, rfl⟩ := hy
      exact ⟨z, rfl⟩
  let E : ↥𝒪[K] ≃+ ↥(𝓂[K] ^ i : Ideal ↥𝒪[K]) :=
    { Equiv.ofBijective _ hbij with
      map_add' := fun a b => by
        ext
        simp [Equiv.ofBijective_apply, mul_add] }
  have hcont : Continuous E := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_const.mul continuous_subtype_val).subtype_mk _
  -- Rebuild the normed structure to reach a `T2Space` instance for the carrier topology.
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  haveI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := K)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K := Valued.toNontriviallyNormedField K (ValueGroupWithZero K)
  haveI : T2Space K := inferInstance
  let h : ↥𝒪[K] ≃ₜ ↥(𝓂[K] ^ i : Ideal ↥𝒪[K]) :=
    Continuous.homeoOfEquivCompactToT2 (f := E.toEquiv) hcont
  exact ⟨{ E with continuous_toFun := hcont, continuous_invFun := h.symm.continuous }⟩

end DeepUnitGroup

/-- A **deep unit group** is free of rank the absolute degree: for `(p - 1) * i > e`, the
higher unit group `U i (K)`, in its subspace topology, is topologically isomorphic to
`Multiplicative (Fin d → ℤ_[p])` for `d = e * f` the absolute degree—the exponential
identifying it with `𝓂 ^ i`, which the coefficient embedding makes `d` copies of `ℤ_[p]`
([Fesenko–Vostokov 2002, Chap. I, (6.1) and (6.5), pp.17–20][FesenkoVostokov2002] for the
`ℤ_p`-structure and the rank-`e * f` free part of `U 1 (K)`;
[Mochizuki 1997, §1, p.501][Mochizuki1997] for the logarithm identifying a deep open subgroup
of the units with an open subgroup of `K`; [Hyeon 2025, §4, p.17][Hyeon2025] for the level
isomorphism). -/
theorem deepUnitGroup_continuousMulEquiv (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] (p : ℕ) [Fact p.Prime]
    (hp : residueCharacteristic K = p) (i : ℕ+)
    (hi : absoluteRamificationIndex K < (p - 1) * (i : ℕ)) :
    Nonempty (↥(higherUnitGroup K i) ≃ₜ* Multiplicative (Fin (absoluteDegree K) → ℤ_[p])) := by
  rw [← hp] at hi
  obtain ⟨e₁⟩ := padicExpTopologicalIso K i hi
  obtain ⟨e₂⟩ := padicIntegerFreeModule K p hp
  obtain ⟨e₃⟩ := DeepUnitGroup.integer_continuousAddEquiv_ideal_pow K (i : ℕ)
  let e₄ := e₂.trans e₃
  let e₅ : Multiplicative (Fin (absoluteDegree K) → ℤ_[p])
      ≃ₜ* Multiplicative ↥(𝓂[K] ^ (i : ℕ) : Ideal ↥𝒪[K]) :=
    { AddEquiv.toMultiplicative e₄.toAddEquiv with
      continuous_toFun := e₄.continuous_toFun
      continuous_invFun := e₄.continuous_invFun }
  exact ⟨(e₅.trans e₁).symm⟩

end Atlas.Knowledge
