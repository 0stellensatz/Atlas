import Mathlib
import Atlas.Knowledge.HerbrandQuotient
import Atlas.Knowledge.NormalizedValuationAlgEquiv
import Atlas.Knowledge.PadicExpIsomorphism

/-!
# equivariant exponential at a deep level

The deep exponential of `Atlas.Knowledge.padicExpIsomorphism`, bundled into a multiplicative
equivalence and made Galois-equivariant: above the threshold, `exp` is a `MulEquiv` from the
additively-read ideal power `𝓂 ^ i` onto the higher unit group `U i`, a `K`-automorphism of
the extension acts on both sides — on the ideal power through its restriction to the
integers, on the unit level through the unit action — and the exponential intertwines the
two. This is the bridge that carries the graded pieces of a deep unit level of
`Atlas.Knowledge.herbrandQuotient` onto the additive side, where the normal-basis lattice
computes them; equivariance holds because an automorphism is a continuous ℚ-algebra map
(`Atlas.Knowledge.continuous_algEquiv`) and the exponential series has rational
coefficients.

## Main definitions

* `expLevel` — the deep exponential as a `MulEquiv` `Multiplicative (𝓂 ^ i) ≃* U i`.
* `galIdealPow` — the additive action of a `K`-automorphism on a deep ideal power.

## Main statements

* `exp_algEquiv` — `σ ∘ exp = exp ∘ σ`; proved.
* `expLevel_intertwines` — the exponential intertwines the restricted unit action with the
  additive action; proved.
* `algEquivIntegerRestrict_mem_pow` / `galUnits_mem_higherUnitGroup` — the automorphism
  preserves the ideal powers and the unit levels; proved.
* `algEquivIntegerRestrict_map_maximalIdeal` — the automorphism fixes the maximal ideal;
  proved.
* `deep_le_threshold` — a deep level lies inside the exponential's convergence ideal;
  proved.

## Implementation notes

The `MulEquiv` is assembled from the layer's named `Set.BijOn` through the coercion
equivalences of the two subtypes, so its underlying map is the exponential by construction
— `expLevelEquiv_coe` is `Equiv.apply_symm_apply` read through the coercions — and the
homomorphism law is `Atlas.Knowledge.PadicExpIsomorphism.exp_add` under the containment
`deep_le_threshold` of the level in the convergence ideal. The equivariance of the series
runs through `Function.LeftInverse.map_tsum` at the automorphism — a homeomorphism by
`Atlas.Knowledge.continuous_algEquiv` — with no summability hypothesis: an unsummable series
maps junk to junk. The unit-level action is deliberately the `stableRestrict` of
`Atlas.Knowledge.HerbrandQuotient` at the unit action of the extension, so the intertwining
plugs into `card_H0_congr` and `card_H1_congr` with no adapter.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [FesenkoVostokov2002] I. B. Fesenko, S. V. Vostokov, *Local fields and their extensions*,
  Translations of Mathematical Monographs **121**, American Mathematical Society, second
  edition, 2002.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic
  local fields*, J. London Math. Soc. **112** (2025), e70402.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open ValuativeRel Nat

namespace Atlas.Knowledge

section SingleField

variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsMixedCharLocalField F]

/- The two coercion equivalences: the ideal-power subtype onto its field image, and the
unit level onto its image. -/
private noncomputable def idealImageEquiv (i : ℕ+) :
    ↥(𝓂[F] ^ (i : ℕ) : Ideal ↥𝒪[F]) ≃
      ↥((((↑) : ↥𝒪[F] → F) '' ((𝓂[F] ^ (i : ℕ) : Ideal ↥𝒪[F]) : Set ↥𝒪[F]))) :=
  Equiv.Set.imageOfInjOn _ _ (fun _ _ _ _ hab => Subtype.ext hab)

private noncomputable def unitsImageEquiv (i : ℕ+) :
    ↥(higherUnitGroup F i) ≃ ↥((((↑) : Fˣ → F) '' (higherUnitGroup F i : Set Fˣ))) :=
  Equiv.Set.imageOfInjOn _ _ (fun _ _ _ _ hab => Units.ext hab)

/- The exponential at a deep level, as a bare equivalence. -/
private noncomputable def expLevelEquiv (i : ℕ+)
    (hi : absoluteRamificationIndex F < (residueCharacteristic F - 1) * (i : ℕ)) :
    ↥(𝓂[F] ^ (i : ℕ) : Ideal ↥𝒪[F]) ≃ ↥(higherUnitGroup F i) :=
  ((idealImageEquiv F i).trans ((padicExpIsomorphism F i hi).equiv _)).trans
    (unitsImageEquiv F i).symm

/- The deep-level equivalence is the exponential, pointwise. -/
private theorem expLevelEquiv_coe (i : ℕ+)
    (hi : absoluteRamificationIndex F < (residueCharacteristic F - 1) * (i : ℕ))
    (m : ↥(𝓂[F] ^ (i : ℕ) : Ideal ↥𝒪[F])) :
    ((expLevelEquiv F i hi m : Fˣ) : F) = NormedSpace.exp ((m : ↥𝒪[F]) : F) :=
  congrArg Subtype.val ((unitsImageEquiv F i).apply_symm_apply
    (((idealImageEquiv F i).trans ((padicExpIsomorphism F i hi).equiv _)) m))

/-- Deepness clears the convergence threshold. -/
theorem deep_le_threshold (i : ℕ+)
    (hi : absoluteRamificationIndex F < (residueCharacteristic F - 1) * (i : ℕ)) :
    (𝓂[F] ^ (i : ℕ) : Ideal ↥𝒪[F]) ≤
      (𝓂[F] ^ (absoluteRamificationIndex F / (residueCharacteristic F - 1) + 1) :
        Ideal ↥𝒪[F]) := by
  refine Ideal.pow_le_pow_right ?_
  have hp : 0 < residueCharacteristic F - 1 := by
    have := (residueCharacteristic_prime F).two_le
    omega
  have h2 : absoluteRamificationIndex F < (i : ℕ) * (residueCharacteristic F - 1) := by
    rw [mul_comm]
    exact hi
  have := (Nat.div_lt_iff_lt_mul hp).mpr h2
  omega

/-- **The exponential at a deep level, as a multiplicative equivalence**: the layer's
`Set.BijOn` bundled, with `Atlas.Knowledge.PadicExpIsomorphism.exp_add` giving the
homomorphism law ([Fesenko–Vostokov 2002, Chap. VI, (1.4), p.212][FesenkoVostokov2002];
[Hyeon 2025, §4, p.17][Hyeon2025]). -/
noncomputable def expLevel (i : ℕ+)
    (hi : absoluteRamificationIndex F < (residueCharacteristic F - 1) * (i : ℕ)) :
    Multiplicative ↥(𝓂[F] ^ (i : ℕ) : Ideal ↥𝒪[F]) ≃* ↥(higherUnitGroup F i) where
  toFun m := expLevelEquiv F i hi (Multiplicative.toAdd m)
  invFun u := Multiplicative.ofAdd ((expLevelEquiv F i hi).symm u)
  left_inv m := by
    change Multiplicative.ofAdd ((expLevelEquiv F i hi).symm
      ((expLevelEquiv F i hi) (Multiplicative.toAdd m))) = m
    rw [Equiv.symm_apply_apply]
    rfl
  right_inv u := by
    change (expLevelEquiv F i hi) (Multiplicative.toAdd
      (Multiplicative.ofAdd ((expLevelEquiv F i hi).symm u))) = u
    rw [toAdd_ofAdd, Equiv.apply_symm_apply]
  map_mul' m₁ m₂ := by
    set a₁ := Multiplicative.toAdd m₁ with ha₁
    set a₂ := Multiplicative.toAdd m₂ with ha₂
    refine Subtype.ext (Units.ext ?_)
    have htoadd : Multiplicative.toAdd (m₁ * m₂) = a₁ + a₂ := rfl
    change ((((expLevelEquiv F i hi) (Multiplicative.toAdd (m₁ * m₂))) : Fˣ) : F) =
      ((((expLevelEquiv F i hi) a₁ : Fˣ) * ((expLevelEquiv F i hi) a₂ : Fˣ)) : F)
    rw [htoadd]
    have h1 : ((((expLevelEquiv F i hi) (a₁ + a₂)) : Fˣ) : F) =
        NormedSpace.exp (((a₁ + a₂ : ↥(𝓂[F] ^ (i : ℕ) : Ideal ↥𝒪[F])) : ↥𝒪[F]) : F) :=
      expLevelEquiv_coe F i hi _
    have hadd : ((((a₁ + a₂ : ↥(𝓂[F] ^ (i : ℕ) : Ideal ↥𝒪[F])) : ↥𝒪[F])) : F) =
        ((a₁ : ↥𝒪[F]) : F) + ((a₂ : ↥𝒪[F]) : F) := by
      push_cast
      rfl
    rw [hadd] at h1
    rw [PadicExpIsomorphism.exp_add F _ _ (deep_le_threshold F i hi a₁.2)
      (deep_le_threshold F i hi a₂.2)] at h1
    rw [h1, expLevelEquiv_coe F i hi, expLevelEquiv_coe F i hi]

end SingleField

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [Algebra K L]
  [ValuativeExtension K L] [IsValuativeTopology L] [FiniteDimensional K L]
  [IsMixedCharLocalField L]

omit [IsValuativeTopology L] in
/-- **The exponential is equivariant**: a `K`-automorphism is a continuous ℚ-algebra map,
and the series has rational coefficients — the exponential side of the equivariant
logarithm diagram ([Hyeon 2025, §4, p.15][Hyeon2025]). -/
theorem exp_algEquiv (σ : L ≃ₐ[K] L) (x : L) :
    σ (NormedSpace.exp x) = NormedSpace.exp (σ x) := by
  letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  haveI : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := L)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := L).comp MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField L := Valued.toNontriviallyNormedField L (ValueGroupWithZero L)
  haveI : T2Space L := inferInstance
  rw [NormedSpace.exp_eq_tsum_rat]
  have hmap : σ (∑' n : ℕ, (n !⁻¹ : ℚ) • x ^ n) =
      ∑' n : ℕ, σ ((n !⁻¹ : ℚ) • x ^ n) :=
    Function.LeftInverse.map_tsum _ (continuous_algEquiv K L σ)
      (continuous_algEquiv K L σ.symm) σ.symm_apply_apply (g := σ.toAlgHom.toAddMonoidHom)
  have hterm : ∀ n : ℕ, σ ((n !⁻¹ : ℚ) • x ^ n) = (n !⁻¹ : ℚ) • (σ x) ^ n := by
    intro n
    rw [Rat.smul_def, Rat.smul_def, map_mul, map_pow, map_ratCast]
  calc σ (∑' n : ℕ, (n !⁻¹ : ℚ) • x ^ n) = ∑' n : ℕ, σ ((n !⁻¹ : ℚ) • x ^ n) := hmap
    _ = ∑' n : ℕ, (n !⁻¹ : ℚ) • (σ x) ^ n := tsum_congr hterm

section Equivariant

omit [IsValuativeTopology L] in
/-- The restricted automorphism preserves the maximal ideal
([Serre 1979, Chap. II, §2, Cor. 2–3, p.29][Serre1979]). -/
theorem algEquivIntegerRestrict_map_maximalIdeal (σ : L ≃ₐ[K] L) :
    Ideal.map (algEquivIntegerRestrict K L σ : ↥𝒪[L] →+* ↥𝒪[L])
      (IsLocalRing.maximalIdeal ↥𝒪[L]) = IsLocalRing.maximalIdeal ↥𝒪[L] := by
  have hmax : (Ideal.map (algEquivIntegerRestrict K L σ : ↥𝒪[L] →+* ↥𝒪[L])
      (IsLocalRing.maximalIdeal ↥𝒪[L])).IsMaximal := by
    rw [Ideal.map_comap_of_equiv]
    exact Ideal.comap_isMaximal_of_surjective _
      (algEquivIntegerRestrict K L σ).symm.surjective
  exact IsLocalRing.eq_maximalIdeal hmax

omit [IsValuativeTopology L] in
/-- The restricted automorphism preserves the ideal powers. -/
theorem algEquivIntegerRestrict_mem_pow (σ : L ≃ₐ[K] L) (i : ℕ) {x : ↥𝒪[L]}
    (hx : x ∈ (𝓂[L] ^ i : Ideal ↥𝒪[L])) :
    algEquivIntegerRestrict K L σ x ∈ (𝓂[L] ^ i : Ideal ↥𝒪[L]) := by
  have h1 : algEquivIntegerRestrict K L σ x ∈
      Ideal.map (algEquivIntegerRestrict K L σ : ↥𝒪[L] →+* ↥𝒪[L])
        ((𝓂[L] : Ideal ↥𝒪[L]) ^ i) :=
    Ideal.mem_map_of_mem _ hx
  rwa [Ideal.map_pow, algEquivIntegerRestrict_map_maximalIdeal K L σ] at h1

omit [IsValuativeTopology L] in
/-- The unit action preserves the higher unit groups
(Yamaguchi 2026,
`LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean:90`,
the stability this level-wise form feeds). -/
theorem galUnits_mem_higherUnitGroup (σ : L ≃ₐ[K] L) (i : ℕ+) {u : Lˣ}
    (hu : u ∈ higherUnitGroup L i) :
    Units.mapEquiv σ.toMulEquiv u ∈ higherUnitGroup L i := by
  obtain ⟨m, hm⟩ := hu
  refine ⟨⟨algEquivIntegerRestrict K L σ (m : ↥𝒪[L]),
    algEquivIntegerRestrict_mem_pow K L σ (i : ℕ) m.2⟩, ?_⟩
  have hσ1 : σ ((1 : L) + ((m : ↥𝒪[L]) : L)) = σ ((u : Lˣ) : L) := congrArg σ hm
  rw [map_add, map_one] at hσ1
  exact hσ1

set_option linter.overlappingInstances false in
-- The section's `[IsValuativeTopology L]` is implied by `[IsMixedCharLocalField L]` here, and
-- Lean already prunes the unused binder from the signature; the linter reads the section's
-- binder list and fires regardless of `omit`, so it is silenced instead.
/-- The additive action of a `K`-automorphism on a deep ideal power. -/
noncomputable def galIdealPow (σ : L ≃ₐ[K] L) (i : ℕ) :
    ↥(𝓂[L] ^ i : Ideal ↥𝒪[L]) ≃+ ↥(𝓂[L] ^ i : Ideal ↥𝒪[L]) where
  toFun x := ⟨algEquivIntegerRestrict K L σ x,
    algEquivIntegerRestrict_mem_pow K L σ i x.2⟩
  invFun x := ⟨algEquivIntegerRestrict K L σ.symm x,
    algEquivIntegerRestrict_mem_pow K L σ.symm i x.2⟩
  left_inv x := by
    refine Subtype.ext (Subtype.ext ?_)
    exact σ.symm_apply_apply _
  right_inv x := by
    refine Subtype.ext (Subtype.ext ?_)
    exact σ.apply_symm_apply _
  map_add' x y := Subtype.ext (map_add _ _ _)

omit [IsValuativeTopology L] in
/-- **The exponential intertwines the two actions at a deep level**: the restricted unit
action corresponds to the additive action across `Atlas.Knowledge.expLevel` — what carries
the graded counts of a deep unit level onto the additive side
([Hyeon 2025, §4, p.15][Hyeon2025]). -/
theorem expLevel_intertwines (σ : L ≃ₐ[K] L) (i : ℕ+)
    (hi : absoluteRamificationIndex L < (residueCharacteristic L - 1) * (i : ℕ))
    (m : Multiplicative ↥(𝓂[L] ^ (i : ℕ) : Ideal ↥𝒪[L])) :
    HerbrandQuotient.stableRestrict (Units.mapEquiv σ.toMulEquiv) (higherUnitGroup L i)
        (fun _ hu => galUnits_mem_higherUnitGroup K L σ i hu)
        (fun _ hu => galUnits_mem_higherUnitGroup K L σ.symm i hu)
        (expLevel L i hi m) =
      expLevel L i hi
        (Multiplicative.ofAdd (galIdealPow K L σ (i : ℕ) (Multiplicative.toAdd m))) := by
  refine Subtype.ext (Units.ext ?_)
  have hLHS : (((HerbrandQuotient.stableRestrict (Units.mapEquiv σ.toMulEquiv)
      (higherUnitGroup L i)
      (fun _ hu => galUnits_mem_higherUnitGroup K L σ i hu)
      (fun _ hu => galUnits_mem_higherUnitGroup K L σ.symm i hu)
      (expLevel L i hi m) : ↥(higherUnitGroup L i)) : Lˣ) : L) =
      σ (((expLevel L i hi m : Lˣ) : L)) := rfl
  have hcoe1 : (((expLevel L i hi m : Lˣ)) : L) =
      NormedSpace.exp ((((Multiplicative.toAdd m :
        ↥(𝓂[L] ^ (i : ℕ) : Ideal ↥𝒪[L])) : ↥𝒪[L])) : L) :=
    expLevelEquiv_coe L i hi _
  have hcoe2 : (((expLevel L i hi
      (Multiplicative.ofAdd (galIdealPow K L σ (i : ℕ) (Multiplicative.toAdd m))) :
        Lˣ)) : L) =
      NormedSpace.exp (((galIdealPow K L σ (i : ℕ) (Multiplicative.toAdd m) :
        ↥𝒪[L])) : L) := by
    have := expLevelEquiv_coe L i hi
      (Multiplicative.toAdd
        (Multiplicative.ofAdd (galIdealPow K L σ (i : ℕ) (Multiplicative.toAdd m))))
    rwa [toAdd_ofAdd] at this
  have hgal : (((galIdealPow K L σ (i : ℕ) (Multiplicative.toAdd m) : ↥𝒪[L])) : L) =
      σ ((((Multiplicative.toAdd m :
        ↥(𝓂[L] ^ (i : ℕ) : Ideal ↥𝒪[L])) : ↥𝒪[L])) : L) := rfl
  rw [hLHS, hcoe1, hcoe2, hgal, exp_algEquiv K L σ]

end Equivariant

end Atlas.Knowledge
