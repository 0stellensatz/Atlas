import Mathlib
import Atlas.Knowledge.IsArithmeticFrobenius
import Atlas.Knowledge.MapMaximalIdealEqPowCardInertia
import Atlas.Knowledge.NormIndexCyclic
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.NormalizedValuationAlgEquiv

/-!
# norm range of an unramified extension

The norm subgroup of a finite Galois unramified extension of mixed-characteristic local
fields is the full preimage of the degree's multiples under the normalized valuation:
`N Lˣ = v⁻¹ (n ℤ)`. With trivial inertia a base uniformizer stays a uniformizer, so the
embedding preserves the normalized valuation and a norm's value is the degree times the
value upstairs; the containment then closes by index counting against the class field
axiom `Atlas.Knowledge.normIndexCyclic`, both sides having index exactly the degree. This
is the unramified floor of the reciprocity map: on it the Frobenius-normalized map
`x ↦ σ ^ v (x)` of `Atlas.Knowledge.IsFrobeniusNormalized` has the right kernel.

## Main statements

* `normalizedValuation_algebraMap_of_unramified` — the embedding preserves the normalized
  valuation, `e = 1`; proved.
* `normalizedValuation_norm_of_unramified` — a norm's value is the degree times the value;
  proved.
* `unramifiedNormRange` — `N Lˣ` is the preimage of the degree's powers; proved.

## Implementation notes

The unramified input enters once, as the ideal identity
`Atlas.Knowledge.map_maximalIdeal_eq_pow_card_inertia` read at `E = K` with the inertia
group trivial, transported to the layer's own carriers `𝒪[K] → 𝒪[L]` along the
`Atlas.Knowledge.integerEquivIntegralClosure` identification and its base analogue —
`Ideal.map` only depends on the underlying
function, which the private `map_congr_fn` records. The trivial self-extension
`ValuativeExtension K K` is not an instance at the pin and is provided inline. The final
counting runs through the reduction of `Kˣ` to `ZMod n` along the bundled valuation, and
`Subgroup.relIndex_mul_index` turns equal finite indices plus one containment into
equality.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer
  New York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L] [Algebra K L]
  [ValuativeExtension K L] [FiniteDimensional K L] [IsMixedCharLocalField L] [IsGalois K L]

/- The identification of the base integers with their integral closure in the base. -/
private noncomputable def baseEquiv : integralClosure ↥𝒪[K] K ≃+* ↥𝒪[K] :=
  (IsIntegralClosure.equiv ↥𝒪[K] (integralClosure ↥𝒪[K] K) K ↥𝒪[K]).toRingEquiv

/- Ideal images depend only on the underlying function of the map. -/
private theorem map_congr_fn {R S : Type*} [Semiring R] [Semiring S]
    {F G : Type*} [FunLike F R S] [FunLike G R S] (f : F) (g : G)
    (hfg : ⇑f = ⇑g) (I : Ideal R) : Ideal.map f I = Ideal.map g I := by
  unfold Ideal.map
  rw [hfg]

/- The unramified ideal identity on the layer's own carriers: with trivial inertia, the
maximal ideal of the base generates the maximal ideal upstairs. -/
private theorem map_maximalIdeal_of_unramified
    (h : lowerRamificationGroup K L 0 = ⊥) :
    Ideal.map (algebraMap ↥𝒪[K] ↥𝒪[L]) 𝓂[K] = 𝓂[L] := by
  haveI : ValuativeExtension K K := ⟨fun _ _ => Iff.rfl⟩
  have hKL := map_maximalIdeal_eq_pow_card_inertia K L K
  rw [h, Subgroup.card_bot, pow_one] at hKL
  have hbase : ∀ r : ↥𝒪[K], ((algebraMap ↥𝒪[K] ↥𝒪[L] r : ↥𝒪[L]) : L) =
      algebraMap K L (r : K) := by
    intro r
    have h1 := IsScalarTower.algebraMap_apply ↥𝒪[K] ↥𝒪[L] L r
    have h2 := IsScalarTower.algebraMap_apply ↥𝒪[K] K L r
    rw [h1] at h2
    exact h2.symm
  have hfn : ∀ z : integralClosure ↥𝒪[K] K,
      algebraMap ↥𝒪[K] ↥𝒪[L] (baseEquiv K z) =
        integerEquivIntegralClosure K L
          (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom ↥𝒪[K] K L) z) := by
    intro z
    refine Subtype.ext ?_
    rw [hbase]
    have hK : ((baseEquiv K z : ↥𝒪[K]) : K) = algebraMap (integralClosure ↥𝒪[K] K) K z := by
      have h := IsIntegralClosure.algebraMap_equiv ↥𝒪[K] (integralClosure ↥𝒪[K] K) K ↥𝒪[K] z
      exact h
    have hL : ((integerEquivIntegralClosure K L
        (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom ↥𝒪[K] K L) z) :
        ↥𝒪[L]) : L) =
        algebraMap (integralClosure ↥𝒪[K] L) L
          (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom ↥𝒪[K] K L) z) := by
      have h := IsIntegralClosure.algebraMap_equiv ↥𝒪[K] (integralClosure ↥𝒪[K] L) L ↥𝒪[L]
        (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom ↥𝒪[K] K L) z)
      exact h
    rw [hK, hL]
    rfl
  calc Ideal.map (algebraMap ↥𝒪[K] ↥𝒪[L]) 𝓂[K]
      = Ideal.map (algebraMap ↥𝒪[K] ↥𝒪[L])
          (Ideal.map (baseEquiv K : integralClosure ↥𝒪[K] K →+* ↥𝒪[K])
          (IsLocalRing.maximalIdeal (integralClosure ↥𝒪[K] K))) := by
        rw [MapMaximalIdealEqPowCardInertia.map_maximalIdeal_ringEquiv (baseEquiv K)]
  _ = Ideal.map ((algebraMap ↥𝒪[K] ↥𝒪[L]).comp (baseEquiv K : integralClosure ↥𝒪[K] K →+* ↥𝒪[K]))
        (IsLocalRing.maximalIdeal (integralClosure ↥𝒪[K] K)) :=
      Ideal.map_map _ _
  _ = Ideal.map ((integerEquivIntegralClosure K L : integralClosure ↥𝒪[K] L →+* ↥𝒪[L]).comp
        ((AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom ↥𝒪[K] K L)) :
          integralClosure ↥𝒪[K] K →+* integralClosure ↥𝒪[K] L))
        (IsLocalRing.maximalIdeal (integralClosure ↥𝒪[K] K)) := by
      refine map_congr_fn _ _ (funext fun z => ?_) _
      exact hfn z
  _ = Ideal.map (integerEquivIntegralClosure K L : integralClosure ↥𝒪[K] L →+* ↥𝒪[L]) (Ideal.map
        ((AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom ↥𝒪[K] K L)) :
          integralClosure ↥𝒪[K] K →+* integralClosure ↥𝒪[K] L)
        (IsLocalRing.maximalIdeal (integralClosure ↥𝒪[K] K))) := (Ideal.map_map _ _).symm
  _ = Ideal.map (integerEquivIntegralClosure K L : integralClosure ↥𝒪[K] L →+* ↥𝒪[L]) (Ideal.map
        (AlgHom.mapIntegralClosure (IsScalarTower.toAlgHom ↥𝒪[K] K L))
        (IsLocalRing.maximalIdeal (integralClosure ↥𝒪[K] K))) := by
      refine congrArg _ (map_congr_fn _ _ rfl _)
  _ = Ideal.map (integerEquivIntegralClosure K L : integralClosure ↥𝒪[K] L →+* ↥𝒪[L])
        (IsLocalRing.maximalIdeal (integralClosure ↥𝒪[K] L)) := by
      rw [hKL]
  _ = 𝓂[L] := by
      rw [MapMaximalIdealEqPowCardInertia.map_maximalIdeal_ringEquiv
        (integerEquivIntegralClosure K L)]

/- With trivial inertia a base uniformizer stays irreducible upstairs. -/
private theorem irreducible_algebraMap_of_unramified
    (h : lowerRamificationGroup K L 0 = ⊥) {π : ↥𝒪[K]} (hπ : Irreducible π) :
    Irreducible (algebraMap ↥𝒪[K] ↥𝒪[L] π) := by
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer] at hπ ⊢
  rw [← map_maximalIdeal_of_unramified K L h, hπ, Ideal.map_span]
  simp

/-- **The unramified embedding preserves the normalized valuation** — the
`v_𝔓 (x) = e_𝔓 v_p (x)` formula at `e = 1`: a base uniformizer stays a uniformizer, and
units of the integers stay units ([Serre 1979, Chap. I, §4, p.15][Serre1979]). -/
theorem normalizedValuation_algebraMap_of_unramified
    (h : lowerRamificationGroup K L 0 = ⊥) (x : Kˣ) :
    normalizedValuation L (Units.map ((algebraMap K L) : K →* L) x) =
      normalizedValuation K x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[K])
  have hx0 : (x : K) ≠ 0 := Units.ne_zero x
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hπ hx0
  have hinjK : Function.Injective (algebraMap ↥𝒪[K] K) := IsFractionRing.injective ↥𝒪[K] K
  have hneK : ∀ a : ↥𝒪[K], a ≠ 0 → algebraMap ↥𝒪[K] K a ≠ 0 := fun a ha h0 =>
    ha (hinjK (by rwa [map_zero]))
  have hπ0 : algebraMap ↥𝒪[K] K π ≠ 0 := hneK π hπ.ne_zero
  have hu0 : algebraMap ↥𝒪[K] K (u : ↥𝒪[K]) ≠ 0 := hneK _ (Units.ne_zero u)
  have hxeq : x = Units.mk0 (algebraMap ↥𝒪[K] K (u : ↥𝒪[K])) hu0 *
      (Units.mk0 (algebraMap ↥𝒪[K] K π) hπ0) ^ n := by
    ext
    push_cast [hu, Units.smul_def, Algebra.smul_def]
    rfl
  have hinjL : Function.Injective (algebraMap ↥𝒪[L] L) := IsFractionRing.injective ↥𝒪[L] L
  have hneL : ∀ a : ↥𝒪[L], a ≠ 0 → algebraMap ↥𝒪[L] L a ≠ 0 := fun a ha h0 =>
    ha (hinjL (by rwa [map_zero]))
  have hπL := irreducible_algebraMap_of_unramified K L h hπ
  have hπL0 : algebraMap ↥𝒪[L] L (algebraMap ↥𝒪[K] ↥𝒪[L] π) ≠ 0 :=
    hneL _ hπL.ne_zero
  have huL0 : algebraMap ↥𝒪[L] L
      ((Units.map ((algebraMap ↥𝒪[K] ↥𝒪[L]) : ↥𝒪[K] →* ↥𝒪[L]) u : (↥𝒪[L])ˣ) : ↥𝒪[L]) ≠ 0 :=
    hneL _ (Units.ne_zero _)
  have hbase' : ∀ r : ↥𝒪[K], algebraMap K L (algebraMap ↥𝒪[K] K r) =
      algebraMap ↥𝒪[L] L (algebraMap ↥𝒪[K] ↥𝒪[L] r) := by
    intro r
    rw [← IsScalarTower.algebraMap_apply ↥𝒪[K] K L,
      IsScalarTower.algebraMap_apply ↥𝒪[K] ↥𝒪[L] L]
  have hxval : (x : K) = algebraMap ↥𝒪[K] K (u : ↥𝒪[K]) * (algebraMap ↥𝒪[K] K π) ^ n := by
    rw [hu, Units.smul_def, Algebra.smul_def]
  have hmapeq : Units.map ((algebraMap K L) : K →* L) x =
      Units.mk0 (algebraMap ↥𝒪[L] L
        ((Units.map ((algebraMap ↥𝒪[K] ↥𝒪[L]) : ↥𝒪[K] →* ↥𝒪[L]) u : (↥𝒪[L])ˣ) : ↥𝒪[L]))
        huL0 *
      (Units.mk0 (algebraMap ↥𝒪[L] L (algebraMap ↥𝒪[K] ↥𝒪[L] π)) hπL0) ^ n := by
    ext
    change algebraMap K L (x : K) = _
    rw [hxval, map_mul, map_zpow₀, hbase', hbase']
    push_cast
    rfl
  rw [hmapeq, hxeq,
    value_unit_mul_zpow (L := K) π hπ u hu0 hπ0 n,
    value_unit_mul_zpow (L := L) (algebraMap ↥𝒪[K] ↥𝒪[L] π) hπL
      (Units.map ((algebraMap ↥𝒪[K] ↥𝒪[L]) : ↥𝒪[K] →* ↥𝒪[L]) u) huL0 hπL0 n]

/-- **A norm's value is the degree times the value upstairs** — the element form of
`N (𝔓) = p ^ f` at `f = n`: the norm is the full product of conjugates, each of the same
value by `Atlas.Knowledge.normalizedValuation_algEquiv`
([Serre 1979, Chap. I, §5, p.16][Serre1979]). -/
theorem normalizedValuation_norm_of_unramified
    (h : lowerRamificationGroup K L 0 = ⊥) (y : Lˣ) :
    normalizedValuation K (Units.map ((Algebra.norm K) : L →* K) y) =
      (Module.finrank K L : ℤ) * normalizedValuation L y := by
  have hunit : Units.map ((algebraMap K L) : K →* L)
      (Units.map ((Algebra.norm K) : L →* K) y) =
      ∏ σ : L ≃ₐ[K] L, Units.map (σ : L →* L) y := by
    ext
    rw [show ((∏ σ : L ≃ₐ[K] L, Units.map (σ : L →* L) y : Lˣ) : L) =
      ∏ σ : L ≃ₐ[K] L, ((Units.map (σ : L →* L) y : Lˣ) : L) from
        map_prod (Units.coeHom L) _ _]
    change algebraMap K L (Algebra.norm K ((y : Lˣ) : L)) = _
    rw [Algebra.norm_eq_prod_automorphisms]
    rfl
  have hv := congrArg (normalizedValuationHom L) hunit
  rw [map_prod] at hv
  have hterm : ∀ σ : L ≃ₐ[K] L,
      normalizedValuationHom L (Units.map (σ : L →* L) y) =
        Multiplicative.ofAdd (normalizedValuation L y) := by
    intro σ
    calc normalizedValuationHom L (Units.map (σ : L →* L) y)
        = Multiplicative.ofAdd (normalizedValuation L (Units.map (σ : L →* L) y)) := rfl
    _ = Multiplicative.ofAdd (normalizedValuation L y) := by
        rw [normalizedValuation_algEquiv (K := K) (L := L)]
  rw [Finset.prod_congr rfl fun σ _ => hterm σ, Finset.prod_const] at hv
  have hcard : (Finset.univ : Finset (L ≃ₐ[K] L)).card = Module.finrank K L := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact IsGalois.card_aut_eq_finrank K L
  rw [hcard] at hv
  have hfinal := congrArg Multiplicative.toAdd hv
  have hLHS : Multiplicative.toAdd (normalizedValuationHom L
      (Units.map ((algebraMap K L) : K →* L) (Units.map ((Algebra.norm K) : L →* K) y))) =
      normalizedValuation K (Units.map ((Algebra.norm K) : L →* K) y) :=
    normalizedValuation_algebraMap_of_unramified K L h _
  rw [hLHS] at hfinal
  rw [hfinal, _root_.toAdd_pow]
  simp

/-- **The norm subgroup of an unramified extension is the preimage of the degree's
powers**: both it and the preimage have index the degree — the class field axiom on one
side, the reduction to `ZMod n` on the other — and one contains the other
([Serre 1979, Chap. V, §2, Prop. 3 and Cor., p.82][Serre1979]; the source counterpart, in
its own valuation vocabulary, is
[Yamaguchi 2026, `LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean:149`]
[Yamaguchi2026]). -/
theorem unramifiedNormRange (h : lowerRamificationGroup K L 0 = ⊥) :
    (Units.map ((Algebra.norm K) : L →* K)).range =
      Subgroup.comap (normalizedValuationHom K)
        (Subgroup.zpowers (Multiplicative.ofAdd (Module.finrank K L : ℤ))) := by
  have hn0 : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  obtain ⟨σ, hσ⟩ := exists_isArithmeticFrobenius K L h
  have hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ := fun τ =>
    (zpowers_of_isArithmeticFrobenius K L h hσ) ▸ Subgroup.mem_top τ
  -- the containment: a norm's value is a multiple of the degree
  have hle : (Units.map ((Algebra.norm K) : L →* K)).range ≤
      Subgroup.comap (normalizedValuationHom K)
        (Subgroup.zpowers (Multiplicative.ofAdd (Module.finrank K L : ℤ))) := by
    rintro x ⟨y, rfl⟩
    rw [Subgroup.mem_comap, Subgroup.mem_zpowers_iff]
    refine ⟨normalizedValuation L y, ?_⟩
    calc (Multiplicative.ofAdd (Module.finrank K L : ℤ)) ^ normalizedValuation L y
        = Multiplicative.ofAdd (normalizedValuation L y • (Module.finrank K L : ℤ)) := by
          rw [← ofAdd_zsmul]
    _ = Multiplicative.ofAdd ((Module.finrank K L : ℤ) * normalizedValuation L y) := by
          rw [smul_eq_mul, mul_comm]
    _ = normalizedValuationHom K (Units.map ((Algebra.norm K) : L →* K) y) := by
          rw [← normalizedValuation_norm_of_unramified K L h y]
          rfl
  -- the reduction to `ZMod n` computes both indices
  have hψker : ((AddMonoidHom.toMultiplicative
      (Int.castAddHom (ZMod (Module.finrank K L)))).comp
        (normalizedValuationHom K)).ker =
      Subgroup.comap (normalizedValuationHom K)
        (Subgroup.zpowers (Multiplicative.ofAdd (Module.finrank K L : ℤ))) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, Subgroup.mem_zpowers_iff]
    constructor
    · intro hx
      have h0 : ((Multiplicative.toAdd (normalizedValuationHom K x) : ℤ) :
          ZMod (Module.finrank K L)) = 0 := by
        have := congrArg Multiplicative.toAdd hx
        simpa using this
      obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
      refine ⟨c, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [← ofAdd_zsmul]
      simp only [toAdd_ofAdd]
      rw [smul_eq_mul, mul_comm]
      exact hc.symm
    · rintro ⟨c, hc⟩
      apply Multiplicative.toAdd.injective
      have hdvd : ((Module.finrank K L : ℤ)) ∣
          Multiplicative.toAdd (normalizedValuationHom K x) := by
        refine ⟨c, ?_⟩
        have := congrArg Multiplicative.toAdd hc
        rw [← ofAdd_zsmul] at this
        simpa [mul_comm] using this.symm
      simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  have hψsurj : Function.Surjective ((AddMonoidHom.toMultiplicative
      (Int.castAddHom (ZMod (Module.finrank K L)))).comp (normalizedValuationHom K)) := by
    intro z
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (Multiplicative.toAdd z)
    obtain ⟨x, hx⟩ := normalizedValuation_surjective K a
    refine ⟨x, ?_⟩
    apply Multiplicative.toAdd.injective
    calc Multiplicative.toAdd ((AddMonoidHom.toMultiplicative
        (Int.castAddHom (ZMod (Module.finrank K L)))).comp (normalizedValuationHom K) x)
        = ((normalizedValuation K x : ℤ) : ZMod (Module.finrank K L)) := rfl
    _ = ((a : ℤ) : ZMod (Module.finrank K L)) := by rw [hx]
    _ = Multiplicative.toAdd z := ha
  have hcardC : Nat.card (Kˣ ⧸ Subgroup.comap (normalizedValuationHom K)
      (Subgroup.zpowers (Multiplicative.ofAdd (Module.finrank K L : ℤ)))) =
      Module.finrank K L := by
    rw [← hψker]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hψsurj).toEquiv]
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have hcardN := normIndexCyclic (K := K) (L := L) σ hgen
  -- equal finite indices with a containment force equality
  have hCindex : (Subgroup.comap (normalizedValuationHom K)
      (Subgroup.zpowers (Multiplicative.ofAdd (Module.finrank K L : ℤ)))).index =
      Module.finrank K L := hcardC
  have hNindex : (Units.map ((Algebra.norm K) : L →* K)).range.index =
      Module.finrank K L := hcardN
  have hrel := Subgroup.relIndex_mul_index hle
  rw [hCindex, hNindex] at hrel
  have hrel1 : (Units.map ((Algebra.norm K) : L →* K)).range.relIndex
      (Subgroup.comap (normalizedValuationHom K)
        (Subgroup.zpowers (Multiplicative.ofAdd (Module.finrank K L : ℤ)))) = 1 :=
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn0) (by rw [hrel, one_mul])
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hrel1)

end Atlas.Knowledge
