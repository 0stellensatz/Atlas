import Mathlib
import Atlas.Knowledge.IntegralClosureDVR
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LowerRamificationGroup

/-!
# arithmetic Frobenius

The arithmetic Frobenius of an extension of a mixed-characteristic local field, as a
predicate: `σ : L ≃ₐ[K] L` is an arithmetic Frobenius when it satisfies the Frobenius
substitution congruence `σ x ≡ x ^ q` on the integral closure of `𝒪[K]` in `L` modulo its
Jacobson radical, `q` the cardinality of the residue field of `K`. This is the literature's
definition read literally — no residue-action isomorphism is constructed to state it — and it
is the element the unramified normalization of the Artin map
(`Atlas.Knowledge.IsFrobeniusNormalized`) points at. Over an unramified extension the
predicate pins a unique element, which generates the Galois group; existence, uniqueness,
the order, and the generation are all proved here.

## Main definitions

* `IsArithmeticFrobenius` — the Frobenius substitution congruence.

## Main statements

* `isArithmeticFrobenius_unique` / `exists_isArithmeticFrobenius` — over an unramified
  extension (trivial inertia, `G_0 = ⊥`) there is exactly one arithmetic Frobenius; both
  proved, and only uniqueness uses the unramifiedness — existence carries the hypothesis in
  its statement alone.
* `orderOf_of_isArithmeticFrobenius` / `zpowers_of_isArithmeticFrobenius` — its order is the
  degree and it generates; both proved.

## Implementation notes

The carrier is `integralClosure 𝒪[K] L` with congruence modulo `Ideal.jacobson ⊥`, the
layer's uniform encoding (`Atlas.Knowledge.LowerRamificationGroup`), and unramifiedness is
rendered Atlas-natively as `lowerRamificationGroup K L 0 = ⊥`; the identification with the
ramification-index-one class of the literature is `e = |G_0|`,
`Atlas.Knowledge.MapMaximalIdealEqPowCardInertia`. The predicate is stated for any algebraic
extension and owns its junk regions: without unramifiedness the congruence pins σ only up to
inertia — uniqueness genuinely needs `G_0 = ⊥` — and the exponent is `Nat.card 𝓀[K]`, the
*base* residue cardinality, so nothing here collapses when the residue extension is proper.
The source repository builds its Frobenius through a residue-action equivalence instead
(`LocalFieldTheory/NonarchimedeanLocalField/UnramifiedFrobenius.lean:119`) and proves that
it satisfies the equivalent residue-field form of the congruence (`:167`). The proofs here
instead go through Mathlib's Frobenius theory at a single prime: the integral closure is
local (`Atlas.Knowledge.IntegralClosureDVR`), so the Jacobson radical is its maximal ideal
`Q` and the layer's congruence is the mod-`Q` congruence of `IsArithFrobAt` — existence is
`IsArithFrobAt.exists_of_isInvariant`, and the order is computed through
`Ideal.Quotient.stabilizerHom`, bijective onto the residue Galois group once `G_0 = ⊥`
kills its inertia kernel. Uniqueness never leaves the layer: the quotient of two Frobenii
satisfies `s x ≡ x`, which is membership in the trivial `G_0`. The two-names dictionary
`natCard_quotient_under` — the exponent conversion of that single-prime identification — is
public since the #104 Brick-C promotion, whose root-of-unity wrapper
`Atlas.Knowledge.IsArithmeticFrobenius.apply_of_pow_eq_one` consumes the same conversion and
could not host it without an import cycle; its companion `under_maximalIdeal` stays private
with its in-file consumers.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

open scoped Pointwise

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  (L : Type*) [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]

/-- The **arithmetic Frobenius** predicate: `σ` satisfies the Frobenius substitution
congruence `σ x ≡ x ^ q` modulo the Jacobson radical on the integral closure of `𝒪[K]` in
`L`, where `q = Nat.card 𝓀[K]`
([Milne 2020, Chap. I, §1, p.20][MilneCFT];
[Yamaguchi 2026, `LocalFieldTheory/NonarchimedeanLocalField/UnramifiedFrobenius.lean:167`]
[Yamaguchi2026]). -/
def IsArithmeticFrobenius (σ : L ≃ₐ[K] L) : Prop :=
  ∀ x : integralClosure 𝒪[K] L,
    galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ x - x ^ Nat.card 𝓀[K] ∈
      Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L))

/-- Over an unramified extension the arithmetic Frobenius is unique: two automorphisms
satisfying the substitution congruence agree once the inertia group is trivial — their
quotient moves every integral element within the radical, which is membership in the trivial
`G_0` ([Milne 2020, Chap. I, §1, p.20][MilneCFT]). -/
theorem isArithmeticFrobenius_unique [FiniteDimensional K L]
    (h : lowerRamificationGroup K L 0 = ⊥) {σ τ : L ≃ₐ[K] L}
    (hσ : IsArithmeticFrobenius K L σ) (hτ : IsArithmeticFrobenius K L τ) : σ = τ := by
  have hmem : σ * τ⁻¹ ∈ lowerRamificationGroup K L 0 := by
    rw [mem_lowerRamificationGroup_iff]
    intro x
    rw [show ((0 : ℤ) + 1).toNat = 1 by norm_num, pow_one]
    set y := galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) τ⁻¹ x with hy
    have hcomp : galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) (σ * τ⁻¹) x =
        galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ y := by
      rw [hy, map_mul]; rfl
    have hτy : galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) τ y = x := by
      rw [hy, map_inv, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    -- `σ y ≡ y ^ q ≡ τ y = x`, both congruences modulo the radical
    have h2 := hτ y
    rw [hτy] at h2
    have hsub : galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ y - x =
        (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ y - y ^ Nat.card 𝓀[K]) -
          (x - y ^ Nat.card 𝓀[K]) := by ring
    rw [hcomp, hsub]
    exact sub_mem (hσ y) h2
  rw [h, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

/- The maximal ideal of the local integral closure lies over the maximal ideal of the base:
its trace on `𝒪[K]` is maximal by integrality, and the base is local. -/
private theorem under_maximalIdeal [FiniteDimensional K L] :
    (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L)).under 𝒪[K] =
      IsLocalRing.maximalIdeal 𝒪[K] :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
      (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L)))

/-- The residue field of the base under its two names: the quotient by the trace of the
closure's maximal ideal is `𝓀[K]` — the exponent conversion between the layer's congruence
and Mathlib's `AlgHom.IsArithFrobAt`. -/
theorem natCard_quotient_under [FiniteDimensional K L] :
    Nat.card (𝒪[K] ⧸ (IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L)).under 𝒪[K]) =
      Nat.card 𝓀[K] := by
  rw [under_maximalIdeal K L]
  rfl

/- The residue field of the integral closure is finite: the closure is module-finite over
`𝒪[K]`, so its residue field is module-finite over the finite `𝓀[K]`. -/
private theorem finite_quotient_maximalIdeal [FiniteDimensional K L] :
    Finite ((integralClosure 𝒪[K] L) ⧸
      IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L)) := by
  haveI : IsNoetherian 𝒪[K] (integralClosure 𝒪[K] L) :=
    IsIntegralClosure.isNoetherian 𝒪[K] K L (integralClosure 𝒪[K] L)
  haveI : Module.Finite 𝒪[K] (integralClosure 𝒪[K] L) := ⟨IsNoetherian.noetherian ⊤⟩
  set Q := IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L)
  haveI : Q.LiesOver (Q.under 𝒪[K]) := ⟨rfl⟩
  haveI : Module.Finite (𝒪[K] ⧸ Q.under 𝒪[K]) ((integralClosure 𝒪[K] L) ⧸ Q) :=
    Module.Finite.of_restrictScalars_finite 𝒪[K] _ _
  haveI : Finite (𝒪[K] ⧸ Q.under 𝒪[K]) :=
    Finite.of_equiv 𝓀[K] (Ideal.quotEquivOfEq (under_maximalIdeal K L)).symm.toEquiv
  exact Module.finite_of_finite (𝒪[K] ⧸ Q.under 𝒪[K])

set_option linter.unusedVariables false in
/-- Over a finite Galois unramified extension an arithmetic Frobenius exists: Mathlib's
Frobenius element at the maximal ideal of the integral closure, whose single-prime congruence
is the substitution congruence because the closure is local. Existence needs no
unramifiedness, and the hypothesis is carried by the statement, not the proof
([Milne 2020, Chap. I, §1, p.20][MilneCFT]). -/
theorem exists_isArithmeticFrobenius [FiniteDimensional K L] [IsGalois K L]
    (h : lowerRamificationGroup K L 0 = ⊥) :
    ∃ σ : L ≃ₐ[K] L, IsArithmeticFrobenius K L σ := by
  classical
  haveI : IsFractionRing (integralClosure 𝒪[K] L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  letI := IsIntegralClosure.MulSemiringAction 𝒪[K] K L (integralClosure 𝒪[K] L)
  haveI : SMulCommClass (L ≃ₐ[K] L) 𝒪[K] (integralClosure 𝒪[K] L) :=
    ⟨fun g r x => map_smul (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) g) r x⟩
  haveI := Algebra.isInvariant_of_isGalois 𝒪[K] K L (integralClosure 𝒪[K] L)
  set Q := IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L) with hQdef
  haveI : Finite ((integralClosure 𝒪[K] L) ⧸ Q) := finite_quotient_maximalIdeal K L
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant 𝒪[K] (L ≃ₐ[K] L) Q
  refine ⟨σ, fun x => ?_⟩
  rw [integralClosure_jacobson_bot_eq_maximalIdeal K L]
  have hx := hσ x
  rwa [natCard_quotient_under K L] at hx

set_option maxHeartbeats 800000 in
-- The residue-side instance chain (quotient field, algebra, module, Galois) is synthesized
-- through the `LiesOver` tower and exceeds the default limits.
set_option synthInstance.maxHeartbeats 80000 in
/-- The arithmetic Frobenius of a finite Galois unramified extension has order the degree —
the Galois group is cyclic of order `[L : K]`, carried by the residue extension: with the
inertia group trivial the residue map on the Galois group is bijective, and the `q`-power
map on the finite residue field has order exactly the residue degree
([Milne 2020, Chap. I, §1, p.20][MilneCFT]). -/
theorem orderOf_of_isArithmeticFrobenius [FiniteDimensional K L] [IsGalois K L]
    (h : lowerRamificationGroup K L 0 = ⊥) {σ : L ≃ₐ[K] L}
    (hσ : IsArithmeticFrobenius K L σ) : orderOf σ = Module.finrank K L := by
  classical
  haveI : IsFractionRing (integralClosure 𝒪[K] L) L :=
    integralClosure.isFractionRing_of_finite_extension K L
  letI := IsIntegralClosure.MulSemiringAction 𝒪[K] K L (integralClosure 𝒪[K] L)
  haveI : SMulCommClass (L ≃ₐ[K] L) 𝒪[K] (integralClosure 𝒪[K] L) :=
    ⟨fun g r x => map_smul (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) g) r x⟩
  haveI := Algebra.isInvariant_of_isGalois 𝒪[K] K L (integralClosure 𝒪[K] L)
  set Q := IsLocalRing.maximalIdeal (integralClosure 𝒪[K] L) with hQdef
  set P := Q.under 𝒪[K] with hPdef
  haveI : Q.LiesOver P := ⟨rfl⟩
  letI : Module (𝒪[K] ⧸ P) ((integralClosure 𝒪[K] L) ⧸ Q) := Algebra.toModule
  haveI : P.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  haveI hfin : Finite ((integralClosure 𝒪[K] L) ⧸ Q) := finite_quotient_maximalIdeal K L
  haveI : Finite (𝒪[K] ⧸ P) :=
    Finite.of_equiv 𝓀[K] (Ideal.quotEquivOfEq (under_maximalIdeal K L)).symm.toEquiv
  letI : Field (𝒪[K] ⧸ P) := Ideal.Quotient.field P
  letI : Field ((integralClosure 𝒪[K] L) ⧸ Q) := Ideal.Quotient.field Q
  -- the whole Galois group stabilizes the unique maximal ideal
  have hstab : ∀ g : L ≃ₐ[K] L, g ∈ MulAction.stabilizer (L ≃ₐ[K] L) Q := by
    intro g
    rw [MulAction.mem_stabilizer_iff]
    have : (g • Q).IsMaximal := by
      rw [Ideal.pointwise_smul_eq_comap]
      exact Ideal.comap_isMaximal_of_surjective _
        (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) g⁻¹).surjective
    exact (IsLocalRing.eq_maximalIdeal this).trans hQdef.symm
  -- the residue map on the Galois group, injective by unramifiedness, surjective always
  set ρ := Ideal.Quotient.stabilizerHom Q P (L ≃ₐ[K] L) with hρdef
  have hinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, Ideal.Quotient.ker_stabilizerHom]
    rw [Subgroup.eq_bot_iff_forall]
    intro s hs
    have hs1 : (s : L ≃ₐ[K] L) ∈ lowerRamificationGroup K L 0 := by
      rw [mem_lowerRamificationGroup_iff]
      intro x
      rw [show ((0 : ℤ) + 1).toNat = 1 by norm_num, pow_one,
        integralClosure_jacobson_bot_eq_maximalIdeal K L]
      exact hs x
    rw [h, Subgroup.mem_bot] at hs1
    exact Subtype.ext hs1
  have hsurj : Function.Surjective ρ :=
    Ideal.Quotient.stabilizerHom_surjective (L ≃ₐ[K] L) P Q
  -- transport the order of `σ` to the residue side
  set σ' : MulAction.stabilizer (L ≃ₐ[K] L) Q := ⟨σ, hstab σ⟩ with hσ'def
  have horder : orderOf σ = orderOf (ρ σ') := by
    rw [orderOf_injective ρ hinj σ']
    exact orderOf_injective (MulAction.stabilizer (L ≃ₐ[K] L) Q).subtype
      (MulAction.stabilizer (L ≃ₐ[K] L) Q).subtype_injective σ'
  -- the residue image of `σ` is the `q`-power map
  have hpow : ∀ y : (integralClosure 𝒪[K] L) ⧸ Q, ρ σ' y = y ^ Nat.card 𝓀[K] := by
    intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    have hx := hσ x
    rw [integralClosure_jacobson_bot_eq_maximalIdeal K L, ← Ideal.Quotient.eq] at hx
    calc ρ σ' (Ideal.Quotient.mk Q x)
      = Ideal.Quotient.mk Q (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ x) := rfl
    _ = Ideal.Quotient.mk Q (x ^ Nat.card 𝓀[K]) := hx
    _ = Ideal.Quotient.mk Q x ^ Nat.card 𝓀[K] := map_pow _ x _
  -- the `q`-power map on the residue field has order the residue degree
  have hiter : ∀ (j : ℕ) (y : (integralClosure 𝒪[K] L) ⧸ Q),
      (ρ σ' ^ j) y = y ^ Nat.card 𝓀[K] ^ j := by
    intro j
    induction j with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, AlgEquiv.mul_apply, hpow y, ih, ← pow_mul, ← pow_succ']
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  set f := Module.finrank (𝒪[K] ⧸ P) ((integralClosure 𝒪[K] L) ⧸ Q) with hfdef
  haveI : Algebra.IsIntegral 𝒪[K] (integralClosure 𝒪[K] L) :=
    IsIntegralClosure.isIntegral_algebra 𝒪[K] L
  haveI : Algebra.IsIntegral (𝒪[K] ⧸ P) ((integralClosure 𝒪[K] L) ⧸ Q) :=
    Algebra.IsIntegral.quotient
  haveI : Algebra.IsSeparable (𝒪[K] ⧸ P) ((integralClosure 𝒪[K] L) ⧸ Q) := by
    refine ⟨fun y => PerfectField.separable_of_irreducible (minpoly.irreducible ?_)⟩
    exact Algebra.IsIntegral.isIntegral y
  haveI : Normal (𝒪[K] ⧸ P) ((integralClosure 𝒪[K] L) ⧸ Q) :=
    Ideal.Quotient.normal (L ≃ₐ[K] L) P Q
  haveI : Module.Finite (𝒪[K] ⧸ P) ((integralClosure 𝒪[K] L) ⧸ Q) :=
    Ideal.Quotient.finite_of_isInvariant (L ≃ₐ[K] L) P Q
  haveI : IsGalois (𝒪[K] ⧸ P) ((integralClosure 𝒪[K] L) ⧸ Q) := ⟨⟩
  have hcardF : Nat.card ((integralClosure 𝒪[K] L) ⧸ Q) = Nat.card 𝓀[K] ^ f := by
    rw [Module.natCard_eq_pow_finrank (K := 𝒪[K] ⧸ P), natCard_quotient_under K L, hfdef]
  -- order of the `q`-power map is exactly `f`
  have hordf : orderOf (ρ σ') = f := by
    have hf0 : 0 < f := Module.finrank_pos
    have hpowf : ρ σ' ^ f = 1 := by
      ext y
      cases nonempty_fintype ((integralClosure 𝒪[K] L) ⧸ Q)
      rw [hiter f y, AlgEquiv.one_apply, ← hcardF, Nat.card_eq_fintype_card,
        FiniteField.pow_card]
    have hdvd : orderOf (ρ σ') ∣ f := orderOf_dvd_of_pow_eq_one hpowf
    have hle : f ≤ orderOf (ρ σ') := by
      set j := orderOf (ρ σ') with hjdef
      have hj0 : 0 < j :=
        (isOfFinOrder_iff_pow_eq_one.mpr ⟨f, hf0, hpowf⟩).orderOf_pos
      obtain ⟨ξ, hξ⟩ := IsCyclic.exists_ofOrder_eq_natCard
        (α := ((integralClosure 𝒪[K] L) ⧸ Q)ˣ)
      have hfix : (ξ : (integralClosure 𝒪[K] L) ⧸ Q) ^ Nat.card 𝓀[K] ^ j = ξ := by
        rw [← hiter j ξ, hjdef, pow_orderOf_eq_one, AlgEquiv.one_apply]
      have hξpow : ξ ^ (Nat.card 𝓀[K] ^ j - 1) = 1 := by
        have h1 : ξ ^ Nat.card 𝓀[K] ^ j = ξ :=
          Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hfix)
        have hsplit : Nat.card 𝓀[K] ^ j = (Nat.card 𝓀[K] ^ j - 1) + 1 := by
          have : 1 ≤ Nat.card 𝓀[K] ^ j := Nat.one_le_pow _ _ (by omega)
          omega
        have h2 : ξ ^ (Nat.card 𝓀[K] ^ j - 1) * ξ = 1 * ξ := by
          rw [one_mul, ← pow_succ, ← hsplit, h1]
        exact mul_right_cancel h2
      have hdvd2 : Nat.card ((integralClosure 𝒪[K] L) ⧸ Q)ˣ ∣ Nat.card 𝓀[K] ^ j - 1 := by
        rw [← hξ]
        exact orderOf_dvd_of_pow_eq_one hξpow
      have hcards : Nat.card ((integralClosure 𝒪[K] L) ⧸ Q)ˣ =
          Nat.card ((integralClosure 𝒪[K] L) ⧸ Q) - 1 := by
        cases nonempty_fintype ((integralClosure 𝒪[K] L) ⧸ Q)
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_units]
      have hle2 : Nat.card 𝓀[K] ^ f - 1 ≤ Nat.card 𝓀[K] ^ j - 1 := by
        refine Nat.le_of_dvd ?_ ?_
        · have : 1 < Nat.card 𝓀[K] ^ j := Nat.one_lt_pow hj0.ne' hq1
          omega
        · rw [← hcardF, ← hcards]
          exact hdvd2
      have hlepow : Nat.card 𝓀[K] ^ f ≤ Nat.card 𝓀[K] ^ j := by
        have hqj : 1 ≤ Nat.card 𝓀[K] ^ j := Nat.one_le_pow _ _ (by omega)
        exact (tsub_le_tsub_iff_right hqj).mp hle2
      exact (Nat.pow_le_pow_iff_right hq1).mp hlepow
    exact Nat.le_antisymm (Nat.le_of_dvd (by omega) hdvd) hle
  -- residue degree equals the global degree: the residue map is bijective
  have hcardG : Nat.card (L ≃ₐ[K] L) =
      Nat.card (((integralClosure 𝒪[K] L) ⧸ Q) ≃ₐ[𝒪[K] ⧸ P] ((integralClosure 𝒪[K] L) ⧸ Q)) := by
    have hstabtop : MulAction.stabilizer (L ≃ₐ[K] L) Q = ⊤ := by
      rw [Subgroup.eq_top_iff']
      exact hstab
    rw [← Nat.card_congr (Equiv.ofBijective ρ ⟨hinj, hsurj⟩),
      ← Nat.card_congr (Subgroup.topEquiv.toEquiv), ← hstabtop]
  rw [horder, hordf, hfdef, ← IsGalois.card_aut_eq_finrank, ← hcardG,
    IsGalois.card_aut_eq_finrank]

/-- The arithmetic Frobenius of a finite Galois unramified extension generates the Galois
group: its cyclic subgroup has cardinality its order, which is the degree, which is the
cardinality of the whole group ([Milne 2020, Chap. I, §1, p.20][MilneCFT];
[Yamaguchi 2026, `LocalFieldTheory/NonarchimedeanLocalField/UnramifiedFrobenius.lean:377`]
[Yamaguchi2026]). -/
theorem zpowers_of_isArithmeticFrobenius [FiniteDimensional K L] [IsGalois K L]
    (h : lowerRamificationGroup K L 0 = ⊥) {σ : L ≃ₐ[K] L}
    (hσ : IsArithmeticFrobenius K L σ) : Subgroup.zpowers σ = ⊤ := by
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [Nat.card_zpowers, orderOf_of_isArithmeticFrobenius K L h hσ]
  exact (IsGalois.card_aut_eq_finrank K L).symm

end Atlas.Knowledge
