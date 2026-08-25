import Mathlib
import Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField
import Atlas.Knowledge.IntegerHigherUnitCount
import Atlas.Knowledge.IntegerHigherUnitGroup
import Atlas.Knowledge.IntegerIsIntegralClosure
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LubinTateModule
import Atlas.Knowledge.NormalizedValuationAlgEquiv
import Atlas.Knowledge.StandardLubinTateLevelField
import Atlas.Knowledge.StandardLubinTateTorsion

/-!
# standard Lubin–Tate Galois description

The Galois structure of the level tower over a mixed-characteristic local field, proved:
the level-`n + 1` field is abelian over `K`, with Galois group the finite unit-parameter
group `𝒪ˣ/U^{(n+1)}` — Milne's `(A/𝔪^{n+1})ˣ ≅ Gal(K_{π,n+1}/K)`, read through
`𝒪ˣ/(1 + 𝔪^{n+1}) ≅ (A/𝔪^{n+1})ˣ`. The engine is the unit character on the generator
orbit: a unit `u` moves the chosen level generator to `[u] λ` through the evaluated
formal module, the power-basis lift makes that an automorphism, the module's
equivariance makes the assignment a homomorphism whose kernel is exactly the higher
unit group, and the count of `Atlas.Knowledge.integerHigherUnitCount` against the level
degree squeezes the descended injection into an isomorphism — the same count that
proves the extension Galois, through the automorphism count.

## Main definitions

* `levelGeneratorInteger` — the level generator as an integer of the level field, the
  witness instantiating the abstract-carrier torsion and splitting statements.

## Main statements

* `nonempty_standardLubinTateGaloisDescription` — `𝒪ˣ/U^{(n+1)} ≃* Gal(Lₙ/K)`; proved.
* `standardLubinTateLevelField_isAbelianGalois` — proved.
* `standardLubinTateLevelField_isGalois` — the plain Galois weakening; proved.
* `aeval_levelGeneratorInteger` — the level generator is an integral primitive root;
  proved.

## Implementation notes

**Deliberate weakening, kept:** the source's description is *data* — the specific action
sending the unit parameter `u` to the automorphism moving the chosen torsion point by
`[u⁻¹]` (`LubinTate/FiniteLevel/LevelAbelian.lean:53`; the twist is Milne's
`φ_π(a)(λ) = [u⁻¹]_f(λ)` on p.40, two pages past the bare isomorphism). Atlas proves
abstract isomorphy and the abelianness — the character constructed inside the proof
sends `u` to the untwisted `[u]`-action — and a refinement that pins the action would
replace this claim rather than extend it. The local-field structure on the level field
is not data either: each proof obtains it from
`Atlas.Knowledge.exists_extension_isMixedCharLocalField`, which is why the torsion
theory of `Atlas.Knowledge.StandardLubinTateTorsion` is stated over an abstract carrier
extension. The abelianness stays a plain theorem rather than an `instance`, keeping the
recorded statement unchanged now that its proof has landed. One instance seam is
handled by hand: the integer scalar tower `𝒪[K] → 𝒪[L] → L` is supplied as
`Valuation.HasExtension.instIsScalarTowerInteger` at the two valuations, where instance
search at the level field runs into the ambient separable closure and fails.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

section Generator

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable {π : ↥𝒪[K]} (hπ : Irreducible π) (n : ℕ)

-- the carrier instances on the level field, hypothesized; the discharge obtains them
-- from `exists_extension_isMixedCharLocalField`
variable [ValuativeRel ↥(standardLubinTateLevelField K hπ n)]
  [TopologicalSpace ↥(standardLubinTateLevelField K hπ n)]
  [ValuativeExtension K ↥(standardLubinTateLevelField K hπ n)]
  [IsMixedCharLocalField ↥(standardLubinTateLevelField K hπ n)]

omit [ValuativeRel ↥(standardLubinTateLevelField K hπ n)]
  [TopologicalSpace ↥(standardLubinTateLevelField K hπ n)]
  [ValuativeExtension K ↥(standardLubinTateLevelField K hπ n)]
  [IsMixedCharLocalField ↥(standardLubinTateLevelField K hπ n)] in
/-- The level generator satisfies the integral primitive polynomial in the level field. -/
private theorem aeval_generator_field :
    Polynomial.aeval (standardLubinTateLevelGenerator K hπ n :
        standardLubinTateLevelField K hπ n)
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0 := by
  have hroot := chosenStandardLubinTatePrimitiveRoot_isRoot K hπ n
  rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def] at hroot
  have hfield : Polynomial.aeval (standardLubinTateLevelGenerator K hπ n :
      standardLubinTateLevelField K hπ n)
      (standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n) = 0 := by
    have hinj : Function.Injective (standardLubinTateLevelField K hπ n).val :=
      (standardLubinTateLevelField K hπ n).val.toRingHom.injective
    apply hinj
    rw [map_zero, ← Polynomial.aeval_algHom_apply]
    exact hroot
  calc Polynomial.aeval (standardLubinTateLevelGenerator K hπ n :
        standardLubinTateLevelField K hπ n)
        (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n)
      = Polynomial.aeval (standardLubinTateLevelGenerator K hπ n :
          standardLubinTateLevelField K hπ n)
        ((standardLubinTatePrimitivePolynomial ↥𝒪[K] π n).map (algebraMap ↥𝒪[K] K)) :=
        (Polynomial.aeval_map_algebraMap _ _ _).symm
    _ = 0 := hfield

omit [TopologicalSpace ↥(standardLubinTateLevelField K hπ n)]
  [IsMixedCharLocalField ↥(standardLubinTateLevelField K hπ n)] in
/-- The level generator is an integer of the level field. -/
private theorem generator_mem_integer :
    (standardLubinTateLevelGenerator K hπ n :
      standardLubinTateLevelField K hπ n) ∈ 𝒪[↥(standardLubinTateLevelField K hπ n)] := by
  rw [mem_integer_iff_isIntegral K]
  exact ⟨standardLubinTatePrimitivePolynomial ↥𝒪[K] π n,
    standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n,
    by rw [← Polynomial.aeval_def]; exact aeval_generator_field K hπ n⟩

/-- The **level generator as an integer of the level field** — the witness that
instantiates the abstract-carrier torsion and splitting statements at the level tower.
Integrality is forced by the monic integral primitive polynomial; the generator itself,
`Atlas.Knowledge.standardLubinTateLevelGenerator`, carries the source pinpoint. -/
noncomputable def levelGeneratorInteger :
    ↥𝒪[↥(standardLubinTateLevelField K hπ n)] :=
  ⟨standardLubinTateLevelGenerator K hπ n, generator_mem_integer K hπ n⟩

omit [TopologicalSpace ↥(standardLubinTateLevelField K hπ n)]
  [IsMixedCharLocalField ↥(standardLubinTateLevelField K hπ n)] in
/-- **The integral primitive-root identity at integer level**: the level generator,
read as an integer, is a root of the integral primitive polynomial — the hypothesis
shape the abstract-carrier torsion and splitting statements consume, e.g.
`Atlas.Knowledge.standardLubinTateSplitting`. -/
theorem aeval_levelGeneratorInteger :
    Polynomial.aeval (levelGeneratorInteger K hπ n)
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n) = 0 := by
  letI : IsScalarTower ↥𝒪[K] ↥𝒪[↥(standardLubinTateLevelField K hπ n)]
      ↥(standardLubinTateLevelField K hπ n) :=
    Valuation.HasExtension.instIsScalarTowerInteger
      (vR := valuation K) (vA := valuation ↥(standardLubinTateLevelField K hπ n))
  apply Subtype.ext
  change (IsScalarTower.toAlgHom ↥𝒪[K] ↥𝒪[↥(standardLubinTateLevelField K hπ n)]
      ↥(standardLubinTateLevelField K hπ n))
    ((Polynomial.aeval (levelGeneratorInteger K hπ n))
      (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n)) =
    ((0 : ↥𝒪[↥(standardLubinTateLevelField K hπ n)]) :
      ↥(standardLubinTateLevelField K hπ n))
  rw [← Polynomial.aeval_algHom_apply, ZeroMemClass.coe_zero]
  exact aeval_generator_field K hπ n

/-- The level generator lies in the maximal ideal of the level integers. -/
private theorem levelGeneratorInteger_mem_maximalIdeal :
    levelGeneratorInteger K hπ n ∈ 𝓂[↥(standardLubinTateLevelField K hπ n)] :=
  mem_maximalIdeal_of_aeval_primitive K _ hπ (aeval_levelGeneratorInteger K hπ n)

/-- The power basis of the level field at the chosen root. -/
private noncomputable def levelPowerBasis :
    PowerBasis K ↥(standardLubinTateLevelField K hπ n) :=
  IntermediateField.adjoin.powerBasis
    (chosenStandardLubinTatePrimitiveRoot_isIntegral K hπ n)

omit [ValuativeRel ↥(standardLubinTateLevelField K hπ n)]
  [TopologicalSpace ↥(standardLubinTateLevelField K hπ n)]
  [ValuativeExtension K ↥(standardLubinTateLevelField K hπ n)]
  [IsMixedCharLocalField ↥(standardLubinTateLevelField K hπ n)] in
/-- The minimal polynomial of the basis generator is the primitive polynomial. -/
private theorem minpoly_levelPowerBasis_gen :
    minpoly K (levelPowerBasis K hπ n).gen =
      standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n := by
  change minpoly K (IntermediateField.AdjoinSimple.gen K
      (chosenStandardLubinTatePrimitiveRoot K hπ n)) = _
  rw [IntermediateField.minpoly_gen,
    ← standardLubinTatePrimitivePolynomialOverField_eq_minpoly K hπ n]

/-- The orbit point of a unit, as a root of the generator's minimal polynomial. -/
private theorem aeval_orbit (u : 𝒪[K]ˣ) :
    Polynomial.aeval
      ((lubinTateSMul K ↥(standardLubinTateLevelField K hπ n) hπ
          (standardLubinTateSeries hπ) (↑u) (levelGeneratorInteger K hπ n) :
        ↥𝒪[↥(standardLubinTateLevelField K hπ n)]) :
        ↥(standardLubinTateLevelField K hπ n))
      (minpoly K (levelPowerBasis K hπ n).gen) = 0 := by
  rw [minpoly_levelPowerBasis_gen]
  letI : IsScalarTower ↥𝒪[K] ↥𝒪[↥(standardLubinTateLevelField K hπ n)]
      ↥(standardLubinTateLevelField K hπ n) :=
    Valuation.HasExtension.instIsScalarTowerInteger
      (vR := valuation K) (vA := valuation ↥(standardLubinTateLevelField K hπ n))
  have hint := standardLubinTateSMul_isRoot K
    ↥(standardLubinTateLevelField K hπ n) hπ
    (levelGeneratorInteger_mem_maximalIdeal K hπ n) (aeval_levelGeneratorInteger K hπ n) u
  have hpush := Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ↥𝒪[K] ↥𝒪[↥(standardLubinTateLevelField K hπ n)]
      ↥(standardLubinTateLevelField K hπ n))
    (lubinTateSMul K ↥(standardLubinTateLevelField K hπ n) hπ
      (standardLubinTateSeries hπ) (↑u) (levelGeneratorInteger K hπ n))
    (standardLubinTatePrimitivePolynomial ↥𝒪[K] π n)
  rw [hint, map_zero] at hpush
  rw [standardLubinTatePrimitivePolynomialOverField, Polynomial.aeval_map_algebraMap]
  exact hpush

/-- The unit-orbit algebra endomorphism: the generator goes to its orbit point. -/
private noncomputable def orbitHom (u : 𝒪[K]ˣ) :
    ↥(standardLubinTateLevelField K hπ n) →ₐ[K]
      ↥(standardLubinTateLevelField K hπ n) :=
  (levelPowerBasis K hπ n).lift _ (aeval_orbit K hπ n u)

private theorem orbitHom_gen (u : 𝒪[K]ˣ) :
    orbitHom K hπ n u (standardLubinTateLevelGenerator K hπ n) =
      ((lubinTateSMul K ↥(standardLubinTateLevelField K hπ n) hπ
          (standardLubinTateSeries hπ) (↑u) (levelGeneratorInteger K hπ n) :
        ↥𝒪[↥(standardLubinTateLevelField K hπ n)]) :
        ↥(standardLubinTateLevelField K hπ n)) :=
  PowerBasis.lift_gen _ _ _

/-- The unit-orbit automorphism: injective by field theory, surjective by dimension. -/
private noncomputable def orbitAut (u : 𝒪[K]ˣ) :
    ↥(standardLubinTateLevelField K hπ n) ≃ₐ[K]
      ↥(standardLubinTateLevelField K hπ n) :=
  AlgEquiv.ofBijective (orbitHom K hπ n u)
    (by
      have hinj : Function.Injective (orbitHom K hπ n u) :=
        (orbitHom K hπ n u).toRingHom.injective
      refine ⟨hinj, ?_⟩
      have hlin : Function.Injective (orbitHom K hπ n u).toLinearMap := hinj
      exact LinearMap.injective_iff_surjective.mp hlin)

/-- The restricted orbit automorphism moves the generator by the scalar. -/
private theorem restrict_orbitAut_generator (u : 𝒪[K]ˣ) :
    algEquivIntegerRestrict K ↥(standardLubinTateLevelField K hπ n)
      (orbitAut K hπ n u) (levelGeneratorInteger K hπ n) =
    lubinTateSMul K ↥(standardLubinTateLevelField K hπ n) hπ
      (standardLubinTateSeries hπ) (↑u) (levelGeneratorInteger K hπ n) := by
  apply Subtype.ext
  exact orbitHom_gen K hπ n u

/-- The restricted automorphisms commute with the scalars — the equivariance of the
evaluated module, read at the scalar face. -/
private theorem restrict_smul (σ : ↥(standardLubinTateLevelField K hπ n) ≃ₐ[K]
      ↥(standardLubinTateLevelField K hπ n))
    (a : ↥𝒪[K]) {x : ↥𝒪[↥(standardLubinTateLevelField K hπ n)]}
    (hx : x ∈ 𝓂[↥(standardLubinTateLevelField K hπ n)]) :
    algEquivIntegerRestrict K ↥(standardLubinTateLevelField K hπ n) σ
      (lubinTateSMul K ↥(standardLubinTateLevelField K hπ n) hπ
        (standardLubinTateSeries hπ) a x) =
    lubinTateSMul K ↥(standardLubinTateLevelField K hπ n) hπ
      (standardLubinTateSeries hπ) a
      (algEquivIntegerRestrict K ↥(standardLubinTateLevelField K hπ n) σ x) := by
  unfold lubinTateSMul
  exact eval₂_algEquiv K ↥(standardLubinTateLevelField K hπ n) σ
    (v := fun _ : Unit => x) (fun _ => hx)
    (lubinTateScalar hπ (standardLubinTateSeries hπ) a)

/-- The orbit map is multiplicative. -/
private theorem orbitAut_mul (u v : 𝒪[K]ˣ) :
    orbitAut K hπ n (u * v) = orbitAut K hπ n u * orbitAut K hπ n v := by
  have hgenmem := levelGeneratorInteger_mem_maximalIdeal K hπ n
  have hext : (orbitAut K hπ n (u * v)).toAlgHom =
      (orbitAut K hπ n u * orbitAut K hπ n v).toAlgHom := by
    apply (levelPowerBasis K hπ n).algHom_ext
    change orbitAut K hπ n (u * v) (levelPowerBasis K hπ n).gen =
      (orbitAut K hπ n u) ((orbitAut K hπ n v) (levelPowerBasis K hπ n).gen)
    have hL : orbitAut K hπ n (u * v) (levelPowerBasis K hπ n).gen =
        ((lubinTateSMul K ↥(standardLubinTateLevelField K hπ n) hπ
            (standardLubinTateSeries hπ) ((↑u : ↥𝒪[K]) * ↑v)
            (levelGeneratorInteger K hπ n) :
          ↥𝒪[↥(standardLubinTateLevelField K hπ n)]) :
          ↥(standardLubinTateLevelField K hπ n)) := by
      have := orbitHom_gen K hπ n (u * v)
      rwa [Units.val_mul] at this
    have hv : orbitAut K hπ n v (levelPowerBasis K hπ n).gen =
        ((lubinTateSMul K ↥(standardLubinTateLevelField K hπ n) hπ
            (standardLubinTateSeries hπ) (↑v) (levelGeneratorInteger K hπ n) :
          ↥𝒪[↥(standardLubinTateLevelField K hπ n)]) :
          ↥(standardLubinTateLevelField K hπ n)) :=
      orbitHom_gen K hπ n v
    rw [hL, hv]
    have hcoe : (orbitAut K hπ n u)
        ((lubinTateSMul K ↥(standardLubinTateLevelField K hπ n) hπ
            (standardLubinTateSeries hπ) (↑v) (levelGeneratorInteger K hπ n) :
          ↥𝒪[↥(standardLubinTateLevelField K hπ n)]) :
          ↥(standardLubinTateLevelField K hπ n)) =
        ((algEquivIntegerRestrict K ↥(standardLubinTateLevelField K hπ n)
            (orbitAut K hπ n u)
            (lubinTateSMul K ↥(standardLubinTateLevelField K hπ n) hπ
              (standardLubinTateSeries hπ) (↑v) (levelGeneratorInteger K hπ n)) :
          ↥𝒪[↥(standardLubinTateLevelField K hπ n)]) :
          ↥(standardLubinTateLevelField K hπ n)) := rfl
    rw [hcoe, restrict_smul K hπ n _ _ hgenmem,
      restrict_orbitAut_generator K hπ n u,
      lubinTateSMul_smul K ↥(standardLubinTateLevelField K hπ n) hπ
        (standardLubinTateSeries hπ) (↑v) (↑u) hgenmem,
      mul_comm ((↑v : ↥𝒪[K])) (↑u)]
  exact AlgEquiv.ext fun x => DFunLike.congr_fun hext x

/-- The orbit automorphism is trivial exactly on the higher unit classes. -/
private theorem orbitAut_eq_one_iff (u : 𝒪[K]ˣ) :
    orbitAut K hπ n u = 1 ↔
      (u : ↥𝒪[K]) - 1 ∈ (𝓂[K] ^ (n + 1) : Ideal ↥𝒪[K]) := by
  have hgenmem := levelGeneratorInteger_mem_maximalIdeal K hπ n
  have hiff := standardLubinTateSMul_eq_iff K
    ↥(standardLubinTateLevelField K hπ n) hπ hgenmem
    (aeval_levelGeneratorInteger K hπ n) (↑u) 1
  rw [lubinTateSMul_one] at hiff
  constructor
  · intro h1
    have happ := congrArg (fun σ : ↥(standardLubinTateLevelField K hπ n) ≃ₐ[K]
        ↥(standardLubinTateLevelField K hπ n) =>
      σ (standardLubinTateLevelGenerator K hπ n)) h1
    simp only [AlgEquiv.one_apply] at happ
    rw [show (orbitAut K hπ n u) (standardLubinTateLevelGenerator K hπ n) =
        ((lubinTateSMul K ↥(standardLubinTateLevelField K hπ n) hπ
            (standardLubinTateSeries hπ) (↑u) (levelGeneratorInteger K hπ n) :
          ↥𝒪[↥(standardLubinTateLevelField K hπ n)]) :
          ↥(standardLubinTateLevelField K hπ n)) from orbitHom_gen K hπ n u] at happ
    exact hiff.mp (Subtype.coe_injective happ)
  · intro hmem
    have heq : lubinTateSMul K ↥(standardLubinTateLevelField K hπ n) hπ
        (standardLubinTateSeries hπ) (↑u) (levelGeneratorInteger K hπ n) =
        levelGeneratorInteger K hπ n := hiff.mpr hmem
    have hext : (orbitAut K hπ n u).toAlgHom =
        (1 : ↥(standardLubinTateLevelField K hπ n) ≃ₐ[K]
          ↥(standardLubinTateLevelField K hπ n)).toAlgHom := by
      apply (levelPowerBasis K hπ n).algHom_ext
      change orbitAut K hπ n u (levelPowerBasis K hπ n).gen =
        (1 : ↥(standardLubinTateLevelField K hπ n) ≃ₐ[K]
          ↥(standardLubinTateLevelField K hπ n)) (levelPowerBasis K hπ n).gen
      rw [show orbitAut K hπ n u (levelPowerBasis K hπ n).gen =
          ((lubinTateSMul K ↥(standardLubinTateLevelField K hπ n) hπ
              (standardLubinTateSeries hπ) (↑u) (levelGeneratorInteger K hπ n) :
            ↥𝒪[↥(standardLubinTateLevelField K hπ n)]) :
            ↥(standardLubinTateLevelField K hπ n)) from orbitHom_gen K hπ n u,
        heq]
      rfl
    exact AlgEquiv.ext fun x => DFunLike.congr_fun hext x

/-- The level character: units acting on the generator's orbit. -/
private noncomputable def levelCharacter :
    𝒪[K]ˣ →* (↥(standardLubinTateLevelField K hπ n) ≃ₐ[K]
      ↥(standardLubinTateLevelField K hπ n)) :=
  MonoidHom.mk' (orbitAut K hπ n) (orbitAut_mul K hπ n)

/-- The character's kernel is the higher unit group. -/
private theorem levelCharacter_ker :
    (levelCharacter K hπ n).ker = integerHigherUnitGroup K (n + 1) := by
  ext u
  rw [MonoidHom.mem_ker,
    show levelCharacter K hπ n u = orbitAut K hπ n u from rfl,
    orbitAut_eq_one_iff K hπ n u]
  exact Iff.rfl

omit [ValuativeRel ↥(standardLubinTateLevelField K hπ n)]
  [TopologicalSpace ↥(standardLubinTateLevelField K hπ n)]
  [ValuativeExtension K ↥(standardLubinTateLevelField K hπ n)]
  [IsMixedCharLocalField ↥(standardLubinTateLevelField K hπ n)] in
/-- The algebra endomorphisms are finite, at most the level degree many. -/
private theorem card_algHom_le :
    Nat.card (↥(standardLubinTateLevelField K hπ n) →ₐ[K]
        ↥(standardLubinTateLevelField K hπ n)) ≤
      (Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) - 1) *
        Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) ^ n := by
  classical
  have hmapmonic : ((standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n).map
      (algebraMap K ↥(standardLubinTateLevelField K hπ n))).Monic :=
    ((standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n).map _).map _
  have hfin : ∀ y : ↥(standardLubinTateLevelField K hπ n),
      Polynomial.aeval y (minpoly K (levelPowerBasis K hπ n).gen) = 0 →
      y ∈ ((standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n).map
        (algebraMap K ↥(standardLubinTateLevelField K hπ n))).roots.toFinset := by
    intro y hy
    rw [minpoly_levelPowerBasis_gen K hπ n] at hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hmapmonic.ne_zero,
      Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hy
  have hinj : Function.Injective
      (fun y : {y : ↥(standardLubinTateLevelField K hπ n) //
          Polynomial.aeval y (minpoly K (levelPowerBasis K hπ n).gen) = 0} =>
        (⟨y.1, hfin y.1 y.2⟩ :
          ((standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n).map
            (algebraMap K ↥(standardLubinTateLevelField K hπ n))).roots.toFinset)) :=
    fun a b h => Subtype.ext (Subtype.mk_eq_mk.mp h)
  have h1 : Nat.card (↥(standardLubinTateLevelField K hπ n) →ₐ[K]
      ↥(standardLubinTateLevelField K hπ n)) =
      Nat.card {y : ↥(standardLubinTateLevelField K hπ n) //
        Polynomial.aeval y (minpoly K (levelPowerBasis K hπ n).gen) = 0} :=
    Nat.card_congr (levelPowerBasis K hπ n).liftEquiv
  have h2 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_finsetCard] at h2
  have h3 := Multiset.toFinset_card_le
    ((standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n).map
      (algebraMap K ↥(standardLubinTateLevelField K hπ n))).roots
  have h4 := Polynomial.card_roots'
    ((standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n).map
      (algebraMap K ↥(standardLubinTateLevelField K hπ n)))
  have h5 : ((standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n).map
      (algebraMap K ↥(standardLubinTateLevelField K hπ n))).natDegree =
      (Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) - 1) *
        Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) ^ n := by
    rw [standardLubinTatePrimitivePolynomialOverField,
      ((standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n).map
        (algebraMap ↥𝒪[K] K)).natDegree_map,
      (standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n).natDegree_map,
      standardLubinTatePrimitivePolynomial_natDegree]
  omega

omit [ValuativeRel ↥(standardLubinTateLevelField K hπ n)]
  [TopologicalSpace ↥(standardLubinTateLevelField K hπ n)]
  [ValuativeExtension K ↥(standardLubinTateLevelField K hπ n)]
  [IsMixedCharLocalField ↥(standardLubinTateLevelField K hπ n)] in
/-- The endomorphisms are finite. -/
private theorem finite_algHom :
    Finite (↥(standardLubinTateLevelField K hπ n) →ₐ[K]
      ↥(standardLubinTateLevelField K hπ n)) := by
  classical
  have hmapmonic : ((standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n).map
      (algebraMap K ↥(standardLubinTateLevelField K hπ n))).Monic :=
    ((standardLubinTatePrimitivePolynomial_monic ↥𝒪[K] π n).map _).map _
  have hfin : ∀ y : ↥(standardLubinTateLevelField K hπ n),
      Polynomial.aeval y (minpoly K (levelPowerBasis K hπ n).gen) = 0 →
      y ∈ ((standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n).map
        (algebraMap K ↥(standardLubinTateLevelField K hπ n))).roots.toFinset := by
    intro y hy
    rw [minpoly_levelPowerBasis_gen K hπ n] at hy
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hmapmonic.ne_zero,
      Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def]
    exact hy
  haveI hsub : Finite {y : ↥(standardLubinTateLevelField K hπ n) //
      Polynomial.aeval y (minpoly K (levelPowerBasis K hπ n).gen) = 0} :=
    Finite.of_injective
      (fun y : {y : ↥(standardLubinTateLevelField K hπ n) //
          Polynomial.aeval y (minpoly K (levelPowerBasis K hπ n).gen) = 0} =>
        (⟨y.1, hfin y.1 y.2⟩ :
          ((standardLubinTatePrimitivePolynomialOverField ↥𝒪[K] K π n).map
            (algebraMap K ↥(standardLubinTateLevelField K hπ n))).roots.toFinset))
      (fun a b h => Subtype.ext (Subtype.mk_eq_mk.mp h))
  exact Finite.of_equiv _ (levelPowerBasis K hπ n).liftEquiv.symm

omit [ValuativeRel ↥(standardLubinTateLevelField K hπ n)]
  [TopologicalSpace ↥(standardLubinTateLevelField K hπ n)]
  [ValuativeExtension K ↥(standardLubinTateLevelField K hπ n)]
  [IsMixedCharLocalField ↥(standardLubinTateLevelField K hπ n)] in
/-- The automorphisms are finite. -/
private theorem finite_aut :
    Finite (↥(standardLubinTateLevelField K hπ n) ≃ₐ[K]
      ↥(standardLubinTateLevelField K hπ n)) := by
  haveI := finite_algHom K hπ n
  exact Finite.of_injective _ (AlgEquiv.coe_toAlgHom_injective
    (R := K) (A₁ := ↥(standardLubinTateLevelField K hπ n))
    (A₂ := ↥(standardLubinTateLevelField K hπ n)))

/-- The descended character on the unit-parameter quotient. -/
private noncomputable def levelParameterHom :
    (𝒪[K]ˣ ⧸ integerHigherUnitGroup K (n + 1)) →*
      (↥(standardLubinTateLevelField K hπ n) ≃ₐ[K]
        ↥(standardLubinTateLevelField K hπ n)) :=
  (QuotientGroup.kerLift (levelCharacter K hπ n)).comp
    (QuotientGroup.quotientMulEquivOfEq (levelCharacter_ker K hπ n).symm).toMonoidHom

private theorem levelParameterHom_injective :
    Function.Injective (levelParameterHom K hπ n) :=
  (QuotientGroup.kerLift_injective (levelCharacter K hπ n)).comp
    (QuotientGroup.quotientMulEquivOfEq (levelCharacter_ker K hπ n).symm).injective

/-- The squeeze: the automorphism count equals the unit-parameter count. -/
private theorem card_aut_eq :
    Nat.card (↥(standardLubinTateLevelField K hπ n) ≃ₐ[K]
        ↥(standardLubinTateLevelField K hπ n)) =
      (Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) - 1) *
        Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) ^ n := by
  haveI := finite_aut K hπ n
  haveI := finite_algHom K hπ n
  have hQ : Nat.card (𝒪[K]ˣ ⧸ integerHigherUnitGroup K (n + 1)) =
      (Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) - 1) *
        Nat.card (IsLocalRing.ResidueField ↥𝒪[K]) ^ n := by
    have := integerHigherUnitCount K (n + 1) (Nat.succ_ne_zero n)
    simpa using this
  have hup := Nat.card_le_card_of_injective _ (levelParameterHom_injective K hπ n)
  have hdown := Nat.card_le_card_of_injective _ (AlgEquiv.coe_toAlgHom_injective
    (R := K) (A₁ := ↥(standardLubinTateLevelField K hπ n))
    (A₂ := ↥(standardLubinTateLevelField K hπ n)))
  have hAH := card_algHom_le K hπ n
  omega

/-- The unit-parameter description, under the hypothesized carrier. -/
private theorem nonempty_description :
    Nonempty ((𝒪[K]ˣ ⧸ integerHigherUnitGroup K (n + 1)) ≃*
      (↥(standardLubinTateLevelField K hπ n) ≃ₐ[K]
        ↥(standardLubinTateLevelField K hπ n))) := by
  haveI := finite_aut K hπ n
  refine ⟨MulEquiv.ofBijective (levelParameterHom K hπ n) ?_⟩
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨levelParameterHom_injective K hπ n, ?_⟩
  rw [card_aut_eq K hπ n]
  have := integerHigherUnitCount K (n + 1) (Nat.succ_ne_zero n)
  simpa using this

/-- The level field is Galois, by the automorphism count. -/
private theorem isGalois_level :
    IsGalois K ↥(standardLubinTateLevelField K hπ n) := by
  haveI := finite_aut K hπ n
  apply IsGalois.of_card_aut_eq_finrank
  rw [card_aut_eq K hπ n, standardLubinTateLevelField_finrank K hπ n]

/-- The Galois group is commutative, transported from the unit parameters. -/
private theorem isMulCommutative_level :
    IsMulCommutative (↥(standardLubinTateLevelField K hπ n) ≃ₐ[K]
      ↥(standardLubinTateLevelField K hπ n)) := by
  haveI := finite_aut K hπ n
  have hbij : Function.Bijective (levelParameterHom K hπ n) := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨levelParameterHom_injective K hπ n, ?_⟩
    rw [card_aut_eq K hπ n]
    have := integerHigherUnitCount K (n + 1) (Nat.succ_ne_zero n)
    simpa using this
  constructor
  constructor
  intro σ τ
  obtain ⟨a, rfl⟩ := hbij.2 σ
  obtain ⟨b, rfl⟩ := hbij.2 τ
  rw [← map_mul, ← map_mul, mul_comm a b]

end Generator

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- The **unit-parameter description of the level Galois group**:
`𝒪ˣ/U^{(n+1)} ≃* Gal(Lₙ/K)` — deliberately weaker than the source, which constructs
the specific `[u⁻¹]`-action on the chosen torsion point
([Milne 2020, Chap. I, §3, Thm. 3.6 (b), p.38][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/LevelAbelian.lean:53`,
`standardLubinTateUnitParameterEquivGal`][Yamaguchi2026]). -/
theorem nonempty_standardLubinTateGaloisDescription {π : 𝒪[K]} (hπ : Irreducible π)
    (n : ℕ) :
    Nonempty ((𝒪[K]ˣ ⧸ integerHigherUnitGroup K (n + 1)) ≃*
      (standardLubinTateLevelField K hπ n ≃ₐ[K]
        standardLubinTateLevelField K hπ n)) := by
  obtain ⟨vL, tL, hVE, _, hMCL⟩ :=
    exists_extension_isMixedCharLocalField K ↥(standardLubinTateLevelField K hπ n)
  letI := vL
  letI := tL
  haveI := hVE
  haveI := hMCL
  exact nonempty_description K hπ n

/-- Every standard level field is **abelian Galois** over the base local field
([Milne 2020, Chap. I, §3, Thm. 3.6 (b), p.38][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/LevelAbelian.lean:141`][Yamaguchi2026]). -/
theorem standardLubinTateLevelField_isAbelianGalois {π : 𝒪[K]} (hπ : Irreducible π)
    (n : ℕ) :
    IsAbelianGalois K (standardLubinTateLevelField K hπ n) := by
  obtain ⟨vL, tL, hVE, _, hMCL⟩ :=
    exists_extension_isMixedCharLocalField K ↥(standardLubinTateLevelField K hπ n)
  letI := vL
  letI := tL
  haveI := hVE
  haveI := hMCL
  haveI := isGalois_level K hπ n
  haveI := isMulCommutative_level K hπ n
  constructor

/-- The level field is **Galois** over the base — the abelian description, weakened to
the plain Galois statement the compositum machinery consumes. -/
theorem standardLubinTateLevelField_isGalois {π : 𝒪[K]} (hπ : Irreducible π) (n : ℕ) :
    IsGalois K ↥(standardLubinTateLevelField K hπ n) :=
  (standardLubinTateLevelField_isAbelianGalois K hπ n).toIsGalois

end Atlas.Knowledge
