import Mathlib
import Atlas.Knowledge.QuotientNormalOfProfinite

/-!
# residue-action exact sequence of a decomposition group

For a possibly infinite Galois extension and a chosen extension valuation, the
residue extension over the decomposition field is normal and reduction gives
the exact sequence `1 → I_w → G_w → Gal(λ/κ) → 1`. The base residue field is
presented intrinsically as the fixed subring of the chosen valuation ring
modulo the contraction of its maximal ideal — that fixed subring is exactly
the valuation ring on the decomposition field — and the profinite surjectivity
is Mathlib's compact inverse-limit argument. This is the correspondence input
of the reciprocity engine's local-side instantiation (#104).

## Main definitions

* `decompositionGroup` / `inertiaGroup` / `residueAction` /
  `decompositionField` — Mathlib's decomposition data, named for the layer.
* `decompositionResidueField` / `selectedResidueField` — the base and target
  residue fields `κ` and `λ`.
* `decompositionGroupResidueAction` — the residue action of `G_w` on `λ/κ`.
* `decompositionQuotientEquivResidueGalois` — the quotient form
  `G_w ⧸ I_w ≃* Gal(λ/κ)`.

## Main statements

* `decompositionGroup_isClosed` — the decomposition group is Krull-closed;
  proved.
* `decompositionGroupResidueAction_ker` — the kernel is the inertia group;
  proved.
* `decompositionGroupResidueAction_surjective` — reduction is onto the full
  residue Galois group, including the infinite case; proved.
* `decompositionResidueExtension_normal` — `λ/κ` is normal; proved.
* `decompositionGroupResidueAction_shortExact` — the exact sequence; proved.

## Implementation notes

The decomposition and inertia groups and the residue action are Mathlib's
(`ValuationSubring.decompositionSubgroup`, `inertiaSubgroup`,
`MulSemiringAction.toRingAut`), named here once for the layer. The compactness
and continuity of the action on the discrete valuation ring come from
local-constancy on adjoined finite subextensions; surjectivity rides Mathlib's
`Ideal.Quotient.stabilizerHom_surjective_of_profinite` after identifying the
whole decomposition group with the maximal ideal's stabilizer, and normality
rides `Atlas.Knowledge.quotient_normal_of_profinite`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

open scoped Pointwise Topology

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- **The decomposition group** of a valuation subring — Mathlib's
`ValuationSubring.decompositionSubgroup`, named for the layer
([Yamaguchi 2026, `RamificationTheory/HilbertRamification/ValuationSubring.lean:30`]
[Yamaguchi2026]). -/
abbrev decompositionGroup (A : ValuationSubring L) : Subgroup (L ≃ₐ[K] L) :=
  A.decompositionSubgroup K

/-- **The inertia group** — Mathlib's `ValuationSubring.inertiaSubgroup`
([Yamaguchi 2026, `RamificationTheory/HilbertRamification/ValuationSubring.lean:36`]
[Yamaguchi2026]). -/
abbrev inertiaGroup (A : ValuationSubring L) :
    Subgroup (decompositionGroup K A) :=
  A.inertiaSubgroup K

/-- The residue action of the decomposition group on the residue field. -/
abbrev residueAction (A : ValuationSubring L) :
    decompositionGroup K A →*
      (IsLocalRing.ResidueField A ≃+* IsLocalRing.ResidueField A) :=
  MulSemiringAction.toRingAut
    (A.decompositionSubgroup K) (IsLocalRing.ResidueField A)

/-- The inertia group is the kernel of the residue action. -/
theorem residueAction_ker (A : ValuationSubring L) :
    MonoidHom.ker (residueAction K A) = inertiaGroup K A := by
  rfl

/-- The inertia group is normal: it is a kernel. -/
instance inertiaGroup_normal (A : ValuationSubring L) :
    (inertiaGroup K A).Normal := by
  rw [← residueAction_ker (K := K) A]
  infer_instance

/-- **The decomposition field** `Z_w`: the fixed field of the decomposition
group ([Yamaguchi 2026,
`RamificationTheory/HilbertRamification/ValuationSubring.lean:148`]
[Yamaguchi2026]). -/
abbrev decompositionField (A : ValuationSubring L) : IntermediateField K L :=
  IntermediateField.fixedField (decompositionGroup K A)

variable [Algebra.IsAlgebraic K L]

omit [Algebra.IsAlgebraic K L] in
/-- Membership in the decomposition group is preserving the valuation ring. -/
theorem mem_decompositionGroup_iff_apply_mem
    (A : ValuationSubring L) (sigma : L ≃ₐ[K] L) :
    sigma ∈ decompositionGroup K A ↔
      ∀ x : L, sigma x ∈ A ↔ x ∈ A := by
  change sigma • A = A ↔ _
  constructor
  · intro hsigma x
    have hmem := congrArg (fun B : ValuationSubring L => sigma x ∈ B) hsigma
    change (sigma x ∈ sigma • A) = (sigma x ∈ A) at hmem
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hmem
    change (sigma⁻¹ (sigma x) ∈ A) = (sigma x ∈ A) at hmem
    have hinv : sigma⁻¹ (sigma x) = x := by simp
    rw [hinv] at hmem
    exact hmem.symm.to_iff
  · intro hsigma
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simpa using (hsigma (sigma⁻¹ x)).symm

/-- **The decomposition group is closed** in the Krull topology: an
automorphism moving the ring out of itself does so on an adjoined finite
subextension
([Yamaguchi 2026, `RamificationTheory/ClosedSubgroups.lean:49`]
[Yamaguchi2026]). -/
theorem decompositionGroup_isClosed (A : ValuationSubring L) :
    IsClosed (decompositionGroup K A : Set (L ≃ₐ[K] L)) where
  isOpen_compl := isOpen_iff_mem_nhds.mpr fun sigma hsigma => by
    rw [Set.mem_compl_iff, SetLike.mem_coe,
      mem_decompositionGroup_iff_apply_mem] at hsigma
    rcases Classical.not_forall.mp hsigma with ⟨x, hx⟩
    let E : IntermediateField K L := IntermediateField.adjoin K {x}
    letI : FiniteDimensional K E :=
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral x)
    apply mem_nhds_iff.mpr
    refine ⟨sigma • (E.fixingSubgroup : Set (L ≃ₐ[K] L)), ?_, ?_, ?_⟩
    · intro tau htau
      rcases Set.mem_smul_set.mp htau with ⟨g, hg, rfl⟩
      rw [Set.mem_compl_iff, SetLike.mem_coe,
        mem_decompositionGroup_iff_apply_mem]
      intro hmem
      apply hx
      have hgx : g x = x :=
        (IntermediateField.mem_fixingSubgroup_iff E g).mp hg x
          (IntermediateField.subset_adjoin (F := K) (S := {x}) (by simp))
      simpa [AlgEquiv.mul_apply, hgx] using hmem x
    · exact E.fixingSubgroup_isOpen.smul sigma
    · exact ⟨1, E.fixingSubgroup.one_mem, by simp⟩

variable [IsGalois K L]

/-- The valuation ring on the decomposition field, as the fixed subring of the
decomposition group inside the chosen valuation ring. -/
abbrev decompositionFixedSubring (A : ValuationSubring L) : Subring A :=
  FixedPoints.subring A (decompositionGroup K A)

/-- The maximal ideal of the decomposition-field valuation ring. -/
abbrev decompositionFixedMaximalIdeal (A : ValuationSubring L) :
    Ideal (decompositionFixedSubring K A) :=
  (IsLocalRing.maximalIdeal A).comap (decompositionFixedSubring K A).subtype

/-- **The base residue field `κ`** of the residue-action exact sequence. -/
abbrev decompositionResidueField (A : ValuationSubring L) :=
  decompositionFixedSubring K A ⧸ decompositionFixedMaximalIdeal K A

/-- **The target residue field `λ`**. -/
abbrev selectedResidueField (A : ValuationSubring L) :=
  IsLocalRing.ResidueField A

/-- The literal valuation ring on the decomposition field `Z_w`. -/
abbrev decompositionFieldValuationSubring (A : ValuationSubring L) :
    ValuationSubring (decompositionField K A) :=
  A.comap (decompositionField K A).val

/-- **The fixed-subring presentation is the literal valuation ring on `Z_w`**
([Yamaguchi 2026,
`RamificationTheory/HilbertRamification/ResidueExactSequence.lean:60`]
[Yamaguchi2026]). -/
def decompositionFieldValuationSubringEquivFixedSubring
    (A : ValuationSubring L) :
    decompositionFieldValuationSubring K A ≃+*
      decompositionFixedSubring K A where
  toFun z :=
    ⟨⟨((z : decompositionField K A) : L), z.property⟩, by
      intro sigma
      apply Subtype.ext
      change ((sigma : decompositionGroup K A) : L ≃ₐ[K] L)
          ((z : decompositionField K A) : L) =
        ((z : decompositionField K A) : L)
      exact (IntermediateField.mem_fixedField_iff
        (H := decompositionGroup K A) ((z : decompositionField K A) : L)).mp
          (z : decompositionField K A).property
          (sigma : L ≃ₐ[K] L) sigma.property⟩
  invFun r := by
    let z : decompositionField K A :=
      ⟨((r : A) : L), by
        rw [IntermediateField.mem_fixedField_iff]
        intro sigma hsigma
        have hr := r.property ⟨sigma, hsigma⟩
        exact congrArg Subtype.val hr⟩
    exact ⟨z, r.val.property⟩
  left_inv z := by ext; rfl
  right_inv r := by ext; rfl
  map_add' _ _ := by ext; rfl
  map_mul' _ _ := by ext; rfl

/-- The fixed subring is local: it is a valuation ring. -/
instance decompositionFixedSubring.instIsLocalRing
    (A : ValuationSubring L) :
    IsLocalRing (decompositionFixedSubring K A) :=
  (decompositionFieldValuationSubringEquivFixedSubring (K := K) A).isLocalRing

omit [IsGalois K L] in
private theorem decompositionGroup_action_locallyConstant
    (A : ValuationSubring L) (a : A) :
    IsLocallyConstant (fun g : decompositionGroup K A ↦ g • a) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro sigma
  let E : IntermediateField K L := IntermediateField.adjoin K {(a : L)}
  letI : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional
      (Algebra.IsIntegral.isIntegral (a : L))
  let U : Set (decompositionGroup K A) :=
    ((↑) : decompositionGroup K A → (L ≃ₐ[K] L)) ⁻¹'
      (((sigma : L ≃ₐ[K] L)) • (E.fixingSubgroup : Set (L ≃ₐ[K] L)))
  refine ⟨U, E.fixingSubgroup_isOpen.smul
      (sigma : L ≃ₐ[K] L) |>.preimage continuous_subtype_val, ?_, ?_⟩
  · exact ⟨1, E.fixingSubgroup.one_mem, by simp⟩
  · intro tau htau
    rcases htau with ⟨g, hg, heq⟩
    have hga : g (a : L) = (a : L) :=
      (IntermediateField.mem_fixingSubgroup_iff E g).mp hg (a : L)
        (IntermediateField.subset_adjoin (F := K) (S := {(a : L)}) (by simp))
    apply Subtype.ext
    change (((tau : decompositionGroup K A) : L ≃ₐ[K] L) (a : L)) =
      (((sigma : decompositionGroup K A) : L ≃ₐ[K] L) (a : L))
    rw [← heq]
    simp [AlgEquiv.mul_apply, hga]

omit [IsGalois K L] in
private theorem decompositionGroup_continuousSMul
    (A : ValuationSubring L) :
    letI : TopologicalSpace A := ⊥
    ContinuousSMul (decompositionGroup K A) A := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  constructor
  rw [continuous_prod_of_discrete_right]
  intro a
  exact (decompositionGroup_action_locallyConstant (K := K) A a).continuous

private theorem decompositionGroup_compactSpace
    (A : ValuationSubring L) :
    CompactSpace (decompositionGroup K A) :=
  (Topology.IsClosedEmbedding.subtypeVal
    (decompositionGroup_isClosed K A)).compactSpace

omit [Algebra.IsAlgebraic K L] [IsGalois K L] in
private theorem decompositionFixedSubring_smulCommClass
    (A : ValuationSubring L) :
    SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A := by
  constructor
  intro g r x
  change g • ((r : A) * x) = (r : A) * (g • x)
  rw [smul_mul', r.property g]

omit [Algebra.IsAlgebraic K L] [IsGalois K L] in
private theorem decompositionFixedSubring_isInvariant
    (A : ValuationSubring L) :
    Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) := by
  constructor
  intro x hx
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The commuting-action instance of the fixed subring. -/
instance decompositionFixedSubring.instSMulCommClass
    (A : ValuationSubring L) :
    SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A :=
  decompositionFixedSubring_smulCommClass (K := K) A

/-- The invariance instance of the fixed subring. -/
instance decompositionFixedSubring.instIsInvariant
    (A : ValuationSubring L) :
    Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) :=
  decompositionFixedSubring_isInvariant (K := K) A

private theorem decompositionFixedMaximalIdeal_isMaximal
    (A : ValuationSubring L) :
    (decompositionFixedMaximalIdeal K A).IsMaximal := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : CompactSpace (decompositionGroup K A) :=
    decompositionGroup_compactSpace (K := K) A
  letI : ContinuousSMul (decompositionGroup K A) A :=
    decompositionGroup_continuousSMul (K := K) A
  letI : SMulCommClass (decompositionGroup K A)
      (decompositionFixedSubring K A) A :=
    decompositionFixedSubring_smulCommClass (K := K) A
  letI : Algebra.IsInvariant (decompositionFixedSubring K A) A
      (decompositionGroup K A) :=
    decompositionFixedSubring_isInvariant (K := K) A
  letI : Algebra.IsIntegral (decompositionFixedSubring K A) A :=
    Algebra.IsInvariant.isIntegral_of_profinite
      (G := decompositionGroup K A)
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (IsLocalRing.maximalIdeal A)

/-- The contracted ideal is maximal. -/
instance decompositionFixedMaximalIdeal.instIsMaximal
    (A : ValuationSubring L) :
    (decompositionFixedMaximalIdeal K A).IsMaximal :=
  decompositionFixedMaximalIdeal_isMaximal (K := K) A

/-- The contracted ideal is the actual maximal ideal of the fixed subring. -/
theorem decompositionFixedMaximalIdeal_eq_maximalIdeal
    (A : ValuationSubring L) :
    decompositionFixedMaximalIdeal K A =
      IsLocalRing.maximalIdeal (decompositionFixedSubring K A) :=
  IsLocalRing.eq_maximalIdeal
    (decompositionFixedMaximalIdeal.instIsMaximal (K := K) A)

/-- **The literal residue field of `Z_w` is the base residue field**
([Yamaguchi 2026,
`RamificationTheory/HilbertRamification/ResidueExactSequence.lean:208`]
[Yamaguchi2026]). -/
def decompositionFieldResidueEquiv (A : ValuationSubring L) :
    IsLocalRing.ResidueField (decompositionFieldValuationSubring K A) ≃+*
      decompositionResidueField K A :=
  (IsLocalRing.ResidueField.mapEquiv
      (decompositionFieldValuationSubringEquivFixedSubring (K := K) A)).trans
    (Ideal.quotientEquivAlgOfEq ℤ
      (decompositionFixedMaximalIdeal_eq_maximalIdeal
        (K := K) A).symm).toRingEquiv

/-- The selected maximal ideal lies over the contracted one. -/
instance selectedMaximalIdeal.instLiesOver (A : ValuationSubring L) :
    (IsLocalRing.maximalIdeal A).LiesOver
      (decompositionFixedMaximalIdeal K A) := by
  constructor
  rfl

/-- The base residue field is a field. -/
noncomputable instance decompositionResidueField.instField
    (A : ValuationSubring L) :
    Field (decompositionResidueField K A) :=
  Ideal.Quotient.field (decompositionFixedMaximalIdeal K A)

/-- The residue extension's algebra structure. -/
noncomputable instance selectedResidueField.instAlgebra
    (A : ValuationSubring L) :
    Algebra (decompositionResidueField K A) (selectedResidueField A) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (le_of_eq ((IsLocalRing.maximalIdeal A).over_def
      (decompositionFixedMaximalIdeal K A)))

omit [Algebra.IsAlgebraic K L] [IsGalois K L] in
/-- Every decomposition automorphism stabilizes the maximal ideal. -/
theorem decompositionGroup_maximalIdeal_stabilizer_eq_top
    (A : ValuationSubring L) :
    MulAction.stabilizer (decompositionGroup K A)
        (IsLocalRing.maximalIdeal A) = ⊤ := by
  apply top_unique
  intro sigma _hsigma
  change sigma • IsLocalRing.maximalIdeal A = IsLocalRing.maximalIdeal A
  apply Ideal.ext
  intro x
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [IsLocalRing.mem_maximalIdeal]
  constructor
  · intro hnonunit hx
    apply hnonunit
    simpa using hx.map (MulSemiringAction.toRingAut
      (decompositionGroup K A) A sigma⁻¹)
  · intro hnonunit hx
    apply hnonunit
    simpa using hx.map (MulSemiringAction.toRingAut
      (decompositionGroup K A) A sigma)

/- The decomposition group as the stabilizer of the selected maximal ideal. -/
private def decompositionGroupToMaximalIdealStabilizer
    (A : ValuationSubring L) :
    decompositionGroup K A →*
      MulAction.stabilizer (decompositionGroup K A)
        (IsLocalRing.maximalIdeal A) where
  toFun sigma := ⟨sigma, by
    rw [decompositionGroup_maximalIdeal_stabilizer_eq_top (K := K) A]
    exact Subgroup.mem_top sigma⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- **The residue action of `G_w` on `λ/κ`**
([Yamaguchi 2026,
`RamificationTheory/HilbertRamification/ResidueExactSequence.lean:277`]
[Yamaguchi2026]). -/
def decompositionGroupResidueAction (A : ValuationSubring L) :
    decompositionGroup K A →*
      (selectedResidueField A ≃ₐ[decompositionResidueField K A]
        selectedResidueField A) :=
  (Ideal.Quotient.stabilizerHom
      (IsLocalRing.maximalIdeal A)
      (decompositionFixedMaximalIdeal K A)
      (decompositionGroup K A)).comp
    (decompositionGroupToMaximalIdealStabilizer (K := K) A)

omit [Algebra.IsAlgebraic K L] [IsGalois K L] in
/-- The residue action computes on residues. -/
@[simp] theorem decompositionGroupResidueAction_residue
    (A : ValuationSubring L)
    (sigma : decompositionGroup K A) (x : A) :
    decompositionGroupResidueAction (K := K) A sigma
        (IsLocalRing.residue A x) =
      IsLocalRing.residue A (sigma • x) :=
  rfl

omit [Algebra.IsAlgebraic K L] [IsGalois K L] in
/-- **The kernel of the residue action is the inertia group**
([Yamaguchi 2026,
`RamificationTheory/HilbertRamification/ResidueExactSequence.lean:324`]
[Yamaguchi2026]). -/
theorem decompositionGroupResidueAction_ker (A : ValuationSubring L) :
    MonoidHom.ker (decompositionGroupResidueAction (K := K) A) =
      inertiaGroup K A := by
  ext sigma
  rw [MonoidHom.mem_ker, ← residueAction_ker (K := K) A,
    MonoidHom.mem_ker]
  constructor
  · intro hsigma
    ext y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    have h := DFunLike.congr_fun hsigma (IsLocalRing.residue A x)
    exact h
  · intro hsigma
    apply AlgEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    have h := DFunLike.congr_fun hsigma (IsLocalRing.residue A x)
    exact h

/-- **Reduction is onto the full residue Galois group**, including the
infinite case — Mathlib's profinite stabilizer surjectivity applied to the
whole decomposition group
([Yamaguchi 2026,
`RamificationTheory/HilbertRamification/ResidueExactSequence.lean:347`]
[Yamaguchi2026]). -/
theorem decompositionGroupResidueAction_surjective (A : ValuationSubring L) :
    Function.Surjective (decompositionGroupResidueAction (K := K) A) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : CompactSpace (decompositionGroup K A) :=
    decompositionGroup_compactSpace (K := K) A
  letI : ContinuousSMul (decompositionGroup K A) A :=
    decompositionGroup_continuousSMul (K := K) A
  intro sigma
  obtain ⟨tau, htau⟩ :=
    Ideal.Quotient.stabilizerHom_surjective_of_profinite
      (G := decompositionGroup K A)
      (decompositionFixedMaximalIdeal K A)
      (IsLocalRing.maximalIdeal A) sigma
  refine ⟨tau.1, ?_⟩
  have htau_eq :
      decompositionGroupToMaximalIdealStabilizer (K := K) A tau.1 = tau := by
    apply Subtype.ext
    rfl
  change
    Ideal.Quotient.stabilizerHom
        (IsLocalRing.maximalIdeal A)
        (decompositionFixedMaximalIdeal K A)
        (decompositionGroup K A)
        (decompositionGroupToMaximalIdealStabilizer (K := K) A tau.1) =
      sigma
  rw [htau_eq]
  exact htau

/-- **The residue extension `λ/κ` is normal**, also in the infinite case. -/
instance decompositionResidueExtension_normal (A : ValuationSubring L) :
    Normal (decompositionResidueField K A) (selectedResidueField A) := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : CompactSpace (decompositionGroup K A) :=
    decompositionGroup_compactSpace (K := K) A
  letI : ContinuousSMul (decompositionGroup K A) A :=
    decompositionGroup_continuousSMul (K := K) A
  exact quotient_normal_of_profinite
    (G := decompositionGroup K A)
    (decompositionFixedMaximalIdeal K A)
    (IsLocalRing.maximalIdeal A)

omit [Algebra.IsAlgebraic K L] [IsGalois K L] in
/-- Exactness at `G_w`. -/
theorem inertiaGroup_mulExact_decompositionGroupResidueAction
    (A : ValuationSubring L) :
    Function.MulExact (inertiaGroup K A).subtype
      (decompositionGroupResidueAction (K := K) A) := by
  rw [MonoidHom.mulExact_iff, decompositionGroupResidueAction_ker]
  exact (Subgroup.range_subtype _).symm

/-- **The residue-action exact sequence**
`1 → I_w → G_w → Gal(λ/κ) → 1`
([Yamaguchi 2026,
`RamificationTheory/HilbertRamification/ResidueExactSequence.lean:409`]
[Yamaguchi2026]). -/
theorem decompositionGroupResidueAction_shortExact (A : ValuationSubring L) :
    Function.Injective (inertiaGroup K A).subtype ∧
      Function.MulExact (inertiaGroup K A).subtype
        (decompositionGroupResidueAction (K := K) A) ∧
      Function.Surjective (decompositionGroupResidueAction (K := K) A) :=
  ⟨Subtype.coe_injective,
    inertiaGroup_mulExact_decompositionGroupResidueAction (K := K) A,
    decompositionGroupResidueAction_surjective (K := K) A⟩

/-- **The quotient form** `G_w ⧸ I_w ≃* Gal(λ/κ)`
([Yamaguchi 2026,
`RamificationTheory/HilbertRamification/ResidueExactSequence.lean:421`]
[Yamaguchi2026]). -/
def decompositionQuotientEquivResidueGalois (A : ValuationSubring L) :
    decompositionGroup K A ⧸ inertiaGroup K A ≃*
      (selectedResidueField A ≃ₐ[decompositionResidueField K A]
        selectedResidueField A) :=
  (QuotientGroup.quotientMulEquivOfEq
      (decompositionGroupResidueAction_ker (K := K) A).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (decompositionGroupResidueAction (K := K) A)
      (decompositionGroupResidueAction_surjective (K := K) A))

/-- The quotient form computes on representatives. -/
@[simp] theorem decompositionQuotientEquivResidueGalois_mk
    (A : ValuationSubring L) (sigma : decompositionGroup K A) :
    decompositionQuotientEquivResidueGalois (K := K) A
        (QuotientGroup.mk' (inertiaGroup K A) sigma) =
      decompositionGroupResidueAction (K := K) A sigma := by
  simp [decompositionQuotientEquivResidueGalois,
    QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse]

end

end Atlas.Knowledge
