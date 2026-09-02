import Mathlib
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteReciprocityNaturalityNorm
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.IntermediateGaloisCorrespondence
import Atlas.Knowledge.ReciprocityExactRows
import Atlas.Knowledge.ReciprocityReductionArithmetic
import Atlas.Knowledge.ReductionGaloisArrows
import Atlas.Knowledge.TransferNormNaturality

/-!
# reduction diagram chases

The representation-level content of the three reductions: the norm
arrow and the fixed-element inclusion for the actual intermediate field
cut out by `S ≤ G(L/K)` — constructed without any normality assumption
on the intermediate extension, as the Sylow reduction requires — with
the identity `N_{M/K} ∘ i = [M:K]`; the injectivity of the lower norm
arrow at the maximal unramified subextension; and the pure diagram
chases the reductions apply to the reciprocity homomorphisms (#104).

## Main definitions

* `FiniteGaloisSubextension.intermediateNormMap` — the norm arrow for a
  possibly nonnormal intermediate field.

## Main statements

* `FiniteGaloisSubextension.intermediateNormMap_comp_inclusion` — the
  identity `N_{M/K} ∘ i = [M:K]` for an arbitrary intermediate field;
  proved.
* `FiniteGaloisSubextension.maximalUnramified_normMap_injective` — the
  lower norm arrow at the inertia-image field is injective in the
  cyclic case; proved.
* `abstractReciprocity_bijective_of_exact_diagram` — the third
  reduction's diagram chase; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling —
under which the source's `simpa only using L.finite` and
`simpa only using L.normal` proof-term adjustments vanish with the
containment argument they adjusted, closing by the field itself — and
`extensionSubgroup_over_intermediate_normal` is the layer's
`subgroupOf_over_intermediate_normal`. One `noncomputable section`
holds two ambient-group scopes with a shadowing `variable` line between
them, the way `Atlas.Knowledge.ReciprocityExactRows` does: the
fixed-element inclusion pair, the two diagram chases, the commutator
kernel lemma, and the two kernel arguments precede it (the chases and
the commutator lemma polymorphic in their own groups and mentioning no
ambient one), while the four declarations that consume the Type-pinned
`Atlas.Knowledge.finiteReciprocityNaturalityNormMap` or
`Atlas.Knowledge.abstractReciprocityNormMap` — the norm-arrow trio and
the maximal-unramified injectivity — follow the second, `{G : Type}`,
variable line, which reorders both source sections' contents. This
completes `Reciprocity/Reduction.lean`: the `GroupOnly` section is the
layer's `Atlas.Knowledge.ReductionGaloisArrows`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- Inclusion of fixed elements, descended to the two actual norm
quotients — the map `i` in the Sylow argument ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:100`]
[Yamaguchi2026]). -/
def intermediateNormQuotientInclusion (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    letI : Finite (K.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.toSubgroup) := L.finite
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        L.field.toSubgroup.subgroupOf
          (L.intermediateField S).toSubgroup) :=
      L.extension_over_intermediate_finite S
    FiniteNormQuotient A K L.field L.below →+
      FiniteNormQuotient A (L.intermediateField S) L.field
        (L.field_le_intermediateField S) := by
  letI : Finite (K.toSubgroup ⧸
      L.field.toSubgroup.subgroupOf K.toSubgroup) := L.finite
  letI : (L.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L.normal
  letI : (L.field.toSubgroup.subgroupOf
      (L.intermediateField S).toSubgroup).Normal :=
    L.subgroupOf_over_intermediate_normal S
  letI : Finite ((L.intermediateField S).toSubgroup ⧸
      L.field.toSubgroup.subgroupOf
        (L.intermediateField S).toSubgroup) :=
    L.extension_over_intermediate_finite S
  exact transferNormNaturalityNormQuotientInclusion A K
    (L.intermediateField S)
    L.field (L.field_le_intermediateField S)
      (L.intermediateField_le_base S)

/-- Representative formula for the inclusion used in the Sylow
reduction ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:128`]
[Yamaguchi2026]). -/
@[simp]
theorem intermediateNormQuotientInclusion_finiteNormClass (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite (K.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.toSubgroup) := L.finite
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        L.field.toSubgroup.subgroupOf
          (L.intermediateField S).toSubgroup) :=
      L.extension_over_intermediate_finite S
    L.intermediateNormQuotientInclusion A S
        (finiteNormClass A K L.field L.below a) =
      finiteNormClass A (L.intermediateField S) L.field
        (L.field_le_intermediateField S)
        (fixedFieldInclusion A K (L.intermediateField S)
          (L.intermediateField_le_base S) a) := by
  letI : Finite (K.toSubgroup ⧸
      L.field.toSubgroup.subgroupOf K.toSubgroup) := L.finite
  letI : (L.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L.normal
  letI : (L.field.toSubgroup.subgroupOf
      (L.intermediateField S).toSubgroup).Normal :=
    L.subgroupOf_over_intermediate_normal S
  letI : Finite ((L.intermediateField S).toSubgroup ⧸
      L.field.toSubgroup.subgroupOf
        (L.intermediateField S).toSubgroup) :=
    L.extension_over_intermediate_finite S
  exact transferNormNaturality_normQuotientInclusion_finiteNormClass A K
    (L.intermediateField S) L.field (L.field_le_intermediateField S)
      (L.intermediateField_le_base S) a

end FiniteGaloisSubextension

/-- The diagram chase used twice in the first reduction: the middle
vertical arrow is surjective when the two outside vertical arrows are
surjective, the top-right arrow is surjective, and the bottom row is
exact ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:663`]
[Yamaguchi2026]). -/
theorem abstractReciprocity_surjective_of_exact_diagram
    {Q₀ Q Q₁ B₀ B B₁ : Type*}
    [AddGroup Q₀] [AddGroup Q] [AddGroup Q₁]
    [AddGroup B₀] [AddGroup B] [AddGroup B₁]
    (iQ : Q₀ →+ Q) (pQ : Q →+ Q₁)
    (iB : B₀ →+ B) (pB : B →+ B₁)
    (r₀ : Q₀ →+ B₀) (r : Q →+ B) (r₁ : Q₁ →+ B₁)
    (hexact : Function.Exact iB pB)
    (hpQ : Function.Surjective pQ)
    (hleft : ∀ q, r (iQ q) = iB (r₀ q))
    (hright : ∀ q, pB (r q) = r₁ (pQ q))
    (hr₀ : Function.Surjective r₀)
    (hr₁ : Function.Surjective r₁) :
    Function.Surjective r := by
  intro b
  obtain ⟨q₁, hq₁⟩ := hr₁ (pB b)
  obtain ⟨q, hq⟩ := hpQ q₁
  have hzero : pB (b - r q) = 0 := by
    calc
      pB (b - r q) = pB b - pB (r q) := map_sub pB b (r q)
      _ = pB b - r₁ (pQ q) := by rw [hright q]
      _ = pB b - r₁ q₁ := by rw [hq]
      _ = pB b - pB b := by rw [hq₁]
      _ = 0 := sub_self _
  obtain ⟨b₀, hb₀⟩ := (hexact (b - r q)).mp hzero
  obtain ⟨q₀, hq₀⟩ := hr₀ b₀
  refine ⟨iQ q₀ + q, ?_⟩
  calc
    r (iQ q₀ + q) = r (iQ q₀) + r q := map_add r _ _
    _ = iB (r₀ q₀) + r q := by rw [hleft q₀]
    _ = iB b₀ + r q := by rw [hq₀]
    _ = (b - r q) + r q := by rw [hb₀]
    _ = b := sub_add_cancel b (r q)

/-- **The diagram chase in the third reduction: if both outside
reciprocity arrows are bijective and the first lower arrow is
injective, then the middle reciprocity arrow is bijective**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:700`]
[Yamaguchi2026]). -/
theorem abstractReciprocity_bijective_of_exact_diagram
    {Q₀ Q Q₁ B₀ B B₁ : Type*}
    [AddGroup Q₀] [AddGroup Q] [AddGroup Q₁]
    [AddGroup B₀] [AddGroup B] [AddGroup B₁]
    (iQ : Q₀ →+ Q) (pQ : Q →+ Q₁)
    (iB : B₀ →+ B) (pB : B →+ B₁)
    (r₀ : Q₀ →+ B₀) (r : Q →+ B) (r₁ : Q₁ →+ B₁)
    (hexactQ : Function.Exact iQ pQ)
    (hexactB : Function.Exact iB pB)
    (hpQ : Function.Surjective pQ)
    (hiB : Function.Injective iB)
    (hleft : ∀ q, r (iQ q) = iB (r₀ q))
    (hright : ∀ q, pB (r q) = r₁ (pQ q))
    (hr₀ : Function.Bijective r₀)
    (hr₁ : Function.Bijective r₁) :
    Function.Bijective r := by
  refine ⟨?_, abstractReciprocity_surjective_of_exact_diagram
    iQ pQ iB pB r₀ r r₁ hexactB hpQ hleft hright hr₀.2 hr₁.2⟩
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hpzero : pB (r q) = 0 := by rw [hq, map_zero]
  have hr₁zero : r₁ (pQ q) = 0 := by
    rw [← hright q]
    exact hpzero
  have hpQzero : pQ q = 0 := by
    apply hr₁.1
    simpa using hr₁zero
  obtain ⟨q₀, hq₀⟩ := (hexactQ q).mp hpQzero
  have hiBzero : iB (r₀ q₀) = 0 := by
    calc
      iB (r₀ q₀) = r (iQ q₀) := (hleft q₀).symm
      _ = r q := by rw [hq₀]
      _ = 0 := hq
  have hr₀zero : r₀ q₀ = 0 := by
    apply hiB
    simpa using hiBzero
  have hq₀zero : q₀ = 0 := by
    apply hr₀.1
    simpa using hr₀zero
  rw [← hq₀, hq₀zero, map_zero]

/-- Every additive homomorphism from a group into an abelian group
kills the commutator subgroup — the automatic inclusion in the kernel
statement of the first reduction ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:744`]
[Yamaguchi2026]). -/
theorem abstractReciprocity_commutator_mem_kernel
    {Q : Type*} {B : Type*} [Group Q] [AddCommGroup B]
    (r : Additive Q →+ B) (q : Q)
    (hq : q ∈ commutator Q) :
    r (Additive.ofMul q) = 0 := by
  let rMul : Q →* Multiplicative B :=
    { toFun := fun x => Multiplicative.ofAdd (r (Additive.ofMul x))
      map_one' := r.map_zero
      map_mul' := r.map_add }
  have hker : q ∈ rMul.ker :=
    Abelianization.commutator_subset_ker rMul hq
  change Multiplicative.ofAdd (r (Additive.ofMul q)) = 1 at hker
  exact Multiplicative.ofAdd.injective (by simpa using hker)

/-- Exact remaining kernel calculation in the first reduction: for the
actual maximal abelian intermediate field, commutativity of the right
square and injectivity of its reciprocity arrow identify the kernel of
the middle arrow with the commutator subgroup ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:762`]
[Yamaguchi2026]). -/
theorem abstractReciprocity_abelianReduction_kernel
    {K : ClosedSubgroup G} {B : Type*} {C : Type*}
    [AddCommGroup B] [AddCommGroup C]
    (L : FiniteGaloisSubextension K)
    (p : B →+ C)
    (r : Additive L.extensionQuotient →+ B)
    (rAb : Additive
        (K.toSubgroup ⧸
          L.abelianIntermediateField.toSubgroup.subgroupOf
            K.toSubgroup) →+ C)
    (hright : ∀ q,
      p (r (Additive.ofMul q)) =
        rAb (Additive.ofMul (L.abelianRestrictionHom q)))
    (hrAb : Function.Injective rAb)
    (q : L.extensionQuotient) :
    r (Additive.ofMul q) = 0 ↔
      q ∈ commutator L.extensionQuotient := by
  constructor
  · intro hq
    have hzero :
        rAb (Additive.ofMul (L.abelianRestrictionHom q)) = 0 := by
      rw [← hright q, hq, map_zero]
    have hresAdd :
        Additive.ofMul (L.abelianRestrictionHom q) = 0 := by
      apply hrAb
      simpa using hzero
    have hres : L.abelianRestrictionHom q = 1 := by
      exact Additive.ofMul.injective (by simpa using hresAdd)
    exact (L.abelianRestrictionHom_eq_one_iff q).1 hres
  · exact abstractReciprocity_commutator_mem_kernel r q

/-- The kernel argument in the second reduction: injectivity of the
reciprocity arrows for a jointly faithful family of cyclic quotients
forces injectivity of the original arrow; all horizontal maps are the
actual restrictions to the intermediate fields cut out by the
coordinate kernels ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:798`]
[Yamaguchi2026]). -/
theorem abstractReciprocity_cyclicFactors_injective
    {K : ClosedSubgroup G} {I : Type*} {C : I → Type*}
    [∀ i, Group (C i)]
    (L : FiniteGaloisSubextension K)
    (f : ∀ i, L.extensionQuotient →* C i)
    (hfaithful : (⨅ i, MonoidHom.ker (f i)) = ⊥)
    {B : Type*} [AddCommGroup B]
    {D : I → Type*} [∀ i, AddCommGroup (D i)]
    (p : ∀ i, B →+ D i)
    (r : Additive L.extensionQuotient →+ B)
    (rFactor : ∀ i,
      Additive
        (K.toSubgroup ⧸
          (L.intermediateField (MonoidHom.ker (f i))).toSubgroup.subgroupOf
          K.toSubgroup) →+ D i)
    (hright : ∀ i q,
      p i (r (Additive.ofMul q)) =
        rFactor i (Additive.ofMul
          (L.upperRestrictionHom (MonoidHom.ker (f i)) q)))
    (hinjective : ∀ i, Function.Injective (rFactor i)) :
    Function.Injective r := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  have hres (i : I) :
      L.upperRestrictionHom (MonoidHom.ker (f i)) q.toMul = 1 := by
    have hrq : r (Additive.ofMul q.toMul) = 0 := by
      simpa using hq
    have hzero : rFactor i (Additive.ofMul
        (L.upperRestrictionHom (MonoidHom.ker (f i)) q.toMul)) = 0 := by
      rw [← hright i q.toMul, hrq, map_zero]
    have hadd : Additive.ofMul
        (L.upperRestrictionHom (MonoidHom.ker (f i)) q.toMul) = 0 := by
      apply hinjective i
      simpa using hzero
    exact Additive.ofMul.injective (by simpa using hadd)
  have hqone : q.toMul = 1 :=
    (L.upperRestrictionHom_jointlyFaithful f hfaithful q.toMul).1 hres
  exact Additive.toMul.injective (by simpa using hqone)

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- **The norm arrow `A_M / N_{L/M} A_L → A_K / N_{L/K} A_L` for the
actual intermediate field cut out by `S ≤ G(L/K)`; no normality of
`M/K` is used** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:42`]
[Yamaguchi2026]). -/
def intermediateNormMap (A : Rep ℤ G) (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    letI : Finite (M.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf M.toSubgroup) :=
      L.extension_over_intermediate_finite S
    letI : Finite (K.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.toSubgroup) :=
      L.finite
    FiniteNormQuotient A M L.field hLM →+
      FiniteNormQuotient A K L.field L.below := by
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  letI : Finite (K.toSubgroup ⧸
      L.field.toSubgroup.subgroupOf K.toSubgroup) := L.finite
  letI : Finite (M.toSubgroup ⧸
      L.field.toSubgroup.subgroupOf M.toSubgroup) :=
    L.extension_over_intermediate_finite S
  letI : Finite (K.toSubgroup ⧸
      M.toSubgroup.subgroupOf K.toSubgroup) :=
    L.intermediateField_finite S
  exact finiteReciprocityNaturalityNormMap A K M L.field L.field
    L.below hLM hMK le_rfl

/-- Representative formula for the nonnormal-intermediate norm arrow
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:67`]
[Yamaguchi2026]). -/
@[simp]
theorem intermediateNormMap_finiteNormClass (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient)
    (a : ambientFixedAddSubgroup A (L.intermediateField S)) :
    letI : Finite (K.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.toSubgroup) := L.finite
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        L.field.toSubgroup.subgroupOf
          (L.intermediateField S).toSubgroup) :=
      L.extension_over_intermediate_finite S
    letI : Finite (K.toSubgroup ⧸
        (L.intermediateField S).toSubgroup.subgroupOf K.toSubgroup) :=
      L.intermediateField_finite S
    L.intermediateNormMap A S
        (finiteNormClass A (L.intermediateField S) L.field
          (L.field_le_intermediateField S) a) =
      finiteNormClass A K L.field L.below
        (relativeNorm A K (L.intermediateField S)
          (L.intermediateField_le_base S) a) := by
  letI : Finite (K.toSubgroup ⧸
      L.field.toSubgroup.subgroupOf K.toSubgroup) := L.finite
  letI : Finite ((L.intermediateField S).toSubgroup ⧸
      L.field.toSubgroup.subgroupOf
        (L.intermediateField S).toSubgroup) :=
    L.extension_over_intermediate_finite S
  letI : Finite (K.toSubgroup ⧸
      (L.intermediateField S).toSubgroup.subgroupOf K.toSubgroup) :=
    L.intermediateField_finite S
  exact finiteReciprocityNaturalityNormMap_finiteNormClass A K
    (L.intermediateField S) L.field L.field L.below
    (L.field_le_intermediateField S) (L.intermediateField_le_base S) le_rfl a

/-- **The exact identity `N_{M/K} ∘ i = [M:K]`, now for an arbitrary
(possibly nonnormal) intermediate field** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:159`]
[Yamaguchi2026]). -/
theorem intermediateNormMap_comp_inclusion (A : Rep ℤ G)
    (L : FiniteGaloisSubextension K) (S : Subgroup L.extensionQuotient) :
    letI : Finite (K.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.toSubgroup) := L.finite
    ∀ q : FiniteNormQuotient A K L.field L.below,
    letI : Finite ((L.intermediateField S).toSubgroup ⧸
        L.field.toSubgroup.subgroupOf
          (L.intermediateField S).toSubgroup) :=
      L.extension_over_intermediate_finite S
    letI : Finite (K.toSubgroup ⧸
        (L.intermediateField S).toSubgroup.subgroupOf K.toSubgroup) :=
      L.intermediateField_finite S
    L.intermediateNormMap A S
        (L.intermediateNormQuotientInclusion A S q) =
      ((L.intermediateFiniteAbstractExtension S).degree : ℕ) • q := by
  letI : Finite (K.toSubgroup ⧸
      L.field.toSubgroup.subgroupOf K.toSubgroup) := L.finite
  intro q
  letI : (L.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L.normal
  letI : (L.field.toSubgroup.subgroupOf
      (L.intermediateField S).toSubgroup).Normal :=
    L.subgroupOf_over_intermediate_normal S
  letI : Finite ((L.intermediateField S).toSubgroup ⧸
      L.field.toSubgroup.subgroupOf
        (L.intermediateField S).toSubgroup) :=
    L.extension_over_intermediate_finite S
  letI : Finite (K.toSubgroup ⧸
      (L.intermediateField S).toSubgroup.subgroupOf K.toSubgroup) :=
    L.intermediateField_finite S
  refine FiniteNormQuotient.induction_on A K L.field L.below q ?_
  intro a
  rw [intermediateNormQuotientInclusion_finiteNormClass,
    intermediateNormMap_finiteNormClass]
  rw [show relativeNorm A K (L.intermediateField S)
      (L.intermediateField_le_base S)
        (fixedFieldInclusion A K (L.intermediateField S)
          (L.intermediateField_le_base S) a) =
      ((L.intermediateFiniteAbstractExtension S).degree : ℕ) • a by
    change relativeNorm A
        (L.intermediateFiniteAbstractExtension S).base
        (L.intermediateFiniteAbstractExtension S).field
        (L.intermediateFiniteAbstractExtension S).below
        (fixedFieldInclusion A
          (L.intermediateFiniteAbstractExtension S).base
          (L.intermediateFiniteAbstractExtension S).field
          (L.intermediateFiniteAbstractExtension S).below a) =
      ((L.intermediateFiniteAbstractExtension S).degree : ℕ) • a
    exact relativeNorm_fixedFieldInclusion A
      (L.intermediateFiniteAbstractExtension S) a]
  exact finiteNormClass_nsmul A K L.field L.below _ a

/-- **In the cyclic case, the lower norm arrow for `L / (L ∩ K̃) / K` is
injective by the order calculation**, specialized to the inertia-image
intermediate field ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:603`]
[Yamaguchi2026]). -/
theorem maximalUnramified_normMap_injective
    (A : Rep ℤ G) (hcf : SatisfiesClassFieldAxiom A)
    (D : DegreeData G) (L : FiniteGaloisSubextension K)
    [Finite ((baseField G).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField G).toSubgroup)]
    [IsCyclic L.extensionQuotient] :
    let S := L.inertiaImage D
    let M := L.intermediateField S
    let hLM := L.field_le_intermediateField S
    let hMK := L.intermediateField_le_base S
    letI : Finite
        (M.toSubgroup ⧸ L.field.toSubgroup.subgroupOf M.toSubgroup) :=
      L.extension_over_intermediate_finite S
    letI : Finite
        (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
      L.intermediateField_finite S
    letI : Finite
        (K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup) :=
      L.finite
    Function.Injective
      (abstractReciprocityNormMap A K M L.field hLM hMK) := by
  dsimp only
  let S := L.inertiaImage D
  let M := L.intermediateField S
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  letI : (L.field.toSubgroup.subgroupOf K.toSubgroup).Normal := L.normal
  letI : (M.toSubgroup.subgroupOf K.toSubgroup).Normal :=
    L.intermediateField_normal S inferInstance
  letI : Finite
      (K.toSubgroup ⧸ L.field.toSubgroup.subgroupOf K.toSubgroup) :=
    L.finite
  letI : Finite
      (M.toSubgroup ⧸ L.field.toSubgroup.subgroupOf M.toSubgroup) :=
    L.extension_over_intermediate_finite S
  letI : Finite
      (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
    L.intermediateField_finite S
  letI : IsCyclic
      (M.toSubgroup ⧸ L.field.toSubgroup.subgroupOf M.toSubgroup) :=
    L.lowerQuotient_isCyclic S
  letI : IsCyclic
      (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
    L.upperQuotient_isCyclic S
  obtain ⟨gKL, hgKL⟩ := IsCyclic.exists_generator
    (α := L.extensionQuotient)
  obtain ⟨gML, hgML⟩ := IsCyclic.exists_generator
    (α := M.toSubgroup ⧸ L.field.toSubgroup.subgroupOf M.toSubgroup)
  obtain ⟨gKM, hgKM⟩ := IsCyclic.exists_generator
    (α := K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup)
  exact abstractReciprocity_cyclicTower_normMap_injective
    A hcf K M L.field hLM hMK gKL hgKL gML hgML gKM hgKM

end FiniteGaloisSubextension

end

end Atlas.Knowledge
