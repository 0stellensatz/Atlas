import Mathlib
import Atlas.Knowledge.AbstractExtension
import Atlas.Knowledge.DegreeData
import Atlas.Knowledge.FiniteCommGroupCyclicFactors
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.IntermediateGaloisCorrespondence

/-!
# reduction Galois arrows

The actual Galois-side arrows the three reductions of the abstract
reciprocity proof run along: for a packaged finite Galois extension
`L / K` and a subgroup `S ≤ G(L/K)`, the injective lower inclusion
`G(L/M) → G(L/K)` and the surjective upper restriction
`G(L/K) → G(M/K)` with their exact row, cyclicity transports, the
maximal abelian intermediate field cut out by the commutator subgroup,
the cyclic intermediate fields of an abelian extension, and the maximal
unramified subextension cut out by the inertia image (#104).

## Main definitions

* `FiniteGaloisSubextension.abelianIntermediateField` — the maximal
  abelian intermediate field, cut out by the commutator subgroup.
* `FiniteGaloisSubextension.maximalUnramifiedSubextension` — the
  maximal unramified subextension `M = L ∩ K̃`, cut out by the inertia
  image.

## Main statements

* `FiniteGaloisSubextension.intermediateGalois_exact` — the actual
  upper row is exact, in additive form; proved.
* `FiniteGaloisSubextension.exists_cyclicIntermediateFields` — a finite
  abelian `G(L/K)` supplies the cyclic intermediate extensions of the
  second reduction; proved.
* `FiniteGaloisSubextension.maximalUnramifiedSubextension_le_of_isUnramified`
  — every unramified intermediate extension lies below the inertia
  image's field in subgroup order; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling, so
`mem_extensionSubgroup_iff` becomes Mathlib's `Subgroup.mem_subgroupOf`
and the correspondence lemma `extensionSubgroup_intermediateField_eq`
is the layer's `subgroupOf_intermediateField_eq`.
`DegreeData.AbstractExtension.mk` is the layer's top-level
`AbstractExtension.mk`, and the jointly faithful cyclic factors come
from the layer's
`Atlas.Knowledge.finiteCommGroup_exists_jointlyFaithful_cyclic_factors`.
The source's `omit [IsTopologicalGroup G] in` marker ports as-is. This
is the source file's `GroupOnly` section whole; its two
`Representation` sections are the next brick.

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

/-- The inclusion `G(L/M) → G(L/K)` for the actual intermediate field,
obtained from `G(L/M) ≃ S` followed by the subgroup inclusion
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:224`]
[Yamaguchi2026]). -/
def lowerInclusionHom (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    (L.intermediateField S).toSubgroup ⧸
        L.field.toSubgroup.subgroupOf (L.intermediateField S).toSubgroup →*
      L.extensionQuotient :=
  S.subtype.comp (L.lowerQuotientEquiv S).toMonoidHom

/-- Representative formula for the actual lower inclusion
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:234`]
[Yamaguchi2026]). -/
@[simp]
theorem lowerInclusionHom_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient)
    (m : (L.intermediateField S).toSubgroup) :
    L.lowerInclusionHom S (QuotientGroup.mk m) =
      (QuotientGroup.mk'
        (L.field.toSubgroup.subgroupOf K.toSubgroup))
          ⟨m.1, L.intermediateField_le_base S m.property⟩ := by
  exact L.lowerQuotientEquiv_mk_coe S m

/-- The lower inclusion is injective ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:244`]
[Yamaguchi2026]). -/
theorem lowerInclusionHom_injective (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) :
    Function.Injective (L.lowerInclusionHom S) := by
  intro x y hxy
  apply (L.lowerQuotientEquiv S).injective
  exact Subtype.ext hxy

/-- Every lower quotient of a cyclic extension is cyclic
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:252`]
[Yamaguchi2026]). -/
theorem lowerQuotient_isCyclic (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [IsCyclic L.extensionQuotient] :
    IsCyclic
      ((L.intermediateField S).toSubgroup ⧸
        L.field.toSubgroup.subgroupOf (L.intermediateField S).toSubgroup) :=
  (L.lowerQuotientEquiv S).isCyclic.2 inferInstance

/-- The actual restriction arrow `G(L/K) → G(M/K)` attached to a normal
subgroup `S ◁ G(L/K)`, expressed through the third-isomorphism
identification ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:263`]
[Yamaguchi2026]). -/
def upperRestrictionHom (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    L.extensionQuotient →*
      K.toSubgroup ⧸ (L.intermediateField S).toSubgroup.subgroupOf
        K.toSubgroup :=
  (L.upperQuotientEquiv S).toMonoidHom.comp (QuotientGroup.mk' S)

/-- Representative formula for the actual upper restriction arrow
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:272`]
[Yamaguchi2026]). -/
@[simp]
theorem upperRestrictionHom_mk (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] (k : K.toSubgroup) :
    L.upperRestrictionHom S
        (QuotientGroup.mk k : L.extensionQuotient) =
      QuotientGroup.mk k := by
  exact L.upperQuotientEquiv_mk_mk S k

/-- Restriction to a normal intermediate field is surjective
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:280`]
[Yamaguchi2026]). -/
theorem upperRestrictionHom_surjective (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    Function.Surjective (L.upperRestrictionHom S) :=
  (L.upperQuotientEquiv S).surjective.comp
    (QuotientGroup.mk'_surjective S)

/-- Every upper quotient of a cyclic extension is cyclic
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:287`]
[Yamaguchi2026]). -/
theorem upperQuotient_isCyclic (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal]
    [IsCyclic L.extensionQuotient] :
    IsCyclic
      (K.toSubgroup ⧸ (L.intermediateField S).toSubgroup.subgroupOf
        K.toSubgroup) := by
  have hsource : IsCyclic (L.extensionQuotient ⧸ S) :=
    isCyclic_of_surjective (QuotientGroup.mk' S)
      (QuotientGroup.mk'_surjective S)
  exact (L.upperQuotientEquiv S).isCyclic.1 hsource

/-- Its kernel is exactly the subgroup defining the intermediate field
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:299`]
[Yamaguchi2026]). -/
theorem upperRestrictionHom_eq_one_iff (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal]
    (q : L.extensionQuotient) :
    L.upperRestrictionHom S q = 1 ↔ q ∈ S := by
  change L.upperQuotientEquiv S
      (L.upperQuotientMk S q) = 1 ↔ q ∈ S
  constructor
  · intro h
    apply (QuotientGroup.eq_one_iff q).1
    change L.upperQuotientMk S q = 1
    apply (L.upperQuotientEquiv S).injective
    exact h.trans ((L.upperQuotientEquiv S).map_one).symm
  · intro h
    have hmk : L.upperQuotientMk S q = 1 := by
      change (QuotientGroup.mk' S) q = 1
      exact (QuotientGroup.eq_one_iff q).2 h
    exact (congrArg (L.upperQuotientEquiv S) hmk).trans
      (L.upperQuotientEquiv S).map_one

/-- **Exactness of the actual upper row for an intermediate field, in
additive form** for direct use with the reciprocity homomorphisms
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:320`]
[Yamaguchi2026]). -/
theorem intermediateGalois_exact (L : FiniteGaloisSubextension K)
    (S : Subgroup L.extensionQuotient) [S.Normal] :
    Function.Exact
      (MonoidHom.toAdditive (L.lowerInclusionHom S))
      (MonoidHom.toAdditive (L.upperRestrictionHom S)) := by
  intro q
  constructor
  · intro hq
    have hres : L.upperRestrictionHom S q.toMul = 1 := by
      exact Additive.ofMul.injective (by simpa using hq)
    have hmem : q.toMul ∈ S :=
      (L.upperRestrictionHom_eq_one_iff S q.toMul).1 hres
    let s : S := ⟨q.toMul, hmem⟩
    refine ⟨Additive.ofMul ((L.lowerQuotientEquiv S).symm s), ?_⟩
    apply Additive.toMul.injective
    change
      ↑(L.lowerQuotientEquiv S ((L.lowerQuotientEquiv S).symm s)) = q.toMul
    exact congrArg Subtype.val
      ((L.lowerQuotientEquiv S).apply_symm_apply s)
  · rintro ⟨x, rfl⟩
    apply Additive.toMul.injective
    change L.upperRestrictionHom S (L.lowerInclusionHom S x.toMul) = 1
    apply (L.upperRestrictionHom_eq_one_iff S _).2
    change (((L.lowerQuotientEquiv S) x.toMul : S) :
      L.extensionQuotient) ∈ S
    exact Subtype.property _

/-- **The maximal abelian intermediate field in the first reduction: the
actual field cut out by the commutator subgroup of `G(L/K)`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:349`]
[Yamaguchi2026]). -/
def abelianIntermediateField (L : FiniteGaloisSubextension K) :
    ClosedSubgroup G :=
  L.intermediateField (commutator L.extensionQuotient)

/-- Normality of the maximal abelian intermediate extension
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:354`]
[Yamaguchi2026]). -/
instance abelianIntermediateField_normalInstance
    (L : FiniteGaloisSubextension K) :
    (L.abelianIntermediateField.toSubgroup.subgroupOf
      K.toSubgroup).Normal := by
  change ((L.intermediateField
    (commutator L.extensionQuotient)).toSubgroup.subgroupOf
      K.toSubgroup).Normal
  exact L.intermediateField_normal
    (commutator L.extensionQuotient) inferInstance

/-- Restriction to the maximal abelian intermediate field
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:367`]
[Yamaguchi2026]). -/
def abelianRestrictionHom (L : FiniteGaloisSubextension K) :
    L.extensionQuotient →*
      K.toSubgroup ⧸ L.abelianIntermediateField.toSubgroup.subgroupOf
        K.toSubgroup :=
  L.upperRestrictionHom (commutator L.extensionQuotient)

/-- The first reduction's exact upper-row assertion: the kernel of
restriction to `L^ab` is the commutator subgroup ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:376`]
[Yamaguchi2026]). -/
theorem abelianRestrictionHom_eq_one_iff
    (L : FiniteGaloisSubextension K) (q : L.extensionQuotient) :
    L.abelianRestrictionHom q = 1 ↔
      q ∈ commutator L.extensionQuotient :=
  L.upperRestrictionHom_eq_one_iff (commutator L.extensionQuotient) q

/-- A jointly faithful family of quotient coordinates gives a jointly
faithful family of actual restriction maps to the corresponding
intermediate fields ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:385`]
[Yamaguchi2026]). -/
theorem upperRestrictionHom_jointlyFaithful
    (L : FiniteGaloisSubextension K)
    {I : Type*} {C : I → Type*} [∀ i, Group (C i)]
    (f : ∀ i, L.extensionQuotient →* C i)
    (hfaithful : (⨅ i, MonoidHom.ker (f i)) = ⊥)
    (q : L.extensionQuotient) :
    (∀ i, L.upperRestrictionHom (MonoidHom.ker (f i)) q = 1) ↔
      q = 1 := by
  constructor
  · intro hq
    have hmem : q ∈ ⨅ i, MonoidHom.ker (f i) := by
      rw [Subgroup.mem_iInf]
      intro i
      exact (L.upperRestrictionHom_eq_one_iff
        (MonoidHom.ker (f i)) q).1 (hq i)
    rw [hfaithful, Subgroup.mem_bot] at hmem
    exact hmem
  · rintro rfl
    intro i
    exact map_one _

/-- For a coordinate homomorphism, the actual restriction map has
exactly the same kernel ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:408`]
[Yamaguchi2026]). -/
theorem upperRestrictionHom_ker_factor
    (L : FiniteGaloisSubextension K) {C : Type*} [Group C]
    (f : L.extensionQuotient →* C) (q : L.extensionQuotient) :
    L.upperRestrictionHom (MonoidHom.ker f) q = 1 ↔ f q = 1 := by
  rw [L.upperRestrictionHom_eq_one_iff (MonoidHom.ker f) q]
  exact MonoidHom.mem_ker

/-- **A finite abelian `G(L/K)` supplies the actual cyclic intermediate
extensions used in the second reduction**: the coordinate kernels have
trivial intersection, and the corresponding groups `G(Mᵢ/K)` are finite
cyclic ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:419`]
[Yamaguchi2026]). -/
theorem exists_cyclicIntermediateFields
    (L : FiniteGaloisSubextension K)
    [IsMulCommutative L.extensionQuotient] :
    ∃ (I : Type 0) (_ : Fintype I) (m : I → ℕ),
      (∀ i, 1 < m i) ∧
      ∃ f : ∀ i,
          L.extensionQuotient →* Multiplicative (ZMod (m i)),
        (∀ i, Function.Surjective (f i)) ∧
        (⨅ i, MonoidHom.ker (f i)) = ⊥ ∧
        (∀ i, IsCyclic
          (K.toSubgroup ⧸
            (L.intermediateField (MonoidHom.ker (f i))).toSubgroup.subgroupOf
            K.toSubgroup)) ∧
        (∀ i, Finite
          (K.toSubgroup ⧸
            (L.intermediateField (MonoidHom.ker (f i))).toSubgroup.subgroupOf
            K.toSubgroup)) := by
  let quotientGroup : Group L.extensionQuotient := inferInstance
  letI : CommGroup L.extensionQuotient :=
    { quotientGroup with
      mul_comm := fun a b => IsMulCommutative.is_comm.comm a b }
  obtain ⟨I, hI, m, hm, f, hf, hfaithful⟩ :=
    finiteCommGroup_exists_jointlyFaithful_cyclic_factors
      L.extensionQuotient
  letI : Fintype I := hI
  refine ⟨I, hI, m, hm, f, hf, hfaithful, ?_, ?_⟩
  · intro i
    let e : L.extensionQuotient ⧸ MonoidHom.ker (f i) ≃*
        Multiplicative (ZMod (m i)) :=
      QuotientGroup.quotientKerEquivOfSurjective (f i) (hf i)
    have hsource : IsCyclic
        (L.extensionQuotient ⧸ MonoidHom.ker (f i)) :=
      e.isCyclic.2 inferInstance
    exact (L.upperQuotientEquiv (MonoidHom.ker (f i))).isCyclic.1 hsource
  · intro i
    exact L.intermediateField_finite (MonoidHom.ker (f i))

/-! ## The maximal unramified subextension in the third reduction -/

/-- The inertia subgroup of `G(L/K)`: the image of `I_K` in the actual
finite quotient; its fixed field is `L ∩ K̃` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:459`]
[Yamaguchi2026]). -/
def inertiaImage (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    Subgroup L.extensionQuotient :=
  (D.fieldInertiaWithin K).map
    (QuotientGroup.mk' (L.field.toSubgroup.subgroupOf K.toSubgroup))

omit [IsTopologicalGroup G] in
/-- The inertia image is normal, since it is the image of the normal
inertia subgroup under a surjective quotient map ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:467`]
[Yamaguchi2026]). -/
theorem inertiaImage_normal (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : (L.inertiaImage D).Normal := by
  exact (inferInstance : (D.fieldInertiaWithin K).Normal).map
    (QuotientGroup.mk' (L.field.toSubgroup.subgroupOf K.toSubgroup))
    (QuotientGroup.mk'_surjective
      (L.field.toSubgroup.subgroupOf K.toSubgroup))

/-- The inertia image in a finite Galois quotient is normal
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:475`]
[Yamaguchi2026]). -/
instance inertiaImage_normalInstance (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : (L.inertiaImage D).Normal :=
  L.inertiaImage_normal D

/-- **The actual maximal unramified subextension `M = L ∩ K̃`**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:480`]
[Yamaguchi2026]). -/
def maximalUnramifiedSubextension (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : ClosedSubgroup G :=
  L.intermediateField (L.inertiaImage D)

/-- `M/K` as an actual finite Galois extension ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:485`]
[Yamaguchi2026]). -/
def maximalUnramifiedFiniteGalois (D : DegreeData G)
    (L : FiniteGaloisSubextension K) : FiniteGaloisSubextension K :=
  L.intermediateFiniteGalois (L.inertiaImage D)
    (L.inertiaImage_normal D)

/-- The constructed `M/K` is unramified ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:491`]
[Yamaguchi2026]). -/
theorem maximalUnramifiedSubextension_isUnramified
    (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    (AbstractExtension.mk (L.maximalUnramifiedSubextension D) K
      (L.intermediateField_le_base (L.inertiaImage D))).IsUnramified D := by
  change (AbstractExtension.mk
    (L.intermediateField (L.inertiaImage D)) K
    (L.intermediateField_le_base (L.inertiaImage D))).IsUnramified D
  rw [(AbstractExtension.mk
    (L.intermediateField (L.inertiaImage D)) K
    (L.intermediateField_le_base
      (L.inertiaImage D))).isUnramified_iff_inertia_le D]
  intro x hx
  let k : K.toSubgroup := ⟨x, hx.1⟩
  have hkI : k ∈ D.fieldInertiaWithin K := by
    exact hx.2
  have hkS :
      (QuotientGroup.mk'
        (L.field.toSubgroup.subgroupOf K.toSubgroup)) k ∈
          L.inertiaImage D :=
    ⟨k, hkI, rfl⟩
  have hkP : k ∈ L.intermediateSubgroup (L.inertiaImage D) := by
    change (QuotientGroup.mk'
      (L.field.toSubgroup.subgroupOf K.toSubgroup)) k ∈ L.inertiaImage D
    exact hkS
  exact ⟨k, hkP, rfl⟩

/-- The complementary extension `L/M` is totally ramified, i.e.
`f_{L/M}=1` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:517`]
[Yamaguchi2026]). -/
theorem maximalUnramifiedSubextension_isTotallyRamified
    (D : DegreeData G) (L : FiniteGaloisSubextension K) :
    (AbstractExtension.mk L.field
      (L.maximalUnramifiedSubextension D)
      (L.field_le_intermediateField
        (L.inertiaImage D))).IsTotallyRamified D := by
  let S := L.inertiaImage D
  let M := L.maximalUnramifiedSubextension D
  let hLM := L.field_le_intermediateField S
  let hMK := L.intermediateField_le_base S
  change (AbstractExtension.mk L.field
    (L.intermediateField (L.inertiaImage D)) hLM).IsTotallyRamified D
  rw [(AbstractExtension.mk L.field
    (L.intermediateField
      (L.inertiaImage D)) hLM).isTotallyRamified_iff_image_le D]
  rintro z ⟨x, hxM, rfl⟩
  let xK : K.toSubgroup := ⟨x, hMK hxM⟩
  have hxP : xK ∈ L.intermediateSubgroup S := by
    rw [← L.subgroupOf_intermediateField_eq S]
    exact Subgroup.mem_subgroupOf.2 hxM
  change (QuotientGroup.mk'
    (L.field.toSubgroup.subgroupOf K.toSubgroup)) xK ∈
      (D.fieldInertiaWithin K).map
        (QuotientGroup.mk'
          (L.field.toSubgroup.subgroupOf K.toSubgroup)) at hxP
  obtain ⟨i, hiI, hi⟩ := hxP
  have hiH : i⁻¹ * xK ∈ L.field.toSubgroup.subgroupOf K.toSubgroup :=
    QuotientGroup.eq.mp hi
  have hiL : i.1⁻¹ * x ∈ L.field.toSubgroup := by
    exact Subgroup.mem_subgroupOf.1 hiH
  refine ⟨i.1⁻¹ * x, hiL, ?_⟩
  have hdegree : D.degree i.1 = 1 :=
    (D.mem_fieldInertiaWithin_iff K i).1 hiI
  simp [hdegree]

/-- **Maximality: every unramified intermediate extension of `L/K` is
contained in the field cut out by the inertia image** — in subgroup
order, the displayed inclusion ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Reduction.lean:553`]
[Yamaguchi2026]). -/
theorem maximalUnramifiedSubextension_le_of_isUnramified
    (D : DegreeData G) (L : FiniteGaloisSubextension K)
    (N : ClosedSubgroup G)
    (hLN : L.field.toSubgroup ≤ N.toSubgroup)
    (hNK : N.toSubgroup ≤ K.toSubgroup)
    (hNunramified : (AbstractExtension.mk N K hNK).IsUnramified D) :
    (L.maximalUnramifiedSubextension D).toSubgroup ≤ N.toSubgroup := by
  change (L.intermediateField (L.inertiaImage D)).toSubgroup ≤
    N.toSubgroup
  intro x hxM
  obtain ⟨k, hkP, rfl⟩ := hxM
  change (QuotientGroup.mk'
    (L.field.toSubgroup.subgroupOf K.toSubgroup)) k ∈
      (D.fieldInertiaWithin K).map
        (QuotientGroup.mk'
          (L.field.toSubgroup.subgroupOf K.toSubgroup)) at hkP
  obtain ⟨i, hiI, hi⟩ := hkP
  have hiH : i⁻¹ * k ∈ L.field.toSubgroup.subgroupOf K.toSubgroup :=
    QuotientGroup.eq.mp hi
  have hikL : i.1⁻¹ * k.1 ∈ L.field.toSubgroup :=
    Subgroup.mem_subgroupOf.1 hiH
  have hiDegree : D.degree i.1 = 1 :=
    (D.mem_fieldInertiaWithin_iff K i).1 hiI
  have hiKN : i.1 ∈ N.toSubgroup := by
    apply ((AbstractExtension.mk N K hNK).isUnramified_iff_inertia_le D).1
      hNunramified
    exact ⟨i.property, hiDegree⟩
  have hikN : i.1⁻¹ * k.1 ∈ N.toSubgroup := hLN hikL
  have hmul : i.1 * (i.1⁻¹ * k.1) ∈ N.toSubgroup :=
    N.toSubgroup.mul_mem hiKN hikN
  simpa [mul_assoc] using hmul

end FiniteGaloisSubextension

end

end Atlas.Knowledge
