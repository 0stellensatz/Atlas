import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FiniteTower
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.RelativeNormLaws

/-!
# norm topology

The norm topology on the fixed subgroup `A_K` of a class formation: the
finite Galois norm subgroups form an additive-group filter basis, and
the topology they generate has a subgroup open exactly when it contains
one of them; every norm subgroup is open, the topology is Hausdorff
exactly when the universal norms vanish, and once every norm quotient
is finite an open subgroup is the same as a closed one of finite index.
The first brick of the abstract half of the finite local existence
theorem — the vocabulary in which the class-field candidate and the
abstract classification of finite abelian subextensions are stated
(#104).

## Main definitions

* `FiniteGaloisSubextension.normSubgroup` — the norm subgroup of a
  packaged finite Galois subextension.
* `normFilterBasis`, `normTopology` — the filter basis of norm
  subgroups and the topology it generates.
* `IsNormOpen`, `IsNormClosed`, `IsNormHausdorff` — openness,
  closedness, and Hausdorffness in the norm topology.
* `universalNormSubgroup` — the intersection of all norm subgroups.

## Main statements

* `FiniteGaloisSubextension.finiteNormSubgroup_compositum_le_left` /
  `_right` — the norm subgroup of a compositum lies in each factor's;
  proved.
* `normTopology_addSubgroup_isOpen_iff` — a subgroup is norm-open
  exactly when it contains a norm subgroup; proved.
* `normTopology_hausdorff` — Hausdorff exactly when the universal norms
  are trivial; proved.
* `normTopology_open_iff_closed_finiteIndex_of_finite_normQuotients` —
  with finite norm quotients, open is closed of finite index; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
the finite tower the layer's top-level `FiniteTower` with its
`norm_trans_apply`, and the ambient group `Type u` with the
class-formation stock. The two compositum norm bounds live in the
source's `FiniteGaloisSubextension.lean` (its `:417`, `:457`), past
where the layer's `Atlas.Knowledge.FiniteGaloisSubextension` stops;
they sit here, in that item's namespace, because they consume
`finiteNormSubgroup` and the norm topology is their first consumer. The
topology is carried on the fixed subgroup itself, as a term
`normTopology A K` supplied explicitly to `IsOpen`, `IsClosed`, and
`T2Space` — the source's `WithNormTopology` carrier, a `WithTopology`
wrapper that exists so that no instance on the underlying group is
mutated, is not ported: the layer never installs the norm topology as
an instance, so the wrapper would wrap nothing, and its two continuity
predicates `IsContinuousFromNormTopology` and `IsNormContinuous`
(consumed by the source's `NormContinuity.lean` and
`ValuationContinuity.lean`) are the continuity-fork material the arc
strips. Hausdorffness is Mathlib's filter-basis criterion
`AddGroupFilterBasis.t2Space_iff` with the topology named explicitly,
where the source transports through the wrapper's homeomorphism. The
two class-typed definitions carry `@[implicit_reducible]` as the
source's do, which the reducibility linter requires. Everything else
ports token-for-token; the file is the source's
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean` less the
wrapper and the continuity predicates.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The norm subgroup of a compositum is contained in the norm subgroup
of its first factor ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:417`]
[Yamaguchi2026]). -/
theorem finiteNormSubgroup_compositum_le_left (A : Rep ℤ G)
    (L₁ L₂ : FiniteGaloisSubextension K) :
    letI := (L₁.compositum L₂).finite
    letI := L₁.finite
    finiteNormSubgroup A K (L₁.compositum L₂).field (L₁.compositum L₂).below ≤
      finiteNormSubgroup A K L₁.field L₁.below := by
  let P := L₁.compositum L₂
  let hPL₁ := L₁.compositum_le_left L₂
  letI : Finite (K.toSubgroup ⧸ P.field.toSubgroup.subgroupOf K.toSubgroup) := P.finite
  letI : Finite (K.toSubgroup ⧸ L₁.field.toSubgroup.subgroupOf K.toSubgroup) := L₁.finite
  have hPKindex : P.field.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact Subgroup.index_ne_zero_of_finite
  have hPLindex : P.field.toSubgroup.relIndex L₁.field.toSubgroup ≠ 0 := by
    intro hzero
    have hmul := Subgroup.relIndex_mul_relIndex
      P.field.toSubgroup L₁.field.toSubgroup K.toSubgroup hPL₁ L₁.below
    rw [hzero, zero_mul] at hmul
    exact hPKindex hmul.symm
  letI hPLfinite :
      Finite (L₁.field.toSubgroup ⧸ P.field.toSubgroup.subgroupOf L₁.field.toSubgroup) := by
    apply Nat.finite_of_card_ne_zero
    change (P.field.toSubgroup.subgroupOf L₁.field.toSubgroup).index ≠ 0
    simpa [Subgroup.relIndex] using hPLindex
  let T : FiniteTower G :=
    { top := P.field
      middle := L₁.field
      base := K
      top_le_middle := hPL₁
      middle_le_base := L₁.below
      finiteTopQuotient := hPLfinite
      finiteBaseQuotient := L₁.finite }
  rintro x ⟨a, rfl⟩
  refine ⟨relativeNorm A L₁.field P.field hPL₁ a, ?_⟩
  exact T.norm_trans_apply A a

/-- The symmetric norm-subgroup containment for the second factor
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:457`]
[Yamaguchi2026]). -/
theorem finiteNormSubgroup_compositum_le_right (A : Rep ℤ G)
    (L₁ L₂ : FiniteGaloisSubextension K) :
    letI := (L₁.compositum L₂).finite
    letI := L₂.finite
    finiteNormSubgroup A K (L₁.compositum L₂).field (L₁.compositum L₂).below ≤
      finiteNormSubgroup A K L₂.field L₂.below := by
  simpa [compositum, inf_comm] using finiteNormSubgroup_compositum_le_left A L₂ L₁

/-- **The norm subgroup of a packaged finite Galois subextension**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:31`]
[Yamaguchi2026]). -/
def normSubgroup (A : Rep ℤ G) (L : FiniteGaloisSubextension K) :
    AddSubgroup (ambientFixedAddSubgroup A K) := by
  letI := L.finite
  exact finiteNormSubgroup A K L.field L.below

/-- The norm subgroup of a compositum lies in that of its first factor
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:37`]
[Yamaguchi2026]). -/
theorem normSubgroup_compositum_le_left (A : Rep ℤ G) (L₁ L₂ : FiniteGaloisSubextension K) :
    normSubgroup A (L₁.compositum L₂) ≤ normSubgroup A L₁ := by
  simpa [normSubgroup] using finiteNormSubgroup_compositum_le_left A L₁ L₂

/-- The norm subgroup of a compositum lies in that of its second factor
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:44`]
[Yamaguchi2026]). -/
theorem normSubgroup_compositum_le_right (A : Rep ℤ G) (L₁ L₂ : FiniteGaloisSubextension K) :
    normSubgroup A (L₁.compositum L₂) ≤ normSubgroup A L₂ := by
  simpa [normSubgroup] using finiteNormSubgroup_compositum_le_right A L₁ L₂

end FiniteGaloisSubextension

open FiniteGaloisSubextension

/-- **The filter basis of finite Galois norm subgroups** on the fixed
subgroup ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:57`]
[Yamaguchi2026]). -/
@[implicit_reducible]
def normFilterBasis (A : Rep ℤ G) (K : ClosedSubgroup G) :
    AddGroupFilterBasis (ambientFixedAddSubgroup A K) :=
  addGroupFilterBasisOfComm
    {U | ∃ L : FiniteGaloisSubextension K,
      U = (normSubgroup A L : Set (ambientFixedAddSubgroup A K))}
    ⟨(normSubgroup A (FiniteGaloisSubextension.refl K) : Set (ambientFixedAddSubgroup A K)),
      FiniteGaloisSubextension.refl K, rfl⟩
    (by
      rintro U V ⟨L₁, rfl⟩ ⟨L₂, rfl⟩
      refine ⟨(normSubgroup A (L₁.compositum L₂) : Set (ambientFixedAddSubgroup A K)),
        ⟨L₁.compositum L₂, rfl⟩, ?_⟩
      intro x hx
      exact ⟨normSubgroup_compositum_le_left A L₁ L₂ hx,
        normSubgroup_compositum_le_right A L₁ L₂ hx⟩)
    (by
      rintro _ ⟨L, rfl⟩
      exact (normSubgroup A L).zero_mem)
    (by
      rintro _ ⟨L, rfl⟩
      refine ⟨(normSubgroup A L : Set (ambientFixedAddSubgroup A K)), ⟨L, rfl⟩, ?_⟩
      rintro x ⟨a, ha, b, hb, rfl⟩
      exact (normSubgroup A L).add_mem ha hb)
    (by
      rintro _ ⟨L, rfl⟩
      refine ⟨(normSubgroup A L : Set (ambientFixedAddSubgroup A K)), ⟨L, rfl⟩, ?_⟩
      intro x hx
      exact (normSubgroup A L).neg_mem hx)

/-- **The norm topology**: the norm subgroups form a basis at zero
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:92`]
[Yamaguchi2026]). -/
@[implicit_reducible]
def normTopology (A : Rep ℤ G) (K : ClosedSubgroup G) :
    TopologicalSpace (ambientFixedAddSubgroup A K) :=
  (normFilterBasis A K).topology

/-- Openness in the norm topology ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:129`]
[Yamaguchi2026]). -/
def IsNormOpen (A : Rep ℤ G) (K : ClosedSubgroup G)
    (s : Set (ambientFixedAddSubgroup A K)) : Prop :=
  @IsOpen (ambientFixedAddSubgroup A K) (normTopology A K) s

/-- Closedness in the norm topology ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:135`]
[Yamaguchi2026]). -/
def IsNormClosed (A : Rep ℤ G) (K : ClosedSubgroup G)
    (s : Set (ambientFixedAddSubgroup A K)) : Prop :=
  @IsClosed (ambientFixedAddSubgroup A K) (normTopology A K) s

/-- Hausdorffness of the norm topology ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:140`]
[Yamaguchi2026]). -/
def IsNormHausdorff (A : Rep ℤ G) (K : ClosedSubgroup G) : Prop :=
  @T2Space (ambientFixedAddSubgroup A K) (normTopology A K)

/-- A set belongs to the defining filter basis exactly when it is a
finite Galois norm subgroup ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:183`]
[Yamaguchi2026]). -/
@[simp]
theorem mem_normFilterBasis_iff (A : Rep ℤ G) (K : ClosedSubgroup G)
    (U : Set (ambientFixedAddSubgroup A K)) :
    U ∈ normFilterBasis A K ↔
      ∃ L : FiniteGaloisSubextension K,
        U = (normSubgroup A L : Set (ambientFixedAddSubgroup A K)) :=
  Iff.rfl

/-- **A subgroup is norm-open exactly when it contains a finite Galois
norm subgroup** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:193`]
[Yamaguchi2026]). -/
theorem normTopology_addSubgroup_isOpen_iff (A : Rep ℤ G) (K : ClosedSubgroup G)
    (H : AddSubgroup (ambientFixedAddSubgroup A K)) :
    IsNormOpen A K H ↔ ∃ L : FiniteGaloisSubextension K, normSubgroup A L ≤ H := by
  letI : TopologicalSpace (ambientFixedAddSubgroup A K) := normTopology A K
  letI : IsTopologicalAddGroup (ambientFixedAddSubgroup A K) :=
    (normFilterBasis A K).isTopologicalAddGroup
  constructor
  · intro hH
    have hnh : (H : Set (ambientFixedAddSubgroup A K)) ∈ nhds 0 := hH.mem_nhds H.zero_mem
    rcases (normFilterBasis A K).nhds_zero_hasBasis.mem_iff.mp hnh with ⟨U, hU, hUH⟩
    rcases hU with ⟨L, rfl⟩
    exact ⟨L, hUH⟩
  · rintro ⟨L, hLH⟩
    apply H.isOpen_of_mem_nhds
    exact Filter.mem_of_superset ((normFilterBasis A K).mem_nhds_zero ⟨L, rfl⟩) hLH

/-- Every defining norm subgroup is open ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:216`]
[Yamaguchi2026]). -/
theorem normSubgroup_isOpen (A : Rep ℤ G) (K : ClosedSubgroup G)
    (L : FiniteGaloisSubextension K) : IsNormOpen A K (normSubgroup A L) := by
  rw [normTopology_addSubgroup_isOpen_iff]
  exact ⟨L, le_rfl⟩

/-- **The universal norm subgroup**: the intersection of all finite
Galois norm subgroups ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:224`]
[Yamaguchi2026]). -/
def universalNormSubgroup (A : Rep ℤ G) (K : ClosedSubgroup G) :
    AddSubgroup (ambientFixedAddSubgroup A K) :=
  ⨅ L : FiniteGaloisSubextension K, normSubgroup A L

/-- Membership in the universal norm subgroup is membership in every
norm subgroup ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:233`]
[Yamaguchi2026]). -/
@[simp]
theorem mem_universalNormSubgroup_iff (A : Rep ℤ G) (K : ClosedSubgroup G)
    (a : ambientFixedAddSubgroup A K) :
    a ∈ universalNormSubgroup A K ↔ ∀ L : FiniteGaloisSubextension K, a ∈ normSubgroup A L := by
  simp [universalNormSubgroup]

/-- **The norm topology is Hausdorff exactly when the universal norms
are trivial** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:270`]
[Yamaguchi2026]). -/
theorem normTopology_hausdorff (A : Rep ℤ G) (K : ClosedSubgroup G) :
    IsNormHausdorff A K ↔ universalNormSubgroup A K = ⊥ := by
  let B := normFilterBasis A K
  have hsInter :
      ⋂₀ B.sets = (universalNormSubgroup A K : Set (ambientFixedAddSubgroup A K)) := by
    ext a
    constructor
    · intro ha
      change a ∈ universalNormSubgroup A K
      rw [mem_universalNormSubgroup_iff]
      intro L
      exact ha (normSubgroup A L) ⟨L, rfl⟩
    · intro ha U hU
      rcases hU with ⟨L, rfl⟩
      exact (mem_universalNormSubgroup_iff A K a).1 ha L
  change @T2Space _ (normTopology A K) ↔ _
  rw [B.t2Space_iff (t := normTopology A K) rfl, hsInter]
  constructor
  · intro h
    apply SetLike.coe_injective
    simpa using h
  · intro h
    have := congrArg
      (fun S : AddSubgroup (ambientFixedAddSubgroup A K) =>
        (S : Set (ambientFixedAddSubgroup A K))) h
    simpa using this

/-- **With finite norm quotients, a norm-open subgroup is a norm-closed
subgroup of finite index, and conversely** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/NormTopology.lean:290`]
[Yamaguchi2026]). -/
theorem normTopology_open_iff_closed_finiteIndex_of_finite_normQuotients (A : Rep ℤ G)
    (K : ClosedSubgroup G)
    (hfinite : ∀ L : FiniteGaloisSubextension K,
      Finite (ambientFixedAddSubgroup A K ⧸ normSubgroup A L))
    (H : AddSubgroup (ambientFixedAddSubgroup A K)) :
    IsNormOpen A K H ↔ IsNormClosed A K H ∧ Finite (ambientFixedAddSubgroup A K ⧸ H) := by
  letI : TopologicalSpace (ambientFixedAddSubgroup A K) := normTopology A K
  letI : IsTopologicalAddGroup (ambientFixedAddSubgroup A K) :=
    (normFilterBasis A K).isTopologicalAddGroup
  constructor
  · intro hH
    refine ⟨H.isClosed_of_isOpen hH, ?_⟩
    obtain ⟨L, hLH⟩ := (normTopology_addSubgroup_isOpen_iff A K H).1 hH
    letI : Finite (ambientFixedAddSubgroup A K ⧸ normSubgroup A L) := hfinite L
    letI : (normSubgroup A L).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
    letI : H.FiniteIndex := AddSubgroup.finiteIndex_of_le hLH
    exact AddSubgroup.finite_quotient_of_finiteIndex
  · rintro ⟨hclosed, hfin⟩
    letI : Finite (ambientFixedAddSubgroup A K ⧸ H) := hfin
    letI : H.FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
    exact H.isOpen_of_isClosed_of_finiteIndex hclosed

end

end Atlas.Knowledge
