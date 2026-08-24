import Mathlib
import Atlas.Knowledge.ExistsValuativeExtension
import Atlas.Knowledge.UpperRamificationGroup
import Atlas.Knowledge.FilteredProfiniteGroup

/-!
# ramification filtration of an infinite Galois group

The upper-numbering ramification filtration of an arbitrary—finite or infinite—Galois
extension `F` of a local field `K`, by passage to the inverse limit: `G (v)` is the set of
automorphisms whose restriction to every finite Galois subextension `E` lies in the
`v`th upper-numbering group of `E` over `K`, which is the subgroup-of-the-limit reading of
`G (v) = lim (G/N) (v)`. The upper numbering is what makes this limit exist—the finite levels
are compatible under quotients, `Atlas.Knowledge.map_upperRamificationGroup`—and the resulting
family is the real-indexed filtration by closed normal subgroups that both anabelian source
papers equip their Galois groups with. The bundling as an
`Atlas.Knowledge.FilteredProfiniteGroup` is `filteredGaloisGroup`, and the bottom of the
filtration is described in `Atlas.Knowledge.WildInertiaSubgroup`.

## Main definitions

* `ramificationFiltration` — `G (v) ≤ F ≃ₐ[K] F` for `v : ℝ`, the inverse-limit filtration.
* `filteredGaloisGroup` — the Galois group of `F` over `K` as a filtered profinite group, the
  filtration restricted to indices in `ℝ≥0`.

## Main statements

* `mem_ramificationFiltration_iff` — membership unwound to the finite levels.
* `ramificationFiltration_antitone` — the family decreases.
* `isClosed_ramificationFiltration` — each `G (v)` is closed in the Krull topology.
* `map_ramificationFiltration` — the filtration restricts onto each finite level.
* `ramificationFiltration_eq_upperRamificationGroup` — for finite `F` the limit recovers the
  finite object.

## Implementation notes

The index `E` of the defining infimum runs over `FiniteGaloisIntermediateField K F`, which
carries the `FiniteDimensional` and `IsGalois` instances every finite-level statement needs;
each level is the comap along `AlgEquiv.restrictNormalHom`, and closedness is the continuity
of that restriction against the discreteness of a finite Galois group. Antitonicity,
normality, and closedness hold with no hypotheses on `F` beyond `Field F` and `Algebra K F`:
they are inherited levelwise, and an empty or degenerate index type only makes the infimum
larger. The finite-level statements need the local-field hypotheses: an intermediate field
carries no valuative structure of its own, so each application of
`Atlas.Knowledge.map_upperRamificationGroup` first equips it through
`Atlas.Knowledge.exists_valuativeExtension`—that is the whole content of
`ramificationFiltration_eq_upperRamificationGroup`, one Herbrand compatibility per level for
one inclusion and injectivity of restriction to `⊤` for the other. The surjectivity of the
limit onto each level, `map_ramificationFiltration`, is the content of the source's
inverse-limit construction, and is where compactness enters: finite-level surjectivity feeds
a directed family of nonempty closed constraint sets in the compact Galois group, whose
common point restricts as prescribed at the given level and lands in the filtration through
the push-down `restrictNormalHom_mem_upperRamificationGroup` at every other.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic
  local fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (F : Type*) [Field F] [Algebra K F]

/-- The **ramification filtration** of the Galois group of an arbitrary Galois extension `F`
of `K`, in the upper numbering: `G (v)` is the inverse limit of the `v`th upper-numbering
groups of the finite Galois subextensions, read as the subgroup of automorphisms restricting
into the `v`th group at every finite level
([Serre 1979, Chap. IV, §3, Rem. 1, p.75][Serre1979];
[Hyeon 2025, §2, (3), p.7][Hyeon2025]). -/
noncomputable def ramificationFiltration (v : ℝ) : Subgroup (F ≃ₐ[K] F) :=
  ⨅ E : FiniteGaloisIntermediateField K F,
    (upperRamificationGroup K E v).comap (AlgEquiv.restrictNormalHom E)

/-- Membership in the ramification filtration, unwound: `g ∈ G (v)` iff the restriction of
`g` to every finite Galois subextension `E` lies in the `v`th upper-numbering ramification
group of `E` over `K` ([Serre 1979, Chap. IV, §3, Rem. 1, p.75][Serre1979]). -/
theorem mem_ramificationFiltration_iff {v : ℝ} {g : F ≃ₐ[K] F} :
    g ∈ ramificationFiltration K F v ↔
      ∀ E : FiniteGaloisIntermediateField K F,
        AlgEquiv.restrictNormalHom E g ∈ upperRamificationGroup K E v := by
  simp [ramificationFiltration, Subgroup.mem_iInf, Subgroup.mem_comap]

/-- The ramification filtration decreases in `v`
([Hyeon 2025, §2, p.7][Hyeon2025]). -/
theorem ramificationFiltration_antitone : Antitone (ramificationFiltration K F) :=
  fun _ _ h =>
    iInf_mono fun E => Subgroup.comap_mono (upperRamificationGroup_antitone K E h)

instance ramificationFiltration_normal (v : ℝ) : (ramificationFiltration K F v).Normal := by
  constructor
  intro n hn g
  rw [mem_ramificationFiltration_iff] at hn ⊢
  intro E
  rw [map_mul, map_mul, map_inv]
  exact Subgroup.Normal.conj_mem inferInstance _ (hn E) _

/-- Each step of the ramification filtration is closed in the Krull topology: it is an
intersection of preimages of subgroups of the discrete finite quotients under the continuous
restriction maps ([Hyeon 2025, §2, p.7][Hyeon2025]). -/
theorem isClosed_ramificationFiltration (v : ℝ) :
    IsClosed (ramificationFiltration K F v : Set (F ≃ₐ[K] F)) := by
  have h : (ramificationFiltration K F v : Set (F ≃ₐ[K] F)) =
      ⋂ E : FiniteGaloisIntermediateField K F,
        AlgEquiv.restrictNormalHom E ⁻¹' (upperRamificationGroup K E v : Set _) := by
    ext g
    simp [mem_ramificationFiltration_iff, Set.mem_iInter]
  rw [h]
  exact isClosed_iInter fun E =>
    (isClosed_discrete _).preimage
      (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField)

/-- The Galois group of a Galois extension `F` of `K` as a **filtered profinite group**: the
profinite group of `InfiniteGalois.profiniteGalGrp` carrying the ramification filtration in
the upper numbering, restricted to indices in `ℝ≥0`
([Hyeon 2025, §2, pp.6–7][Hyeon2025]). -/
noncomputable def filteredGaloisGroup [IsGalois K F] : FilteredProfiniteGroup where
  toProfiniteGrp := InfiniteGalois.profiniteGalGrp K F
  filt v := ramificationFiltration K F (v : ℝ)
  isClosed_filt v := isClosed_ramificationFiltration K F (v : ℝ)
  normal_filt v := ramificationFiltration_normal K F (v : ℝ)
  antitone_filt _ _ h := ramificationFiltration_antitone K F (by exact_mod_cast h)

/-- Between two finite Galois subextensions `E₁ ≤ E₂`, restriction carries the `v`th
upper-numbering group of `E₂` into that of `E₁`—Herbrand compatibility
`Atlas.Knowledge.map_upperRamificationGroup`, after equipping the abstract middle field
through `Atlas.Knowledge.exists_valuativeExtension`
([Serre 1979, Chap. IV, §3, Prop. 14, p.74][Serre1979]). -/
theorem restrictNormalHom_mem_upperRamificationGroup [TopologicalSpace K]
    [IsMixedCharLocalField K] [IsGalois K F]
    (E₁ E₂ : FiniteGaloisIntermediateField K F) (hle : E₁ ≤ E₂) {v : ℝ} (x : F ≃ₐ[K] F)
    (hx : AlgEquiv.restrictNormalHom E₂ x ∈ upperRamificationGroup K E₂ v) :
    AlgEquiv.restrictNormalHom E₁ x ∈ upperRamificationGroup K E₁ v := by
  letI : Algebra E₁ E₂ := RingHom.toAlgebra (Subsemiring.inclusion hle)
  haveI : IsScalarTower K E₁ E₂ := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : IsScalarTower E₁ E₂ F := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  haveI : FiniteDimensional E₁ E₂ := Module.Finite.right K E₁ E₂
  obtain ⟨vE₁, hvE₁⟩ := exists_valuativeExtension K E₁
  letI := vE₁
  haveI := hvE₁
  rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E₁ E₂ x,
    ← map_upperRamificationGroup K E₂ E₁ v]
  exact ⟨_, hx, rfl⟩

/-- The lifting step of the inverse-limit argument: an element of the `v`th upper-numbering
group at a finite level `E` is the restriction of an element of the `v`th step of the
infinite filtration. Finite-level surjectivity feeds a directed family of nonempty closed
subsets of the compact Galois group, and compactness intersects them. -/
private theorem exists_ramificationFiltration_restrictNormalHom_eq [TopologicalSpace K]
    [IsMixedCharLocalField K] [IsGalois K F]
    (E : FiniteGaloisIntermediateField K F) {v : ℝ} {y : E ≃ₐ[K] E}
    (hy : y ∈ upperRamificationGroup K E v) :
    ∃ x ∈ ramificationFiltration K F v, AlgEquiv.restrictNormalHom E x = y := by
  classical
  let T : {E' : FiniteGaloisIntermediateField K F // E ≤ E'} → Set (F ≃ₐ[K] F) := fun E' =>
    AlgEquiv.restrictNormalHom E'.1 ⁻¹' (upperRamificationGroup K E'.1 v : Set _) ∩
      AlgEquiv.restrictNormalHom E ⁻¹' {y}
  haveI : Nonempty {E' : FiniteGaloisIntermediateField K F // E ≤ E'} := ⟨⟨E, le_rfl⟩⟩
  have hne : ∀ E' : {E' : FiniteGaloisIntermediateField K F // E ≤ E'}, (T E').Nonempty := by
    rintro ⟨E', hle⟩
    letI : Algebra E E' := RingHom.toAlgebra (Subsemiring.inclusion hle)
    haveI : IsScalarTower K E E' := IsScalarTower.of_algebraMap_eq (congrFun rfl)
    haveI : IsScalarTower E E' F := IsScalarTower.of_algebraMap_eq (congrFun rfl)
    haveI : FiniteDimensional E E' := Module.Finite.right K E E'
    obtain ⟨vE, hvE⟩ := exists_valuativeExtension K E
    letI := vE
    haveI := hvE
    have hy' := hy
    rw [← map_upperRamificationGroup K E' E v] at hy'
    obtain ⟨y', hy'mem, hy'res⟩ := hy'
    obtain ⟨x, hx⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E') F y'
    refine ⟨x, ⟨?_, ?_⟩⟩
    · rw [Set.mem_preimage, SetLike.mem_coe, hx]
      exact hy'mem
    · rw [Set.mem_preimage, Set.mem_singleton_iff,
        IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply E E' x, hx]
      exact hy'res
  have hdir : Directed (· ⊇ ·) T := by
    intro E₁ E₂
    refine ⟨⟨E₁.1 ⊔ E₂.1, le_trans E₁.2 le_sup_left⟩, fun x hx => ⟨?_, hx.2⟩,
      fun x hx => ⟨?_, hx.2⟩⟩
    · exact restrictNormalHom_mem_upperRamificationGroup K F E₁.1 (E₁.1 ⊔ E₂.1)
        le_sup_left x hx.1
    · exact restrictNormalHom_mem_upperRamificationGroup K F E₂.1 (E₁.1 ⊔ E₂.1)
        le_sup_right x hx.1
  have hclosed : ∀ E' : {E' : FiniteGaloisIntermediateField K F // E ≤ E'},
      IsClosed (T E') := fun E' =>
    ((isClosed_discrete _).preimage
        (InfiniteGalois.restrictNormalHom_continuous E'.1.toIntermediateField)).inter
      ((isClosed_discrete _).preimage
        (InfiniteGalois.restrictNormalHom_continuous E.toIntermediateField))
  obtain ⟨x, hx⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
    T hdir hne (fun E' => (hclosed E').isCompact) hclosed
  rw [Set.mem_iInter] at hx
  refine ⟨x, ?_, (hx ⟨E, le_rfl⟩).2⟩
  rw [mem_ramificationFiltration_iff]
  intro E''
  exact restrictNormalHom_mem_upperRamificationGroup K F E'' (E'' ⊔ E) le_sup_left x
    (hx ⟨E'' ⊔ E, le_sup_right⟩).1

/-- The ramification filtration of an infinite Galois group restricts *onto* each finite
level: the image of `G (v)` under restriction to a finite Galois subextension `E` is the whole
`v`th upper-numbering group of `E` over `K`—the surjectivity that makes `G (v)` the inverse
limit of the finite levels and not merely a subgroup of it
([Serre 1979, Chap. IV, §3, Rem. 1, p.75][Serre1979];
[Hyeon 2025, §2, (3), p.7][Hyeon2025]). -/
theorem map_ramificationFiltration [TopologicalSpace K] [IsMixedCharLocalField K]
    [IsGalois K F] (E : FiniteGaloisIntermediateField K F) (v : ℝ) :
    Subgroup.map (AlgEquiv.restrictNormalHom E) (ramificationFiltration K F v) =
      upperRamificationGroup K E v := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, mem_ramificationFiltration_iff] at hg
    exact hg E
  · intro y hy
    obtain ⟨x, hxmem, hxres⟩ := exists_ramificationFiltration_restrictNormalHom_eq K F E hy
    exact ⟨x, hxmem, hxres⟩

/-- For a finite Galois extension the inverse-limit filtration recovers the finite-level
object: `G (v) = G^v`
([Serre 1979, Chap. IV, §3, Rem. 1, p.75][Serre1979]). -/
theorem ramificationFiltration_eq_upperRamificationGroup [TopologicalSpace K]
    [IsMixedCharLocalField K] [IsGalois K F] [FiniteDimensional K F] (v : ℝ) :
    ramificationFiltration K F v = upperRamificationGroup K F v := by
  haveI : IsGalois K (⊤ : IntermediateField K F) :=
    IsGalois.of_algEquiv IntermediateField.topEquiv.symm
  let T : FiniteGaloisIntermediateField K F := ⟨⊤⟩
  have hinjT : Function.Injective (AlgEquiv.restrictNormalHom (F := K) (K₁ := F) T) := by
    intro σ τ h
    ext x
    have hσ := AlgEquiv.restrictNormal_commutes σ (T : IntermediateField K F)
      ⟨x, IntermediateField.mem_top⟩
    have hτ := AlgEquiv.restrictNormal_commutes τ (T : IntermediateField K F)
      ⟨x, IntermediateField.mem_top⟩
    have hval := congrArg (fun ρ : T ≃ₐ[K] T =>
      (algebraMap (T : IntermediateField K F) F (ρ ⟨x, IntermediateField.mem_top⟩))) h
    exact hσ.symm.trans (hval.trans hτ)
  apply le_antisymm
  · -- the limit constrains the top level, where restriction is injective
    intro g hg
    rw [mem_ramificationFiltration_iff] at hg
    have hT := hg T
    obtain ⟨vT, hvT⟩ := exists_valuativeExtension K T
    letI := vT
    haveI := hvT
    haveI : FiniteDimensional (T : IntermediateField K F) F :=
      Module.Finite.right K (T : IntermediateField K F) F
    rw [← map_upperRamificationGroup K F T v] at hT
    obtain ⟨g', hg'mem, hg'⟩ := hT
    exact hinjT hg' ▸ hg'mem
  · -- Herbrand compatibility pushes the finite object into every level
    intro g hg
    rw [mem_ramificationFiltration_iff]
    intro E
    obtain ⟨vE, hvE⟩ := exists_valuativeExtension K E
    letI := vE
    haveI := hvE
    haveI : FiniteDimensional (E : IntermediateField K F) F :=
      Module.Finite.right K (E : IntermediateField K F) F
    rw [← map_upperRamificationGroup K F E v]
    exact ⟨g, hg, rfl⟩

end Atlas.Knowledge
