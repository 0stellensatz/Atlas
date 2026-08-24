import Mathlib
import Atlas.Knowledge.CommutatorMemLowerRamificationGroup
import Atlas.Knowledge.RamificationFiltration
import Atlas.Knowledge.AbsoluteInertiaSubgroup

/-!
# wild inertia subgroup

The bottom of the ramification filtration of a Galois extension `F` of a local field `K`. The
filtration `Atlas.Knowledge.RamificationFiltration` opens with the inertia group—`G (0)` is
the Galois group of `F` over the maximal unramified subextension, for the absolute group the
kernel `Atlas.Knowledge.AbsoluteInertiaSubgroup`—and immediately below it sits the **wild
inertia group** `G (0+)`, classically the Galois group of `F` over the maximal tamely ramified
subextension. This file defines `G (0+)` as the topological closure of the join of the
`G (v)`, `v > 0`, proves its basic place—each `G (v)` sits inside it, it is closed and normal
and lies under `G (0)`, and as a set it is the closure of the union—proves the abelianness of
the tame quotient in commutator form, and records the identification of `G (0)` with the
absolute inertia subgroup as a claim.

## Main definitions

* `wildInertiaSubgroup` — `G (0+)`, the closure of the join of the `G (v)` over `v > 0`.

## Main statements

* `le_wildInertiaSubgroup` / `coe_wildInertiaSubgroup` — the filtration below `0` generates:
  each `G (v)` with `v > 0` is contained, and the union of them is dense.
* `isClosed_wildInertiaSubgroup` / `wildInertiaSubgroup_le` — `G (0+)` is closed and sits
  under `G (0)`.
* `ramificationFiltration_zero` — over the algebraic closure, `G (0)` is the absolute inertia
  subgroup, recorded ahead of its proof.
* `commutator_mem_wildInertiaSubgroup` — commutators of `G (0)` fall into `G (0+)`: the tame
  quotient is abelian.

## Implementation notes

The source defines `G (0+)` as the *closure* of the union of the `G (v)`, `v > 0`—the
closure bar in its display is load-bearing, and a plain-text extraction of the PDF drops it,
which is worth a warning to any future reader working from one. The bar cannot be omitted:
for infinite `F` the plain union is in general a proper dense subgroup of the wild
inertia—over `ℚ_p` the upper-numbering breaks of finite quotients accumulate at `0`, so by
Baire the countable union of the closed proper steps `G (v)` cannot be closed. The definition
here renders the bar as `Subgroup.topologicalClosure`, the object the source identifies with
the tame fixed field;
`coe_wildInertiaSubgroup` keeps the union visible as a dense subgroup, and antitonicity makes
that union a directed join, so nothing below `0` is lost. The identification itself waits on
tame vocabulary the layer does not yet carry; what is recorded now is the inertia end,
`ramificationFiltration_zero`. The abelianness of `G (0) / G (0+)` is proved in the
commutator form the prosolvability backlog (`Atlas.Knowledge.AbsoluteGaloisProsolvability`)
consumes: at each finite level the commutator falls one step down by
`Atlas.Knowledge.commutator_mem_lowerRamificationGroup`, and the surjectivity of the limit
onto its finite levels, `Atlas.Knowledge.map_ramificationFiltration`, lifts it into a
positive step of the infinite filtration, hence into the closure.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic
  local fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (F : Type*) [Field F] [Algebra K F]

/-- The **wild inertia subgroup** `G (0+)`: the topological closure of the join of the
ramification filtration over indices `v > 0`, classically the Galois group of `F` over the
maximal tamely ramified subextension. The closure renders the source's closure bar and is
load-bearing: for infinite `F` the plain union is a proper dense subgroup
([Hyeon 2025, §2, p.7][Hyeon2025]). -/
noncomputable def wildInertiaSubgroup : Subgroup (F ≃ₐ[K] F) :=
  (⨆ v : {v : ℝ // 0 < v}, ramificationFiltration K F (v : ℝ)).topologicalClosure

private theorem ramificationFiltration_directed :
    Directed (· ≤ ·)
      (fun v : {v : ℝ // 0 < v} => ramificationFiltration K F (v : ℝ)) := by
  intro v w
  exact ⟨⟨min v w, lt_min v.2 w.2⟩,
    ramificationFiltration_antitone K F (min_le_left _ _),
    ramificationFiltration_antitone K F (min_le_right _ _)⟩

/-- Every step of the filtration below the inertia end lies in the wild inertia subgroup:
`G (v) ≤ G (0+)` for `v > 0` ([Hyeon 2025, §2, p.7][Hyeon2025]). -/
theorem le_wildInertiaSubgroup {v : ℝ} (hv : 0 < v) :
    ramificationFiltration K F v ≤ wildInertiaSubgroup K F :=
  (le_iSup (fun w : {w : ℝ // 0 < w} => ramificationFiltration K F (w : ℝ)) ⟨v, hv⟩).trans
    (Subgroup.le_topologicalClosure _)

/-- As a set, the wild inertia subgroup is the closure of the source's union
`⋃ v > 0, G (v)`—antitonicity makes the family directed, so the join really is the union, and
the union is dense in `G (0+)` ([Hyeon 2025, §2, p.7][Hyeon2025]). -/
theorem coe_wildInertiaSubgroup :
    (wildInertiaSubgroup K F : Set (F ≃ₐ[K] F)) =
      closure (⋃ v : {v : ℝ // 0 < v},
        (ramificationFiltration K F (v : ℝ) : Set (F ≃ₐ[K] F))) := by
  haveI : Nonempty {v : ℝ // 0 < v} := ⟨⟨1, one_pos⟩⟩
  rw [wildInertiaSubgroup, Subgroup.topologicalClosure_coe]
  congr 1
  ext g
  simp only [SetLike.mem_coe, Set.mem_iUnion]
  exact Subgroup.mem_iSup_of_directed (ramificationFiltration_directed K F)

/-- The wild inertia subgroup is closed—by definition, the source's closure bar rendered as
`Subgroup.topologicalClosure`; the bar is load-bearing, the plain union being in general
properly dense ([Hyeon 2025, §2, p.7][Hyeon2025]). -/
theorem isClosed_wildInertiaSubgroup :
    IsClosed (wildInertiaSubgroup K F : Set (F ≃ₐ[K] F)) :=
  Subgroup.isClosed_topologicalClosure _

/-- The wild inertia subgroup sits at the bottom of the filtration: `G (0+) ≤ G (0)`, the
target being closed ([Hyeon 2025, §2, p.7][Hyeon2025]). -/
theorem wildInertiaSubgroup_le :
    wildInertiaSubgroup K F ≤ ramificationFiltration K F 0 :=
  Subgroup.topologicalClosure_minimal _
    (iSup_le fun v => ramificationFiltration_antitone K F (le_of_lt v.2))
    (isClosed_ramificationFiltration K F 0)

instance : (wildInertiaSubgroup K F).Normal := by
  haveI hjoin : (⨆ v : {v : ℝ // 0 < v}, ramificationFiltration K F (v : ℝ)).Normal := by
    constructor
    intro n hn g
    haveI : Nonempty {v : ℝ // 0 < v} := ⟨⟨1, one_pos⟩⟩
    rw [Subgroup.mem_iSup_of_directed (ramificationFiltration_directed K F)] at hn ⊢
    obtain ⟨v, hv⟩ := hn
    exact ⟨v, Subgroup.Normal.conj_mem inferInstance _ hv _⟩
  exact Subgroup.is_normal_topologicalClosure _

variable [TopologicalSpace K] [IsMixedCharLocalField K]

/-- The bottom of the filtration is the inertia group: over the algebraic closure of a
mixed-characteristic local field, `G (0)` is the absolute inertia subgroup—the kernel of the
map to the residue Galois group. Claim recorded ahead of its proof
([Hyeon 2025, §2, p.7][Hyeon2025]). -/
theorem ramificationFiltration_zero :
    ramificationFiltration K (AlgebraicClosure K) 0 = absoluteInertiaSubgroup K := by
  sorry

/-- Commutators of inertia elements fall into the wild inertia subgroup: the tame quotient
`G (0) / G (0+)` of the absolute Galois group of a mixed-characteristic local field is
abelian, assembled from the abelianness at the finite levels of
`Atlas.Knowledge.commutator_mem_lowerRamificationGroup` through the closure
([Serre 1979, Chap. IV, §2, Cor. 1, p.67][Serre1979]). -/
theorem commutator_mem_wildInertiaSubgroup
    {a b : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (ha : a ∈ ramificationFiltration K (AlgebraicClosure K) 0)
    (hb : b ∈ ramificationFiltration K (AlgebraicClosure K) 0) :
    a * b * a⁻¹ * b⁻¹ ∈ wildInertiaSubgroup K (AlgebraicClosure K) := by
  haveI : IsGalois K (AlgebraicClosure K) := ⟨⟩
  rw [mem_ramificationFiltration_iff] at ha hb
  rw [← SetLike.mem_coe, wildInertiaSubgroup, Subgroup.topologicalClosure_coe,
    mem_closure_iff_nhds]
  intro N hN
  rw [← map_mul_left_nhds_one, Filter.mem_map] at hN
  obtain ⟨E, hE⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois _).mp hN
  -- at the level of `E` the commutator falls one step down the lower numbering
  have haE : AlgEquiv.restrictNormalHom E a ∈ lowerRamificationGroup K E 0 := by
    have h := ha E
    rwa [upperRamificationGroup_zero] at h
  have hbE : AlgEquiv.restrictNormalHom E b ∈ lowerRamificationGroup K E 0 := by
    have h := hb E
    rwa [upperRamificationGroup_zero] at h
  have hcE : AlgEquiv.restrictNormalHom E (a * b * a⁻¹ * b⁻¹) ∈
      upperRamificationGroup K E (herbrandPhi K E 1) := by
    have hupper1 : upperRamificationGroup K E (herbrandPhi K E 1) =
        lowerRamificationGroup K E 1 := by
      rw [upperRamificationGroup, herbrandPsi_herbrandPhi]
      exact realLowerRamificationGroup_eq K E (i := 1) (by norm_num) (by norm_num)
    rw [hupper1, map_mul, map_mul, map_mul, map_inv, map_inv]
    exact commutator_mem_lowerRamificationGroup K E haE hbE
  have hpos : (0 : ℝ) < herbrandPhi K E 1 := by
    have h := herbrandPhi_strictMono K E (show (0 : ℝ) < 1 by norm_num)
    rwa [herbrandPhi_zero] at h
  -- lift it into the corresponding step of the infinite filtration
  have hlift : AlgEquiv.restrictNormalHom E (a * b * a⁻¹ * b⁻¹) ∈
      Subgroup.map (AlgEquiv.restrictNormalHom E)
        (ramificationFiltration K (AlgebraicClosure K) (herbrandPhi K E 1)) := by
    rw [map_ramificationFiltration]
    exact hcE
  obtain ⟨x, hxmem, hxres⟩ := hlift
  refine ⟨x, ?_, ?_⟩
  · -- `x` agrees with the commutator on `E`, so it lies in the given neighbourhood
    have hfix : (a * b * a⁻¹ * b⁻¹)⁻¹ * x ∈ E.fixingSubgroup := by
      rw [FiniteGaloisIntermediateField.mem_fixingSubgroup_iff]
      rw [map_mul, map_inv, hxres, inv_mul_cancel]
    simpa only [Set.mem_preimage, mul_inv_cancel_left] using hE hfix
  · exact (le_iSup (fun w : {w : ℝ // 0 < w} =>
      ramificationFiltration K (AlgebraicClosure K) (w : ℝ)) ⟨herbrandPhi K E 1, hpos⟩) hxmem

end Atlas.Knowledge
