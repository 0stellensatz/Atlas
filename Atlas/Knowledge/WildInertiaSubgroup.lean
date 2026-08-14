import Mathlib
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
and lies under `G (0)`, and as a set it is the closure of the union—and records the
identification of `G (0)` with the absolute inertia subgroup and the abelianness of the tame
quotient as claims.

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
  quotient is abelian, recorded ahead of its proof.

## Implementation notes

The source writes `G (0+) = ⋃ v > 0, G (v)` with no closure, and identifies it with the
Galois group of `F` over the maximal tamely ramified subextension. For infinite `F` the two
sides of that identification differ by a closure: the right side is closed, while the plain
union is in general a proper dense subgroup of it—over `ℚ_p` the upper-numbering breaks of
finite quotients accumulate at `0`, so by Baire the countable union of the closed proper steps
`G (v)` cannot be closed, let alone all of the wild inertia. The definition here therefore
takes the topological closure, which is the object the source's identification is true of;
`coe_wildInertiaSubgroup` keeps the union visible as a dense subgroup, and antitonicity makes
that union a directed join, so nothing below `0` is lost. The identification itself waits on
tame vocabulary the layer does not yet carry; what is recorded now is the inertia end,
`ramificationFiltration_zero`, and the abelianness of `G (0) / G (0+)` in commutator form,
which is the shape the prosolvability backlog
(`Atlas.Knowledge.AbsoluteGaloisProsolvability`) consumes.

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
maximal tamely ramified subextension. The source writes the plain union, which for infinite
`F` is a proper dense subgroup; the closure is the object its identification with the tame
fixed field is true of ([Hyeon 2025, §2, p.7][Hyeon2025]). -/
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

/-- The wild inertia subgroup is closed—by definition, the closure repairing the source's
plain union, which is in general properly dense in it
([Hyeon 2025, §2, p.7][Hyeon2025]). -/
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
abelian, being pro-cyclic in the limit of the cyclic `G_0 / G_1` of the finite levels. Claim
recorded ahead of its proof ([Serre 1979, Chap. IV, §2, Cor. 1, p.67][Serre1979]). -/
theorem commutator_mem_wildInertiaSubgroup
    {a b : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (ha : a ∈ ramificationFiltration K (AlgebraicClosure K) 0)
    (hb : b ∈ ramificationFiltration K (AlgebraicClosure K) 0) :
    a * b * a⁻¹ * b⁻¹ ∈ wildInertiaSubgroup K (AlgebraicClosure K) := by
  sorry

end Atlas.Knowledge
