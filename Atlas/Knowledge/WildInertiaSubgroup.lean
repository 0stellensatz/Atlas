import Mathlib
import Atlas.Knowledge.RamificationFiltration
import Atlas.Knowledge.AbsoluteInertiaSubgroup

/-!
# wild inertia subgroup

The bottom of the ramification filtration of a Galois extension `F` of a local field `K`. The
filtration `Atlas.Knowledge.RamificationFiltration` opens with the inertia group—`G (0)` is
the Galois group of `F` over the maximal unramified subextension, for the absolute group the
kernel `Atlas.Knowledge.AbsoluteInertiaSubgroup`—and immediately below it sits the **wild
inertia group** `G (0+) = ⋃ v > 0, G (v)`, the Galois group of `F` over the maximal tamely
ramified subextension. This file defines `G (0+)`, proves the union is already a subgroup with
the expected membership and its place under `G (0)`, and records the identification of
`G (0)` with the absolute inertia subgroup and the closedness of `G (0+)` as claims.

## Main definitions

* `wildInertiaSubgroup` — `G (0+)`, the join of the `G (v)` over `v > 0`.

## Main statements

* `mem_wildInertiaSubgroup_iff` — the join of the directed family is its union: membership is
  membership in some `G (v)`, `v > 0`.
* `wildInertiaSubgroup_le` — `G (0+) ≤ G (0)`.
* `ramificationFiltration_zero` — over the algebraic closure, `G (0)` is the absolute inertia
  subgroup, recorded ahead of its proof.
* `isClosed_wildInertiaSubgroup` — `G (0+)` of the absolute group is closed, recorded ahead
  of its proof.

## Implementation notes

The source takes the plain union over `v > 0`; here the definition is the lattice join, and
`mem_wildInertiaSubgroup_iff`—antitonicity makes the family directed—says the two agree, so
nothing is lost to closure-taking. Closedness of `G (0+)` is *not* formal: a union of closed
subgroups has no reason to be closed, and that this one is belongs to the same circle of facts
as the identification of `G (0)`, both recorded rather than proved. Both identification claims
are stated over the algebraic closure, where the layer already owns the inertia object; the
tame quotient `G (0) / G (0+)` and the freeness of `G (0+)` are later tranches of the backlog
(`Atlas.Knowledge.AbsoluteGaloisProsolvability` consumes them).

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic
  local fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] (F : Type*) [Field F] [Algebra K F]

/-- The **wild inertia subgroup** `G (0+) = ⋃ v > 0, G (v)`: the join of the ramification
filtration strictly below index `0`, classically the Galois group of `F` over the maximal
tamely ramified subextension ([Hyeon 2025, §2, p.7][Hyeon2025]). -/
noncomputable def wildInertiaSubgroup : Subgroup (F ≃ₐ[K] F) :=
  ⨆ v : {v : ℝ // 0 < v}, ramificationFiltration K F (v : ℝ)

/-- The join defining the wild inertia subgroup is the union the source takes: the family is
directed by antitonicity, so `g ∈ G (0+)` iff `g ∈ G (v)` for some `v > 0`
([Hyeon 2025, §2, p.7][Hyeon2025]). -/
theorem mem_wildInertiaSubgroup_iff {g : F ≃ₐ[K] F} :
    g ∈ wildInertiaSubgroup K F ↔ ∃ v : ℝ, 0 < v ∧ g ∈ ramificationFiltration K F v := by
  haveI : Nonempty {v : ℝ // 0 < v} := ⟨⟨1, one_pos⟩⟩
  have hdir : Directed (· ≤ ·)
      (fun v : {v : ℝ // 0 < v} => ramificationFiltration K F (v : ℝ)) := by
    intro v w
    exact ⟨⟨min v w, lt_min v.2 w.2⟩,
      ramificationFiltration_antitone K F (min_le_left _ _),
      ramificationFiltration_antitone K F (min_le_right _ _)⟩
  rw [wildInertiaSubgroup, Subgroup.mem_iSup_of_directed hdir]
  exact ⟨fun ⟨v, hv⟩ => ⟨v, v.2, hv⟩, fun ⟨v, hv, hmem⟩ => ⟨⟨v, hv⟩, hmem⟩⟩

/-- The wild inertia subgroup sits at the bottom of the filtration: `G (0+) ≤ G (0)`
([Hyeon 2025, §2, p.7][Hyeon2025]). -/
theorem wildInertiaSubgroup_le :
    wildInertiaSubgroup K F ≤ ramificationFiltration K F 0 :=
  iSup_le fun v => ramificationFiltration_antitone K F (le_of_lt v.2)

instance : (wildInertiaSubgroup K F).Normal := by
  constructor
  intro n hn g
  rw [mem_wildInertiaSubgroup_iff] at hn ⊢
  obtain ⟨v, hv, hmem⟩ := hn
  exact ⟨v, hv, Subgroup.Normal.conj_mem inferInstance _ hmem _⟩

variable [TopologicalSpace K] [IsMixedCharLocalField K]

/-- The bottom of the filtration is the inertia group: over the algebraic closure of a
mixed-characteristic local field, `G (0)` is the absolute inertia subgroup—the kernel of the
map to the residue Galois group. Claim recorded ahead of its proof
([Hyeon 2025, §2, p.7][Hyeon2025]). -/
theorem ramificationFiltration_zero :
    ramificationFiltration K (AlgebraicClosure K) 0 = absoluteInertiaSubgroup K := by
  sorry

/-- The wild inertia subgroup of the absolute Galois group of a mixed-characteristic local
field is closed—not a formal fact about the union, but the start of the unramified / tame /
wild tower. Claim recorded ahead of its proof ([Hyeon 2025, §2, p.7][Hyeon2025]). -/
theorem isClosed_wildInertiaSubgroup :
    IsClosed (wildInertiaSubgroup K (AlgebraicClosure K) :
      Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) := by
  sorry

end Atlas.Knowledge
