import Mathlib

/-!
# closed derived series

The **closed derived series** of a topological group `G`: the descending sequence of closed
normal subgroups starting at `G` itself, each next term the topological closure of the commutator
subgroup of the previous. It differs from Mathlib's `derivedSeries` in taking the closure at
every step, which is what makes each term a closed subgroup—for a profinite `G` the objects that
correspond to subextensions under the Galois correspondence. Its vanishing defines
`Atlas.Knowledge.IsMStepSolvable`, and the quotient by its `m`-th term is the maximal `m`-step
solvable quotient `Atlas.Knowledge.MStepSolvableQuotient`.

## Main definitions

* `closedDerivedSeries` — the series `G = G^[0] ⊇ G^[1] ⊇ ⋯`, with
  `G^[m + 1] = closure ⁅G^[m], G^[m]⁆`.

## Main statements

* `isClosed_closedDerivedSeries`, `closedDerivedSeries_normal` — each term is closed and normal.
* `closedDerivedSeries_antitone` — the series descends.
* `derivedSeries_le_closedDerivedSeries` — it lies above Mathlib's `derivedSeries` termwise.
* `closedDerivedSeries_one` — its first term is the subgroup Mathlib's
  `TopologicalAbelianization` quotients by, definitionally.
* `map_closedDerivedSeries_le`, `map_closedDerivedSeries` — a continuous homomorphism carries
  the series into the series, and a continuous closed surjection carries it onto the series.
  The latter is what computes the series of a quotient of a compact group and so feeds every
  statement about `Atlas.Knowledge.MStepSolvableQuotient`.

## Implementation notes

The definition asks for a topological group but not for profiniteness or Hausdorffness: closure
and normality need neither. The source also notes each term is characteristic; that is deferred
until something needs it, since for a topological group the right statement (invariance under
*continuous* automorphisms) is weaker than `Subgroup.Characteristic`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The **closed derived series** of a topological group: `closedDerivedSeries G 0 = ⊤`, and each
following term is the topological closure of the commutator subgroup of the previous
([Hyeon 2025, §2, p.8][Hyeon2025]). -/
def closedDerivedSeries : ℕ → Subgroup G
  | 0 => ⊤
  | m + 1 => (⁅closedDerivedSeries m, closedDerivedSeries m⁆).topologicalClosure

@[simp]
theorem closedDerivedSeries_zero : closedDerivedSeries G 0 = ⊤ :=
  rfl

theorem closedDerivedSeries_succ (m : ℕ) :
    closedDerivedSeries G (m + 1)
      = (⁅closedDerivedSeries G m, closedDerivedSeries G m⁆).topologicalClosure :=
  rfl

/-- The first term of the closed derived series is the closure of the commutator subgroup—the
subgroup Mathlib's `TopologicalAbelianization` is the quotient by. -/
theorem closedDerivedSeries_one :
    closedDerivedSeries G 1 = (commutator G).topologicalClosure :=
  rfl

theorem isClosed_closedDerivedSeries (m : ℕ) :
    IsClosed (closedDerivedSeries G m : Set G) := by
  cases m with
  | zero => simp
  | succ m => exact Subgroup.isClosed_topologicalClosure _

instance closedDerivedSeries_normal (m : ℕ) : (closedDerivedSeries G m).Normal := by
  induction m with
  | zero =>
    rw [closedDerivedSeries_zero]
    infer_instance
  | succ m ih =>
    haveI := ih
    exact Subgroup.is_normal_topologicalClosure _

theorem closedDerivedSeries_succ_le (m : ℕ) :
    closedDerivedSeries G (m + 1) ≤ closedDerivedSeries G m :=
  Subgroup.topologicalClosure_minimal _ (Subgroup.commutator_le_self _)
    (isClosed_closedDerivedSeries G m)

theorem closedDerivedSeries_antitone : Antitone (closedDerivedSeries G) :=
  antitone_nat_of_succ_le (closedDerivedSeries_succ_le G)

/-- The closed derived series lies above the abstract derived series termwise; for a discrete
group the two coincide. -/
theorem derivedSeries_le_closedDerivedSeries (m : ℕ) :
    derivedSeries G m ≤ closedDerivedSeries G m := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    exact (Subgroup.commutator_mono ih ih).trans (Subgroup.le_topologicalClosure _)

/-! ## Functoriality -/

variable {G} {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A continuous homomorphism carries the topological closure of a subgroup into the
topological closure of its image. -/
theorem map_topologicalClosure_le (f : G →* H) (hf : Continuous f) (S : Subgroup G) :
    S.topologicalClosure.map f ≤ (S.map f).topologicalClosure :=
  Subgroup.map_le_iff_le_comap.mpr <| Subgroup.topologicalClosure_minimal S
    ((Subgroup.le_comap_map f S).trans (Subgroup.comap_mono (Subgroup.le_topologicalClosure _)))
    ((Subgroup.isClosed_topologicalClosure _).preimage hf)

/-- A continuous closed homomorphism carries the topological closure of a subgroup onto the
topological closure of its image. -/
theorem map_topologicalClosure (f : G →* H) (hf : Continuous f) (hf' : IsClosedMap f)
    (S : Subgroup G) : S.topologicalClosure.map f = (S.map f).topologicalClosure := by
  refine le_antisymm (map_topologicalClosure_le f hf S) ?_
  refine Subgroup.topologicalClosure_minimal _
    (Subgroup.map_mono (Subgroup.le_topologicalClosure S)) ?_
  rw [Subgroup.coe_map]
  exact hf' _ (Subgroup.isClosed_topologicalClosure S)

/-- A continuous homomorphism carries each term of the closed derived series into the
corresponding term of the codomain's series. -/
theorem map_closedDerivedSeries_le (f : G →* H) (hf : Continuous f) (m : ℕ) :
    (closedDerivedSeries G m).map f ≤ closedDerivedSeries H m := by
  induction m with
  | zero => exact le_top
  | succ m ih =>
    rw [closedDerivedSeries_succ, closedDerivedSeries_succ]
    calc (⁅closedDerivedSeries G m, closedDerivedSeries G m⁆.topologicalClosure).map f
        ≤ (⁅closedDerivedSeries G m, closedDerivedSeries G m⁆.map f).topologicalClosure :=
          map_topologicalClosure_le f hf _
      _ = (⁅(closedDerivedSeries G m).map f,
            (closedDerivedSeries G m).map f⁆).topologicalClosure := by
          rw [Subgroup.map_commutator]
      _ ≤ (⁅closedDerivedSeries H m, closedDerivedSeries H m⁆).topologicalClosure :=
          Subgroup.topologicalClosure_mono (Subgroup.commutator_mono ih ih)

/-- A continuous closed surjection carries the closed derived series onto the closed derived
series. For a quotient map of compact Hausdorff groups this says the series of the quotient is
the image of the series. -/
theorem map_closedDerivedSeries (f : G →* H) (hf : Continuous f) (hf' : IsClosedMap f)
    (hsurj : Function.Surjective f) (m : ℕ) :
    (closedDerivedSeries G m).map f = closedDerivedSeries H m := by
  induction m with
  | zero => simpa using Subgroup.map_top_of_surjective f hsurj
  | succ m ih =>
    rw [closedDerivedSeries_succ, closedDerivedSeries_succ, map_topologicalClosure f hf hf',
      Subgroup.map_commutator, ih]

end Atlas.Knowledge
