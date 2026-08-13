import Mathlib
import Atlas.Knowledge.ClosedDerivedSeries
import Atlas.Knowledge.MStepSolvableQuotient

/-!
# stability of the m-step solvable quotient

Truncating a compact group deeper than it looks does not disturb the `m`-step solvable
quotients of its open subgroups: for `H` an open subgroup of `Γ` containing the `m`-th term of
the closed derived series `Atlas.Knowledge.ClosedDerivedSeries`, the natural surjection from
`H^n` onto the `n`-step solvable quotient of the image of `H` in `Γ^{m+n}` is bijective. This
is the source's Lemma 2.3 (1), the mechanism by which its induction on `m` can pass to open
subgroups of a truncation `Γ^{m+n}` and still speak about honest `n`-step solvable quotients—in
particular, the "in particular" of the source's Lemma 2.3 (2): an open subgroup of a group of
MLF^{m+n}-type containing the `m`-th derived term has `n`-step solvable quotient again of
MLF^n-type.

## Main statements

* `closedDerivedSeries_le_map_subtype` — for a closed subgroup `H` above the `m`-th term, the
  `(m + n)`-th term of the series of `Γ` lies inside the `n`-th term of the intrinsic series of
  `H`. This is `closedDerivedSeries Γ (m + n) = closedDerivedSeries (closedDerivedSeries Γ m) n`
  in inequality form, with the intrinsic series compared through `Subgroup.map H.subtype`.
* `mStepSolvableQuotient_map_mk'_bijective` — the natural surjection
  `H^n →* (H ⧸ Γ^[m+n])^n` is bijective.

## Implementation notes

The source works with an open subgroup `H` of the quotient `Γ^{m+n}` containing its `m`-th
derived term; here `H` is taken open in `Γ` containing `closedDerivedSeries Γ m`, which is the
same data pulled back along the projection, and the quotient `H ⧸ Γ^[m+n]` is formed as
`↥H ⧸ (closedDerivedSeries Γ (m + n)).subgroupOf H`. Only compactness and Hausdorffness of `Γ`
are used, not profiniteness: they are what make the quotient and inclusion maps closed, so that
the closed derived series can be pushed forward through `map_closedDerivedSeries`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [T2Space Γ]

/-- For a closed subgroup `H` of a compact group containing the `m`-th term of the closed
derived series, the `(m + n)`-th term of the series lies inside the image of the `n`-th term of
the intrinsic series of `H` ([Hyeon 2025, Lem. 2.3 (1), p.8][Hyeon2025]). -/
theorem closedDerivedSeries_le_map_subtype {H : Subgroup Γ} (hH : IsClosed (H : Set Γ))
    {m : ℕ} (hm : closedDerivedSeries Γ m ≤ H) (n : ℕ) :
    closedDerivedSeries Γ (m + n) ≤ (closedDerivedSeries ↥H n).map H.subtype := by
  haveI : CompactSpace ↥H := isCompact_iff_compactSpace.mp hH.isCompact
  induction n with
  | zero =>
    rw [Nat.add_zero, closedDerivedSeries_zero, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    exact hm
  | succ n ih =>
    have hsucc : closedDerivedSeries Γ (m + (n + 1))
        = (⁅closedDerivedSeries Γ (m + n),
            closedDerivedSeries Γ (m + n)⁆).topologicalClosure := rfl
    rw [hsucc, closedDerivedSeries_succ,
      map_topologicalClosure H.subtype continuous_subtype_val
        continuous_subtype_val.isClosedMap,
      Subgroup.map_commutator]
    exact Subgroup.topologicalClosure_mono (Subgroup.commutator_mono ih ih)

/-- The natural surjection from the `n`-step solvable quotient of an open subgroup `H` above
`closedDerivedSeries Γ m` onto the `n`-step solvable quotient of its truncation
`H ⧸ closedDerivedSeries Γ (m + n)` is bijective
([Hyeon 2025, Lem. 2.3 (1), p.8][Hyeon2025]). -/
theorem mStepSolvableQuotient_map_mk'_bijective {H : Subgroup Γ} (hH : IsOpen (H : Set Γ))
    {m : ℕ} (hm : closedDerivedSeries Γ m ≤ H) (n : ℕ)
    (hcont : Continuous (QuotientGroup.mk' ((closedDerivedSeries Γ (m + n)).subgroupOf H))) :
    Function.Bijective (mStepSolvableQuotient.map n
      (QuotientGroup.mk' ((closedDerivedSeries Γ (m + n)).subgroupOf H)) hcont) := by
  have hHc : IsClosed (H : Set Γ) := Subgroup.isClosed_of_isOpen H hH
  haveI : CompactSpace ↥H := isCompact_iff_compactSpace.mp hHc.isCompact
  set N : Subgroup ↥H := (closedDerivedSeries Γ (m + n)).subgroupOf H with hN
  haveI : IsClosed (N : Set ↥H) :=
    (isClosed_closedDerivedSeries Γ (m + n)).preimage continuous_subtype_val
  -- the kernel of the truncation sits inside the `n`-th term of the intrinsic series
  have hNle : N ≤ closedDerivedSeries ↥H n := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := closedDerivedSeries_le_map_subtype hHc hm n
      (Subgroup.mem_subgroupOf.mp hx)
    exact Subtype.val_injective hyx ▸ hy
  constructor
  · -- injectivity: the series of the truncation is the image of the series
    have hser := map_closedDerivedSeries (QuotientGroup.mk' N) hcont hcont.isClosedMap
      (QuotientGroup.mk'_surjective N) n
    rw [injective_iff_map_eq_one]
    intro x hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (closedDerivedSeries ↥H n) x
    have h1 : QuotientGroup.mk' N g ∈ closedDerivedSeries (↥H ⧸ N) n :=
      (QuotientGroup.eq_one_iff (QuotientGroup.mk' N g)).mp hx
    rw [← hser] at h1
    have h2 : g ∈ Subgroup.comap (QuotientGroup.mk' N)
        ((closedDerivedSeries ↥H n).map (QuotientGroup.mk' N)) := h1
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_of_le_left hNle] at h2
    exact (QuotientGroup.eq_one_iff g).mpr h2
  · exact mStepSolvableQuotient.map_surjective n _ hcont (QuotientGroup.mk'_surjective N)

end Atlas.Knowledge
