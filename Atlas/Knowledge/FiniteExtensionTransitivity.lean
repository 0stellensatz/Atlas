import Mathlib
import Atlas.Knowledge.DegreeData

/-!
# finiteness transitivity of abstract extensions

Finiteness of the relative coset spaces in a tower of abstract fields — closed
subgroups of a topological group — composes and restricts: a tower of two
finite extensions is finite, and a finite extension stays finite over every
intermediate field. Pure relative-index arithmetic, used whenever the
reciprocity engine passes between a finite abstract field and the towers
through it (#104).

## Main statements

* `finite_extension_trans` — a tower of two finite extensions is finite;
  proved.
* `finite_extension_over_intermediate` — a finite extension is finite over
  every intermediate field; proved.

## Implementation notes

The engine's relative subgroup is `Subgroup.subgroupOf`, which mentions no
containment — so the order hypotheses the source's `extensionSubgroup`
spelling threads through these statements are inert here, exactly as they
are inert inside the source's abbreviation itself. They are kept, with
underscore names, as the semantic guard the layer's other inert containments
carry: the statements are about towers, and every caller has the proofs in
hand. The source names are kept even where they mention the unported
spelling.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **Finiteness is transitive in a tower of abstract fields** — the order
hypotheses are inert semantic guards ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:217`]
[Yamaguchi2026]). -/
theorem finite_extension_trans
    {P L K : ClosedSubgroup G}
    (_hPL : P.toSubgroup ≤ L.toSubgroup)
    (_hLK : L.toSubgroup ≤ K.toSubgroup)
    [hPLfinite : Finite
      (L.toSubgroup ⧸ P.toSubgroup.subgroupOf L.toSubgroup)]
    [hLKfinite : Finite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)] :
    Finite (K.toSubgroup ⧸ P.toSubgroup.subgroupOf K.toSubgroup) := by
  have hPL0 : P.toSubgroup.relIndex L.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite L.toSubgroup _
      (P.toSubgroup.subgroupOf L.toSubgroup) hPLfinite
  have hLK0 : L.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (L.toSubgroup.subgroupOf K.toSubgroup) hLKfinite
  apply Nat.finite_of_card_ne_zero
  change (P.toSubgroup.subgroupOf K.toSubgroup).index ≠ 0
  simpa [Subgroup.relIndex] using
    Subgroup.relIndex_ne_zero_trans hPL0 hLK0

/-- **A finite extension remains finite over every intermediate field**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FiniteGaloisSubextension.lean:240`]
[Yamaguchi2026]). -/
theorem finite_extension_over_intermediate
    {P M K : ClosedSubgroup G}
    (_hPK : P.toSubgroup ≤ K.toSubgroup)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    (hPM : P.toSubgroup ≤ M.toSubgroup)
    [hPKfinite : Finite
      (K.toSubgroup ⧸ P.toSubgroup.subgroupOf K.toSubgroup)] :
    Finite (M.toSubgroup ⧸ P.toSubgroup.subgroupOf M.toSubgroup) := by
  have hPK0 : P.toSubgroup.relIndex K.toSubgroup ≠ 0 := by
    rw [Subgroup.relIndex]
    exact @Subgroup.index_ne_zero_of_finite K.toSubgroup _
      (P.toSubgroup.subgroupOf K.toSubgroup) hPKfinite
  have hPM0 : P.toSubgroup.relIndex M.toSubgroup ≠ 0 := by
    intro hzero
    have hmul := Subgroup.relIndex_mul_relIndex
      P.toSubgroup M.toSubgroup K.toSubgroup hPM hMK
    rw [hzero, zero_mul] at hmul
    exact hPK0 hmul.symm
  apply Nat.finite_of_card_ne_zero
  change (P.toSubgroup.subgroupOf M.toSubgroup).index ≠ 0
  simpa [Subgroup.relIndex] using hPM0

end Atlas.Knowledge
