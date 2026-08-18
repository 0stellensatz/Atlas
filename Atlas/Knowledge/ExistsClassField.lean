import Mathlib
import Atlas.Knowledge.MaximalAbelianExtension
import Atlas.Knowledge.IdeleClassNormRange

/-!
# existence theorem

The existence theorem of global class field theory: every open finite-index subgroup of
the idele class group is the norm subgroup of exactly one finite subextension of the
maximal abelian extension. Existence and uniqueness are the two recorded claims — the
correspondence `L ↦ N_{L/K} (C_L)` is thereby a bijection onto the open finite-index
subgroups, which is Milne's corollary.

## Main statements

* `exists_classField` — a class field for every open finite-index subgroup; recorded
  ahead of its proof.
* `classField_unique` — at most one; recorded ahead of its proof.

## Implementation notes

The subgroup class is the literature's: *open* of finite index (Milne Thm. 5.5; NSW
(8.1.24), which states the norm groups of finite *separable* extensions — the abelian
reduction is `Atlas.Knowledge.normLimitation` — and whose §2 remark, p.444, adds that for
a number field all open subgroups are of finite index). The source
quantifies over *closed* finite-index subgroups
(`GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldConstruction.lean:97`);
in a topological group a finite-index subgroup is open exactly when it is closed, so the
two forms coincide, and Atlas states the books'. The class fields are found inside
`Atlas.Knowledge.maximalAbelianExtension` as `FiniteGaloisIntermediateField`s — their
abelianness is automatic and not restated.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [NeukirchEtAl2008] J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of number fields*,
  Grundlehren der mathematischen Wissenschaften **323**, Springer Berlin Heidelberg, 2008.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- **The existence theorem**: every open finite-index subgroup of the idele class group
is the norm subgroup of a finite subextension of `K^ab`. Claim recorded ahead of its proof
([Milne 2020, Chap. V, §5, Thm. 5.5, p.179][MilneCFT];
[Neukirch–Schmidt–Wingberg 2008, Chap. VIII, §1, (8.1.24), p.442][NeukirchEtAl2008];
[Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/ClosedFiniteIndexClassFieldOriginalField.lean:197`]
[Yamaguchi2026]). -/
theorem exists_classField (H : Subgroup (IdeleClassGroup K))
    (hopen : IsOpen (H : Set (IdeleClassGroup K))) (hfin : H.FiniteIndex) :
    ∃ L : FiniteGaloisIntermediateField K (maximalAbelianExtension K),
      ideleClassNormRange K L = H := by
  sorry

/-- **Uniqueness of the class field**: two finite subextensions of `K^ab` with the same
norm subgroup coincide. Claim recorded ahead of its proof
([Milne 2020, Chap. V, §5, Thm. 5.5 and Cor. 5.6, p.179][MilneCFT]). -/
theorem classField_unique
    {L M : FiniteGaloisIntermediateField K (maximalAbelianExtension K)}
    (h : ideleClassNormRange K L = ideleClassNormRange K M) : L = M := by
  sorry

end Atlas.Knowledge

end
