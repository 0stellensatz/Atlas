import Mathlib

/-!
# global Kronecker–Weber theorem

Every finite abelian extension of `ℚ` lies in a cyclotomic field: some
`CyclotomicField n ℚ` receives an embedding of it. The statement is two lines of Mathlib
vocabulary — nothing here depends on any other knowledge item — and the claim is recorded
ahead of its proof, which is the whole global chain: the local theorem at every place,
the compositum machinery carrying the local embeddings up, and the ramification bound
that caps the conductor.

## Main statements

* `globalKroneckerWeber` — recorded ahead of its proof.

## Implementation notes

`L` is `Type`, not `Type*`, matching the source — the claim is recorded for the port.
Nothing formal ties this statement to `Atlas.Knowledge.localKroneckerWeber`: the source
derives global from local through its compositum layer, none of which is ported, so the
two claims stand independent here. Pinned Mathlib has no Kronecker–Weber statement to
identify against. The cyclotomic normalization that gives this containment its
class-field meaning is `Atlas.Knowledge.cyclotomicArtinNormalization`.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

/-- The **global Kronecker–Weber theorem**: every finite abelian extension of `ℚ` embeds
in some cyclotomic field. Claim recorded ahead of its proof
([Milne 2020, Chap. I, §4, Thm. 4.16, p.49][MilneCFT]; Yamaguchi 2026,
`KroneckerWeber.lean:41`). -/
theorem globalKroneckerWeber (L : Type) [Field L] [NumberField L]
    [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧ Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) := by
  sorry

end Atlas.Knowledge
