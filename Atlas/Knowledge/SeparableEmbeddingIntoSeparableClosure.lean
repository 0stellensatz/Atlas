import Mathlib

/-!
# separable embedding into the separable closure

A chosen embedding of a separable extension into the separable closure
of its base field — Mathlib's `IsSepClosed.lift` under the name the
concrete realization of finite Galois extensions builds on (#104).

## Main definitions

* `separableEmbeddingIntoSeparableClosure` — the chosen embedding.

## Implementation notes

The source file's `continuous_algEquiv_autCongr` and its two
number-field declarations are not taken: the continuity lemma's only
consumer is the global theory's `CyclotomicZHatBaseChange.lean`, and
the number-field pair is global-theory packaging, none of it on the
local reciprocity path. The declaration ports token-for-token; the
source is `AlgebraicNumberTheory/SeparableClosureEmbedding.lean`.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [Algebra.IsSeparable K L]

/-- **A chosen embedding of a separable extension into the separable
closure of its base field** (Yamaguchi 2026,
`AlgebraicNumberTheory/SeparableClosureEmbedding.lean:56`). -/
noncomputable def separableEmbeddingIntoSeparableClosure :
    L →ₐ[K] SeparableClosure K :=
  IsSepClosed.lift

end

end Atlas.Knowledge
