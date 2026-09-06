import Mathlib
import Atlas.Knowledge.IsGlobalArtinMap
import Atlas.Knowledge.IdeleClassNormRange

/-!
# global reciprocity law

Finite-level global reciprocity: the Artin map induces `C_K / N_{L/K} (C_L) ≅ Gal (L/K)`
for every finite abelian extension, and `Gal (L/K)ᵃᵇ ≅ C_K / N_{L/K} (C_L)` for every
finite Galois one. Both are recorded claims: the first in the normalized form — the
kernel of the Artin map restricted to a finite abelian floor is exactly the norm
subgroup, so the isomorphism is `φ`'s and not an abstract one — and the second as the
existence of the isomorphism for a Galois extension given abstractly, where no restriction
of `φ` is available to carry the normalization.

## Main statements

* `globalReciprocity_ker` — the restricted Artin map has kernel the norm subgroup,
  recorded ahead of its proof.
* `globalReciprocity_abelianization` — `Gal (L/K)ᵃᵇ ≅ C_K / N_{L/K} (C_L)` for finite
  Galois `L/K`, recorded ahead of its proof.

## Implementation notes

The Galois-form claim is a plain `≃*`, deliberately: both sides are finite discrete, so
the topological form adds nothing, and stating it topologically would require the local-instance
re-declarations of the quotient topology on `Abelianization` the source carries
(`GlobalClassFieldTheory/Reciprocity/ArithmeticNormalization.lean:49`). The source's
finite-level equivalence is arithmetically normalized by composing its geometric one with
inversion (`:140`, via `:105`); the kernel statement here needs no such step because the
predicate of `Atlas.Knowledge.IsGlobalArtinMap` is arithmetic from the start.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [NeukirchEtAl2008] J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of number fields*,
  Grundlehren der mathematischen Wissenschaften **323**, Springer Berlin Heidelberg, 2008.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open scoped NumberField
open NumberField

noncomputable section

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- **Finite-level reciprocity, normalized**: the Artin map restricted to a finite
subextension of `K^ab` has kernel exactly the norm subgroup — `φ` itself induces
`C_K / N_{L/K} (C_L) ≅ Gal (L/K)`. Claim recorded ahead of its proof
([Milne 2020, Chap. V, §5, Thm. 5.3, pp.178–179][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/Reciprocity/ArithmeticNormalization.lean:140`). -/
theorem globalReciprocity_ker
    {φ : IdeleClassGroup K →ₜ*
      (maximalAbelianExtension K ≃ₐ[K] maximalAbelianExtension K)}
    (hφ : IsGlobalArtinMap K φ)
    (L : FiniteGaloisIntermediateField K (maximalAbelianExtension K)) :
    MonoidHom.ker ((AlgEquiv.restrictNormalHom L).comp φ.toMonoidHom) =
      ideleClassNormRange K L := by
  sorry

/-- **Finite-level reciprocity, Galois form**: `Gal (L/K)ᵃᵇ ≅ C_K / N_{L/K} (C_L)` for a
finite Galois extension. Claim recorded ahead of its proof
([Neukirch–Schmidt–Wingberg 2008, Chap. VIII, §1, (8.1.23), p.441][NeukirchEtAl2008];
[Milne 2020, Chap. V, §5, Thm. 5.3, pp.178–179][MilneCFT];
Yamaguchi 2026,
`GlobalClassFieldTheory/Reciprocity/ArithmeticNormalization.lean:140`). -/
theorem globalReciprocity_abelianization (L : Type*) [Field L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    Nonempty (Abelianization (L ≃ₐ[K] L) ≃*
      (IdeleClassGroup K ⧸ ideleClassNormRange K L)) := by
  sorry

end Atlas.Knowledge

end
