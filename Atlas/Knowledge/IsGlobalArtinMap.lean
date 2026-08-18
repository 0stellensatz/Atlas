import Mathlib
import Atlas.Knowledge.MaximalAbelianExtension
import Atlas.Knowledge.FinitePlaceIdele
import Atlas.Knowledge.IdeleClassIdentityComponent

/-!
# global Artin map

The global reciprocity map of a number field, as a characterization: a continuous
homomorphism `φ : C_K →ₜ* Gal (K^ab/K)` is a global Artin map when it carries the
arithmetic Frobenius normalization — for every finite subextension `L` of the maximal
abelian extension in which a finite place `v` is unramified, the class of a one-place
uniformizer idele at `v` restricts to the arithmetic Frobenius at every prime of `L` over
`v`. Principal triviality is not a field of the predicate because the domain is already
the idele class group. The map itself is the whole content of global class field theory
and is not constructed; existence, uniqueness, surjectivity, the identification of the
kernel with Phase 4's identity component, and the infinite abelian class-field
correspondence are the recorded claims.

## Main definitions

* `IsGlobalArtinMap` — the arithmetic Frobenius normalization on one-place uniformizer
  classes.

## Main statements

* `exists_isGlobalArtinMap`, `IsGlobalArtinMap.unique` — recorded ahead of their proofs.
* `IsGlobalArtinMap.surjective`, `IsGlobalArtinMap.ker_eq` — the exact sequence
  `1 → C_K° → C_K → Gal (K^ab/K) → 1`; recorded ahead of their proofs.
* `nonempty_infiniteAbelianClassFieldCorrespondence` — closed subgroups of `C_K / C_K°`
  against intermediate fields of `K^ab`, order-reversing; recorded ahead of its proof.

## Implementation notes

The normalization is Milne's and Phase 2's arithmetic convention: uniformizer to
*arithmetic* Frobenius, rendered by Mathlib's `Valuation.IsUniformizer` (a value strictly
below one generating the value group — Serre's side of the convention) and
`IsArithFrobAt` on the ring of integers of
the subextension, with every instance synthesizing — the `NumberField` structure of a
finite subextension enters by `NumberField.of_module_finite` in statement position, the
source's own idiom. The source's infinite-level map
(`GlobalClassFieldTheory/Reciprocity/MaximalAbelianGlobalArtin.lean:24`) is the
*geometric* normalization — its arithmetic form exists only at finite level, by
composition with inversion (`Reciprocity/ArithmeticNormalization.lean:105`, convention
docstring at `:4`) — so a port of its infinite-level statements into this vocabulary
composes with inversion; its cyclotomic computations, in the top-level
`KroneckerWeber/RationalCyclotomicArithmeticReciprocity.lean:112`, pin the same
convention this predicate states. Unramifiedness is `Algebra.IsUnramifiedAt (𝓞 K)` at
every prime over `v`, Mathlib's locus vocabulary.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [NeukirchEtAl2008] J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of number fields*,
  Grundlehren der mathematischen Wissenschaften **323**, Springer Berlin Heidelberg, 2008.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField WithZero
open NumberField IsDedekindDomain

noncomputable section

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- The **global Artin map** characterization: `φ` carries the arithmetic Frobenius
normalization — at every finite abelian floor unramified over `v`, the class of a
one-place uniformizer idele restricts to arithmetic Frobenius at every prime over `v`
([Milne 2020, Chap. I, §1, Thm. 1.1 (a), p.20, Chap. V, §3, p.156, and §5, Prop. 5.2,
p.178][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/MaximalAbelianGlobalArtin.lean:24`,
geometric normalization, inverse of this one][Yamaguchi2026]). -/
def IsGlobalArtinMap
    (φ : IdeleClassGroup K →ₜ*
      (maximalAbelianExtension K ≃ₐ[K] maximalAbelianExtension K)) : Prop :=
  ∀ (L : FiniteGaloisIntermediateField K (maximalAbelianExtension K))
    (v : HeightOneSpectrum (𝓞 K)) (π : (v.adicCompletion K)ˣ),
    (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).IsUniformizer
      (π : v.adicCompletion K) →
    letI : NumberField L := NumberField.of_module_finite K L
    (∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
      Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) →
    ∀ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal →
      IsArithFrobAt (𝓞 K)
        (AlgEquiv.restrictNormalHom L (φ (finitePlaceIdeleClass v π))) w.asIdeal

/-- A global Artin map exists. Claim recorded ahead of its proof
([Milne 2020, Chap. V, §5, Prop. 5.2, p.178][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/MaximalAbelianGlobalArtin.lean:24`]
[Yamaguchi2026]). -/
theorem exists_isGlobalArtinMap : ∃ φ, IsGlobalArtinMap K φ := by
  sorry

/-- The normalization pins the map: two global Artin maps agree. Claim recorded ahead of
its proof ([Milne 2020, Chap. V, §5, Prop. 5.2, p.178][MilneCFT]). -/
theorem IsGlobalArtinMap.unique
    {φ ψ : IdeleClassGroup K →ₜ*
      (maximalAbelianExtension K ≃ₐ[K] maximalAbelianExtension K)}
    (hφ : IsGlobalArtinMap K φ) (hψ : IsGlobalArtinMap K ψ) : φ = ψ := by
  sorry

/-- The global Artin map is surjective. Claim recorded ahead of its proof
([Neukirch–Schmidt–Wingberg 2008, Chap. VIII, §2, (8.2.2), p.445][NeukirchEtAl2008];
[Milne 2020, Chap. V, §5, Rem. 5.7 (a), p.179][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/MaximalAbelianGlobalArtin.lean:58`]
[Yamaguchi2026]). -/
theorem IsGlobalArtinMap.surjective
    {φ : IdeleClassGroup K →ₜ*
      (maximalAbelianExtension K ≃ₐ[K] maximalAbelianExtension K)}
    (hφ : IsGlobalArtinMap K φ) : Function.Surjective φ := by
  sorry

/-- The kernel of the global Artin map is the identity component of the idele class
group: the exact sequence `1 → C_K° → C_K → Gal (K^ab/K) → 1`. Claim recorded ahead of
its proof
([Neukirch–Schmidt–Wingberg 2008, Chap. VIII, §2, (8.2.2), p.445][NeukirchEtAl2008];
[Milne 2020, Chap. V, §5, Rem. 5.7 (a), p.179][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/MaximalAbelianKernel.lean:123`]
[Yamaguchi2026]). -/
theorem IsGlobalArtinMap.ker_eq
    {φ : IdeleClassGroup K →ₜ*
      (maximalAbelianExtension K ≃ₐ[K] maximalAbelianExtension K)}
    (hφ : IsGlobalArtinMap K φ) :
    MonoidHom.ker φ.toMonoidHom = ideleClassIdentityComponent K := by
  sorry

/-- The **infinite abelian class-field correspondence**: closed subgroups of the
component quotient `C_K / C_K°` against intermediate fields of `K^ab`, order-reversing.
Claim recorded ahead of its proof — the finite-level bijection this is the profinite
limit of is Milne's corollary
([Milne 2020, Chap. V, §5, Cor. 5.6, p.179][MilneCFT];
[Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/InfiniteAbelianClassFieldCorrespondence.lean:100`]
[Yamaguchi2026]). -/
theorem nonempty_infiniteAbelianClassFieldCorrespondence :
    Nonempty ((ClosedSubgroup (ideleClassComponentQuotient K))ᵒᵈ ≃o
      IntermediateField K (maximalAbelianExtension K)) := by
  sorry

end Atlas.Knowledge

end
