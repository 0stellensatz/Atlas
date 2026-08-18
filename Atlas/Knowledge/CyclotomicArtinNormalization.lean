import Mathlib
import Atlas.Knowledge.FinitePlaceIdele
import Atlas.Knowledge.IdeleClassGroup
import Atlas.Knowledge.IsGlobalArtinMap
import Atlas.Knowledge.MaximalAbelianExtension

/-!
# cyclotomic Artin normalization

The global Artin map computed on a cyclotomic field: on a floor of `ℚ`'s maximal abelian
extension that is a cyclotomic extension of level `m`, any global Artin map sends the
class of a one-place uniformizer idele at a prime `q` not dividing `m` to an
automorphism whose restriction to the floor is `ζ ↦ ζ ^ q` — Milne's
`(p, ℚ[ζₘ]/ℚ) = [p]`, stated through Mathlib's
`IsCyclotomicExtension.Rat.galEquivZMod` as one equation in `(ZMod m)ˣ`. This is the
normalization that gives Kronecker–Weber its class-field meaning: which automorphism each
unramified prime induces on the cyclotomic field containing a given abelian extension.
The claim quantifies over `Atlas.Knowledge.IsGlobalArtinMap`'s characterization and is
recorded ahead of its proof.

## Main statements

* `cyclotomicArtinNormalization` — recorded ahead of its proof.

## Implementation notes

The statement is nonvacuous — `ℚ(ζₘ)` is abelian over `ℚ`, so level-`m` floors exist —
and true of every such floor: `q ∤ m` keeps every prime over `q` unramified, the Artin
characterization then makes the restricted automorphism an arithmetic Frobenius at each
of them, and reduction is injective on `m`-th roots of unity at primes away from `m`,
which pins the `galEquivZMod` class to `[q]`. The source's transported definition — the
Frobenius as a `Gal` element built from its own reciprocity map
(`KroneckerWeber/RationalRayClassFieldCyclotomic.lean:492`) — is subsumed rather than
ported: the source *constructs* the reciprocity value where Atlas *characterizes* it, as
`Atlas.Knowledge.IsFinitePlaceHilbertSymbol` does for the local symbol, so the
characterization-only Artin layer already names the transported automorphism as a
restriction. The statement's shape moves once against the source: the source computes on
the concrete `CyclotomicField m ℚ`, where this claim quantifies over the level-`m`
floors of `ℚ^ab` — the form the restriction vocabulary forces — and neither statement
implies the other without identifying `CyclotomicField m ℚ` with such a floor. Two
`letI` bindings sit in statement position because pinned Mathlib fails to *synthesize*
`Normal` and `NumberField` for a `FiniteGaloisIntermediateField` floor at `K := ℚ`,
though the instance values themselves typecheck and `FiniteDimensional` synthesizes
fine; the `NumberField` binding is `Atlas.Knowledge.IsGlobalArtinMap`'s own idiom, which
at generic `K` needs no other. Milne's Introduction statement restricts `m` to
be odd or divisible by `4`; `galEquivZMod` needs no such restriction, so neither does
this statement.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField WithZero
open NumberField IsDedekindDomain

namespace Atlas.Knowledge

/-- The **cyclotomic Artin normalization**: on a level-`m` cyclotomic floor of `ℚ`'s
maximal abelian extension, a global Artin map sends the class of a one-place uniformizer
idele at a prime `q ∤ m` to an automorphism restricting on the floor to `ζ ↦ ζ ^ q`.
Claim recorded ahead of its proof
([Milne 2020, Introduction, p.7, and Chap. V, §3, Ex. 3.2, p.157][MilneCFT];
[Yamaguchi 2026, `KroneckerWeber/RationalRayClassFieldCyclotomic.lean:510`, transported
definition at `:492`][Yamaguchi2026]). -/
theorem cyclotomicArtinNormalization
    {φ : IdeleClassGroup ℚ →ₜ*
      (maximalAbelianExtension ℚ ≃ₐ[ℚ] maximalAbelianExtension ℚ)}
    (hφ : IsGlobalArtinMap ℚ φ) (m : ℕ) [NeZero m]
    (L : FiniteGaloisIntermediateField ℚ (maximalAbelianExtension ℚ))
    [IsCyclotomicExtension {m} ℚ L]
    (q : ℕ) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v.asIdeal = Ideal.span {(q : 𝓞 ℚ)})
    (π : (v.adicCompletion ℚ)ˣ)
    (hπ : (Valued.v : Valuation (v.adicCompletion ℚ) ℤᵐ⁰).IsUniformizer
      (π : v.adicCompletion ℚ)) :
    letI : Normal ℚ L := L.isGalois.to_normal
    letI : NumberField L := NumberField.of_module_finite ℚ L
    IsCyclotomicExtension.Rat.galEquivZMod m L
        (AlgEquiv.restrictNormalHom L (φ (finitePlaceIdeleClass v π))) =
      ZMod.unitOfCoprime q (hq.coprime_iff_not_dvd.mpr hqm) := by
  sorry

end Atlas.Knowledge
