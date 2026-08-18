import Mathlib
import Atlas.Knowledge.RayClassGroup
import Atlas.Knowledge.IdeleComponent
import Atlas.Knowledge.IdeleClassNormRange

/-!
# Hilbert class field

The two Hilbert class fields of a number field, as characterizations by their norm
subgroups: the *small* (wide) one belongs to the classes of ideles integral at every
finite place — its reciprocity quotient is the ideal class group, and it is the maximal
abelian extension unramified everywhere including the real places — and the *big*
(narrow) one to the congruence subgroup of the narrow zero modulus, positivity at every
real place. The recorded claims are the identification of the small quotient with
Mathlib's `ClassGroup (𝓞 K)` and the principal ideal theorem: every ideal of `𝓞 K`
becomes principal in a small Hilbert class field.

## Main definitions

* `integralAtFinitePlaces` — ideles integral at every finite place.
* `smallHilbertNormSubgroup`, `bigHilbertNormSubgroup` — the two norm subgroups.
* `IsSmallHilbertClassField`, `IsBigHilbertClassField` — the characterizations.

## Main statements

* `nonempty_smallHilbertQuotient_mulEquiv_classGroup` — `C_K` modulo the small subgroup
  is the ideal class group; recorded ahead of its proof.
* `isPrincipal_map_of_isSmallHilbertClassField` — the principal ideal theorem; recorded
  ahead of its proof.

## Implementation notes

The route to the class-group identification is the divisor map from finite ideles to
fractional ideals with kernel exactly `integralAtFinitePlaces` — the source's
`AlgebraicNumberTheory/Idele/IdealMap.lean:360, :379` and
`Idele/ClassGroup/Core.lean:147` — future work the claim records rather than imports. The
principal ideal theorem is stated on the predicate slot, in pure `Ideal.map` vocabulary;
its classical proof route is the Verlagerung through
`Atlas.Knowledge.AbelianizedGaloisTransfer`'s vocabulary, and Mathlib's
`ClassGroup.extendedHom_eq_one_of_forall_isPrincipal` is the ideal-theoretic bridge.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- Ideles **integral at every finite place**: every finite component is an integral unit
([Milne 2020, Chap. V, §3, Ex. 3.9, p.159][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/IdealMap.lean:374`][Yamaguchi2026]). -/
noncomputable def integralAtFinitePlaces : Subgroup (IdeleGroup K) :=
  ⨅ v : HeightOneSpectrum (𝓞 K),
    Subgroup.comap (finiteIdeleComponent K v) ((v.adicCompletionIntegers K).units)

/-- The **small Hilbert norm subgroup**: classes of ideles integral at every finite place
— the norm subgroup of the wide Hilbert class field
([Milne 2020, Chap. V, §3, Ex. 3.9, p.159][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/GlobalClassFields/SmallHilbertClassField.lean:29`]
[Yamaguchi2026]). -/
noncomputable def smallHilbertNormSubgroup : Subgroup (IdeleClassGroup K) :=
  Subgroup.map (QuotientGroup.mk' (principalIdeleSubgroup K))
    (integralAtFinitePlaces K ⊔ principalIdeleSubgroup K)

open scoped Classical in
/-- The **big Hilbert norm subgroup**: the congruence subgroup of the narrow zero modulus
— integrality at the finite places, positivity at every real place
([Milne 2020, Chap. V, §3, Exercise 3.14, p.160][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/GlobalClassFields/BigHilbertClassField.lean:26`]
[Yamaguchi2026]). -/
noncomputable def bigHilbertNormSubgroup : Subgroup (IdeleClassGroup K) :=
  congruenceSubgroup K ⟨0, Finset.univ⟩

/-- The **small (wide) Hilbert class field** characterization: norm subgroup the small
Hilbert subgroup — the maximal abelian extension unramified at every place, real places
included ([Milne 2020, Chap. V, §3, Ex. 3.9, p.159][MilneCFT];
[Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldRealization.lean:218`]
[Yamaguchi2026]). -/
def IsSmallHilbertClassField (M : Type*) [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] : Prop :=
  ideleClassNormRange K M = smallHilbertNormSubgroup K

/-- The **big (narrow) Hilbert class field** characterization: norm subgroup the narrow
zero modulus's congruence subgroup
([Milne 2020, Chap. V, §3, Exercise 3.14, p.160][MilneCFT];
[Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/HilbertClassFieldRealization.lean:88`]
[Yamaguchi2026]). -/
def IsBigHilbertClassField (M : Type*) [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] : Prop :=
  ideleClassNormRange K M = bigHilbertNormSubgroup K

/-- The idele class group modulo the small Hilbert subgroup is the ideal class group —
`Gal (H/K) ≅ Cl (K)` through reciprocity. Claim recorded ahead of its proof
([Milne 2020, Introduction, Thm. 0.4, p.4, and Chap. V, §3, Ex. 3.9, p.159][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/GlobalClassFields/SmallHilbertClassField.lean:38`]
[Yamaguchi2026]). -/
theorem nonempty_smallHilbertQuotient_mulEquiv_classGroup :
    Nonempty ((IdeleClassGroup K ⧸ smallHilbertNormSubgroup K) ≃* ClassGroup (𝓞 K)) := by
  sorry

/-- **The principal ideal theorem**: every ideal of `𝓞 K` becomes principal in a small
Hilbert class field. Claim recorded ahead of its proof
([Milne 2020, Chap. V, §3, Thm. 3.17, p.161][MilneCFT];
[Yamaguchi 2026,
`GlobalClassFieldTheory/IdealClassFieldTheory/SmallHilbertPrincipalization.lean:183`]
[Yamaguchi2026]). -/
theorem isPrincipal_map_of_isSmallHilbertClassField
    (M : Type*) [Field M] [NumberField M] [Algebra K M] [FiniteDimensional K M]
    (hM : IsSmallHilbertClassField K M) (I : Ideal (𝓞 K)) :
    (I.map (algebraMap (𝓞 K) (𝓞 M))).IsPrincipal := by
  sorry

end Atlas.Knowledge

end
