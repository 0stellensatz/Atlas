import Mathlib
import Atlas.Knowledge.IdeleGroup

/-!
# principal idele

The diagonal embedding of the multiplicative group of a number field into its idele group:
a field unit placed in every completion at once, archimedean and finite. The map is
injective — the ideles remember the field — and its range is the subgroup of principal
ideles, the `K^×` the idele class group divides out. Both facts are proved here; nothing in
this file is recorded.

## Main definitions

* `principalIdele` — the diagonal `Kˣ →* 𝕀_K`.
* `principalIdeleSubgroup` — its range, the principal ideles.

## Main statements

* `principalIdele_injective` — the diagonal is injective, through the archimedean factor.

## Implementation notes

The finite half goes through the algebra map into the finite adele ring and then Mathlib's
`RestrictedProduct.unitsEquiv`, so that evaluating a principal idele at a finite place is
definitionally the local embedding of the field element — the content computation of
`Atlas.Knowledge.ideleContent` leans on that transparency. Injectivity needs only the
archimedean factor: the algebra map of a field into the nonempty product of its archimedean
completions is injective.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def finiteUnitsEquiv :
    (FiniteAdeleRing (𝓞 K) K)ˣ ≃*
      Πʳ v : HeightOneSpectrum (𝓞 K),
        [(v.adicCompletion K)ˣ, (v.adicCompletionIntegers K).units] :=
  RestrictedProduct.unitsEquiv (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)

/-- The **principal idele** of a field unit: the diagonal embedding `Kˣ →* 𝕀_K`, the field
placed in all of its completions at once
([Milne 2020, Chap. V, §4, 4.2, p.170][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/PrincipalCore.lean:21`][Yamaguchi2026]). -/
noncomputable def principalIdele : Kˣ →* IdeleGroup K :=
  (Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom).prod
    ((finiteUnitsEquiv K).toMonoidHom.comp
      (Units.map (algebraMap K (FiniteAdeleRing (𝓞 K) K)).toMonoidHom))

/-- The diagonal is injective: a field unit is recovered from the archimedean factor
([Milne 2020, Chap. V, §4, 4.2, p.170][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/PrincipalCore.lean:48`][Yamaguchi2026]). -/
theorem principalIdele_injective : Function.Injective (principalIdele K) := by
  intro x y h
  have h1 : Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom x
      = Units.map (algebraMap K (InfiniteAdeleRing K)).toMonoidHom y :=
    congrArg Prod.fst h
  exact Units.ext ((algebraMap K (InfiniteAdeleRing K)).injective
    (congrArg Units.val h1))

/-- The subgroup of **principal ideles**, the range of the diagonal — the `K^×` the idele
class group divides out ([Milne 2020, Chap. V, §4, p.171][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/PrincipalCore.lean:55`][Yamaguchi2026]). -/
noncomputable def principalIdeleSubgroup : Subgroup (IdeleGroup K) :=
  MonoidHom.range (principalIdele K)

end Atlas.Knowledge
