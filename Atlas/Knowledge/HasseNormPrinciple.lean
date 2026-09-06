import Mathlib
import Atlas.Knowledge.IdeleComponent
import Atlas.Knowledge.PrincipalIdele

/-!
# Hasse norm principle

Hasse's norm theorem for cyclic extensions: an element of `Kˣ` is a global norm from `L`
exactly when its principal idele is a norm at every place. The two sides are subgroups of
`Kˣ` — the range of the field norm, and the comap along the diagonal of the everywhere-
local norm conditions, each local condition the tensor-model norm at one place. The
statement is Mathlib vocabulary throughout; the equality is the recorded claim, and it is
cyclicity that carries it — Milne's `ℚ [√13, √17]` example breaks the biquadratic case.

## Main definitions

* `allFinitePlaceLocalNormCondition`, `allInfinitePlaceLocalNormCondition` — the local
  norm conditions on ideles, as infima of comaps along the component projections.
* `globalNormSubgroup`, `everywhereLocalNormSubgroup` — the two sides of the principle.

## Main statements

* `hasseNormPrinciple_cyclic` — the two sides agree for finite cyclic extensions;
  recorded ahead of its proof.

## Implementation notes

The local conditions are the tensor form at both kinds of places: `Units.map` of
`Algebra.norm (K_v)` on `(K_v ⊗[K] L)ˣ`, base change synthesizing the module structure
from `[FiniteDimensional K L]`. At the archimedean places this is the source's own shape
(`GlobalClassFieldTheory/ClassFieldAxiom/HasseNormPrinciple.lean:370`); at the finite
places the source uses its chosen-completion subgroups and proves them equal to the tensor
form (`AlgebraicNumberTheory/Idele/Relative/FinitePlaceTensorNorm.lean:162`), so this
item states the Mathlib-native side of that equality.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]
variable (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]

/-- The **finite-place local norm conditions**: at every finite place, the component is a
norm from `K_v ⊗[K] L` ([Milne 2020, Chap. VIII, §3, Thm. 3.1, p.234][MilneCFT];
Yamaguchi 2026,
`GlobalClassFieldTheory/ClassFieldAxiom/IdelePowerLocalUnitNormContainment.lean:121`, on
chosen completions). -/
noncomputable def allFinitePlaceLocalNormCondition : Subgroup (IdeleGroup K) :=
  ⨅ v : HeightOneSpectrum (𝓞 K),
    Subgroup.comap (finiteIdeleComponent K v)
      (MonoidHom.range (Units.map
        (Algebra.norm (v.adicCompletion K) :
          (v.adicCompletion K ⊗[K] L) →* v.adicCompletion K)))

/-- The **archimedean local norm conditions**: at every infinite place, the component is
a norm from `K_v ⊗[K] L` ([Milne 2020, Chap. VIII, §3, Thm. 3.1, p.234][MilneCFT];
Yamaguchi 2026, `GlobalClassFieldTheory/ClassFieldAxiom/HasseNormPrinciple.lean:370`). -/
noncomputable def allInfinitePlaceLocalNormCondition : Subgroup (IdeleGroup K) :=
  ⨅ v : InfinitePlace K,
    Subgroup.comap (infiniteIdeleComponent K v)
      (MonoidHom.range (Units.map
        (Algebra.norm v.Completion : (v.Completion ⊗[K] L) →* v.Completion)))

/-- The **global norms**: the range of the field norm on units
([Milne 2020, Chap. VIII, §3, Thm. 3.1, p.234][MilneCFT];
Yamaguchi 2026,
`GlobalClassFieldTheory/ClassFieldAxiom/HasseNormPrinciple.lean:463`). -/
noncomputable def globalNormSubgroup : Subgroup Kˣ :=
  MonoidHom.range (Units.map (Algebra.norm K : L →* K))

/-- The **everywhere-local norms**: field units whose principal idele satisfies every
local norm condition ([Milne 2020, Chap. VIII, §3, Thm. 3.1, p.234][MilneCFT];
Yamaguchi 2026,
`GlobalClassFieldTheory/ClassFieldAxiom/HasseNormPrinciple.lean:472`). -/
noncomputable def everywhereLocalNormSubgroup : Subgroup Kˣ :=
  Subgroup.comap (principalIdele K)
    (allFinitePlaceLocalNormCondition K L ⊓ allInfinitePlaceLocalNormCondition K L)

/-- **Hasse's norm theorem**: for a finite cyclic extension, the global norms are exactly
the everywhere-local norms. Claim recorded ahead of its proof — and cyclicity is
load-bearing: `5²` is an everywhere-local but not global norm from `ℚ (√13, √17)`
([Milne 2020, Chap. VIII, §3, Thm. 3.1 and Rem. 3.2, p.234][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/ClassFieldAxiom/HasseNormPrinciple.lean:1337`). -/
theorem hasseNormPrinciple_cyclic [IsGalois K L] [IsCyclic (L ≃ₐ[K] L)] :
    globalNormSubgroup K L = everywhereLocalNormSubgroup K L := by
  sorry

end Atlas.Knowledge

end
