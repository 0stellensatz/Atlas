import Mathlib
import Atlas.Knowledge.IdeleGroup

/-!
# idele component

The component projections of the idele group: evaluation of an idele at one finite place
and at one archimedean place, as monoid homomorphisms. They are the counterpart of the
one-place inclusions of `Atlas.Knowledge.FinitePlaceIdele` — local conditions on global
elements are comaps along these maps, and the everywhere-local norm conditions of
`Atlas.Knowledge.HasseNormPrinciple` and the integrality conditions of
`Atlas.Knowledge.HilbertClassField` are exactly such comaps. Everything here is proved.

## Main definitions

* `finiteIdeleComponent` — `𝕀_K →* (v.adicCompletion K)ˣ`.
* `infiniteIdeleComponent` — `𝕀_K →* (v.Completion)ˣ`.

## Implementation notes

The finite projection is Mathlib's restricted-product evaluation after the second
projection, definitionally `a.2 v`; the archimedean one is the units map of the `Pi`
evaluation after the first. The source carries the same maps as `finiteComponent` and
`infiniteComponent` (`AlgebraicNumberTheory/Idele/Basic.lean:114, :109`).

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- The **finite component** of an idele: evaluation at one finite place, definitionally
`a.2 v` ([Milne 2020, Chap. V, §4, p.169][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/Basic.lean:114`][Yamaguchi2026]). -/
noncomputable def finiteIdeleComponent (v : HeightOneSpectrum (𝓞 K)) :
    IdeleGroup K →* (v.adicCompletion K)ˣ :=
  (RestrictedProduct.evalMonoidHom _ v).comp (MonoidHom.snd _ _)

/-- The **archimedean component** of an idele: evaluation at one infinite place
([Milne 2020, Chap. V, §4, p.169][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/Basic.lean:109`][Yamaguchi2026]). -/
noncomputable def infiniteIdeleComponent (v : InfinitePlace K) :
    IdeleGroup K →* v.Completionˣ :=
  (Units.map (Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) v).toMonoidHom).comp
    (MonoidHom.fst _ _)

end Atlas.Knowledge

end
