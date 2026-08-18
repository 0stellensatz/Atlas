import Mathlib
import Atlas.Knowledge.IdeleClassGroup

/-!
# identity component of the idele class group

The connected component of the identity in `C_K`, as a subgroup: the closure of the
archimedean positive blocks times the principal ideles, and — the reason it is vocabulary
worth naming — the kernel of the global reciprocity map, so that `C_K / C_K°` is the Galois
group of the maximal abelian extension. That last statement is Phase 5's; this item is the
component itself, its closedness, and the component quotient the reciprocity map will factor
through. Everything here is proved: the component subgroup is Mathlib's
`Subgroup.connectedComponentOfOne`, and components are closed in any topological space.

## Main definitions

* `ideleClassIdentityComponent` — `C_K°` as a `Subgroup (IdeleClassGroup K)`.
* `ideleClassComponentQuotient` — `C_K / C_K°`.

## Main statements

* `ideleClassIdentityComponent_isClosed` — the component is closed.
* `coe_ideleClassIdentityComponent` — the carrier is `connectedComponent 1`,
  definitionally.

## Implementation notes

The topological group structure on `C_K` that `Subgroup.connectedComponentOfOne` needs
synthesizes from the openness `Fact` of `Atlas.Knowledge.IdeleGroup` through the quotient
instances; nothing is constructed here. Milne describes the component concretely as the
closure of `K^× · ∏_{v | ∞} K_v^+` in the ideles, image in `C_K`; that identification is a
statement about the reciprocity kernel and stays with Phase 5, not with the definition.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField
open NumberField

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- The **identity component** `C_K°` of the idele class group, as a subgroup
([Milne 2020, Chap. V, §5, Rem. 5.7 (a), p.179, and Introduction, pp.11–12][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/IdentityComponent.lean:20`][Yamaguchi2026]). -/
noncomputable def ideleClassIdentityComponent : Subgroup (IdeleClassGroup K) :=
  Subgroup.connectedComponentOfOne (IdeleClassGroup K)

/-- The carrier of the identity component is the connected component of `1`,
definitionally ([Milne 2020, Chap. V, §5, Rem. 5.7 (a), p.179][MilneCFT]). -/
theorem coe_ideleClassIdentityComponent :
    (ideleClassIdentityComponent K : Set (IdeleClassGroup K)) =
      connectedComponent (1 : IdeleClassGroup K) :=
  rfl

/-- The identity component is closed — components are closed, and this is what lets the
reciprocity kernel of Phase 5 contain the closure Milne describes
([Milne 2020, Chap. V, §5, Rem. 5.7 (a), p.179][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/IdentityComponent.lean:30`][Yamaguchi2026]). -/
theorem ideleClassIdentityComponent_isClosed :
    IsClosed (ideleClassIdentityComponent K : Set (IdeleClassGroup K)) :=
  isClosed_connectedComponent

/-- The **component quotient** `C_K / C_K°` — the group global reciprocity identifies with
the Galois group of the maximal abelian extension, in Phase 5's vocabulary
([Milne 2020, Introduction, pp.11–12][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/IdentityComponent.lean:40`][Yamaguchi2026]). -/
abbrev ideleClassComponentQuotient : Type _ :=
  IdeleClassGroup K ⧸ ideleClassIdentityComponent K

end Atlas.Knowledge
