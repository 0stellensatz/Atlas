import Mathlib
import Atlas.Knowledge.FiniteAbstractExtension

/-!
# finite tower of abstract extensions

A composable tower of abstract extensions with both adjacent relative quotients
finite, carried by the object — so downstream norm and degree laws do not thread
containments and finiteness instances as independent arguments. The two stages
are exposed as finite abstract extensions.

## Main definitions

* `FiniteTower` — the tower with its two finiteness certificates,
  `finiteTopQuotient` and `finiteBaseQuotient`.
* `FiniteTower.topExtension` / `FiniteTower.baseExtension` — the stages as
  finite abstract extensions.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **A finite tower of abstract extensions**: the two adjacent finite-quotient
proofs belong to the tower object
([Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Fields.lean:908`][Yamaguchi2026]). -/
structure FiniteTower (G : Type*) [Group G] [TopologicalSpace G]
    extends AbstractExtension.Tower G where
  /-- The quotient for the top-to-middle extension is finite. -/
  finiteTopQuotient : Finite toTower.topExtension.quotient
  /-- The quotient for the middle-to-base extension is finite. -/
  finiteBaseQuotient : Finite toTower.baseExtension.quotient

namespace FiniteTower

variable (T : FiniteTower G)

/-- The upper relative quotient in a finite tower is finite. -/
instance topQuotientFinite :
    Finite (T.middle.toSubgroup ⧸
      T.top.toSubgroup.subgroupOf T.middle.toSubgroup) :=
  T.finiteTopQuotient

/-- The lower relative quotient in a finite tower is finite. -/
instance baseQuotientFinite :
    Finite (T.base.toSubgroup ⧸
      T.middle.toSubgroup.subgroupOf T.base.toSubgroup) :=
  T.finiteBaseQuotient

/-- The upper finite extension of a finite tower. -/
def topExtension : FiniteAbstractExtension G where
  toAbstractExtension := T.toTower.topExtension
  finiteQuotient := T.finiteTopQuotient

/-- The lower finite extension of a finite tower. -/
def baseExtension : FiniteAbstractExtension G where
  toAbstractExtension := T.toTower.baseExtension
  finiteQuotient := T.finiteBaseQuotient

end FiniteTower

end Atlas.Knowledge
