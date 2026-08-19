import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.IsProfiniteTransfer
import Atlas.Knowledge.MStepSolvableQuotient

/-!
# Tate-module system

The data the group-theoretic Tate module `Atlas.Knowledge.groupTateModule` is built over: a
decreasing sequence of open normal subgroups `H ν` of a topological group `G`, beginning at `G`
itself and with each step of finite index, such that the `ℓ ^ ν`-torsion of the topological
abelianization of `H ν` is a copy of `ℤ ⧸ ℓ ^ ν ℤ` and the quotient `G ⧸ H ν` is abelian,
together with a homomorphism
`V ν : (H ν)^ab → (H (ν + 1))^ab` for each step, descending the transfer—the source's unnamed
package of a sequence satisfying its conditions (i) and (ii) with the maps `Ver` between the
abelianizations of its consecutive terms. On the maximal `2`-step solvable quotient of the
absolute Galois group of a mixed-characteristic local field such a system exists at every
prime, which is the recorded claim; the module built over a system is
`Atlas.Knowledge.groupTateModule`, and the character it carries is
`Atlas.Knowledge.groupCyclotomicCharacter`.

## Main definitions

* `IsTateSystem` — the sequence conditions, the finite index of the steps, and the descent of
  the transfers.
* `IsTateSystem.ofSubgroupOf` — the homomorphism reading an element of `H.subgroupOf K` as an
  element of `H`, along which the transfer out of a level lands in the abelianization of the
  next level.

## Main statements

* `exists_isTateSystem` — over the maximal `2`-step solvable quotient of the absolute Galois
  group of a mixed-characteristic local field, a system exists at every prime. Claim recorded
  ahead of its proof.

## Implementation notes

The source's condition (ii), that `G ⧸ H ν` is abelian, is the field `commutator_le`: for a
normal subgroup the quotient is abelian exactly when the subgroup contains the commutator
subgroup, and the containment form needs no quotient group to state. Condition (i) reads the
`ℓ ^ ν`-torsion as the kernel of the `ℓ ^ ν`-power map of the abelianization, a subgroup since
the abelianization is commutative, and asks it to be isomorphic to `Multiplicative` of
`ZMod (ℓ ^ ν)`—the source's `(ℤ ⧸ ℓ^ν ℤ)₊` read multiplicatively. The `transfer` field is the
consumer device of `Atlas.Knowledge.IsProfiniteTransfer`: the transfer of `↥(H ν)` into its
open subgroup is not a construction but a characterization whose existence is that file's
recorded claim, so a system carries a witness `W` satisfying it. That characterization has
content exactly at finite index—its descent field sits behind a `FiniteIndex` binder—and
openness buys finite index only over a compact group, while the structure must elaborate over
carriers through which compactness does not synthesize, the note of
`Atlas.Knowledge.IsProfiniteTransfer`; so the finiteness of each step is the field
`finiteIndex`, over which the descent pins the value of `V ν` at every class, the argument of
`Atlas.Knowledge.IsProfiniteTransfer.unique`. Over a system the family `V` is therefore a
function of the sequence, which is what lets the recorded claims quantify over both. `W` lands
in the topological abelianization of `(H (ν + 1)).subgroupOf (H ν)`, the next level as a
subgroup of the current one; `V ν` is asked to be `W` followed by the map that `ofSubgroupOf`
induces between the abelianizations, which is `Atlas.Knowledge.mStepSolvableQuotient.map` at
`m = 1`. The prime `ℓ` is a bare natural: no field of the structure needs primality, the
local-field claims hypothesize it, and the degenerate values state exactly what they read—at
`ℓ = 1` the torsion condition is satisfied by every group, and at `ℓ = 0` it asks the
abelianizations of the positive levels to be copies of `ℤ`—so away from a prime nothing
meaningful is asserted, and nothing is claimed. The index begins at `ν = 0`, where the torsion
condition asks the `1`-torsion to be trivial, which every group satisfies.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

namespace IsTateSystem

variable {G : Type*} [Group G]

/-- The homomorphism reading an element of `H.subgroupOf K` as an element of `H`: membership in
the subgroup-of-a-subgroup is definitionally membership of the underlying element, so the map
carries no hypothesis—`Subgroup.subgroupOfEquivOfLe` asks for `H ≤ K` only to invert it. -/
def ofSubgroupOf {H K : Subgroup G} : ↥(H.subgroupOf K) →* ↥H where
  toFun z := ⟨↑↑z, z.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Reading an element of `H.subgroupOf K` as an element of `H` is continuous for the subtype
topologies. -/
theorem continuous_ofSubgroupOf [TopologicalSpace G] {H K : Subgroup G} :
    Continuous (ofSubgroupOf (H := H) (K := K)) :=
  Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _

end IsTateSystem

/-- A **Tate-module system** at `ℓ` on a topological group: a decreasing sequence `H ν` of open
normal subgroups beginning at the whole group, with each step of finite index, whose topological
abelianizations have `ℓ ^ ν`-torsion a copy of `ℤ ⧸ ℓ ^ ν ℤ` and abelian quotients, together
with homomorphisms between the abelianizations of consecutive terms descending the transfer
([Hyeon 2025, §3, p.11][Hyeon2025], the sequence with conditions (i) and (ii);
[Hyeon 2025, §3, p.12][Hyeon2025], the maps `Ver` between the abelianizations). -/
structure IsTateSystem (ℓ : ℕ) (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (H : ℕ → Subgroup G)
    (V : ∀ ν, TopologicalAbelianization ↥(H ν) →* TopologicalAbelianization ↥(H (ν + 1))) :
    Prop where
  /-- The sequence begins at the whole group. -/
  zero_eq_top : H 0 = ⊤
  /-- The sequence is decreasing. -/
  le_succ : ∀ ν, H (ν + 1) ≤ H ν
  /-- Every term is open. -/
  isOpen : ∀ ν, IsOpen (H ν : Set G)
  /-- Every term is normal, so that the group acts on it by conjugation. -/
  normal : ∀ ν, (H ν).Normal
  /-- Every step has finite index in the previous level: over a compact group this follows from
  openness, but the structure elaborates over carriers through which compactness does not
  synthesize, and without it the descent of the transfer would have no content. -/
  finiteIndex : ∀ ν, ((H (ν + 1)).subgroupOf (H ν)).FiniteIndex
  /-- The source's condition (i): the `ℓ ^ ν`-torsion of the topological abelianization of the
  `ν`th term—the kernel of its `ℓ ^ ν`-power map—is a copy of `ℤ ⧸ ℓ ^ ν ℤ`, read
  multiplicatively. -/
  torsion : ∀ ν, Nonempty
    (↥((powMonoidHom (ℓ ^ ν) : TopologicalAbelianization ↥(H ν)
        →* TopologicalAbelianization ↥(H ν)).ker)
      ≃* Multiplicative (ZMod (ℓ ^ ν)))
  /-- The source's condition (ii): the quotient by every term is abelian, stated as the term
  containing the commutator subgroup. -/
  commutator_le : ∀ ν, commutator G ≤ H ν
  /-- Each `V ν` descends the transfer of the `ν`th level into the next: it is a witness of
  `Atlas.Knowledge.IsProfiniteTransfer` followed by the passage from the abelianization of
  `(H (ν + 1)).subgroupOf (H ν)` to that of `H (ν + 1)` along `IsTateSystem.ofSubgroupOf`. -/
  transfer : ∀ ν, ∃ W : TopologicalAbelianization ↥(H ν)
        →* TopologicalAbelianization ↥((H (ν + 1)).subgroupOf (H ν)),
      IsProfiniteTransfer ↥(H ν) ((H (ν + 1)).subgroupOf (H ν)) W ∧
      V ν = (mStepSolvableQuotient.map 1 IsTateSystem.ofSubgroupOf
        IsTateSystem.continuous_ofSubgroupOf).comp W

/-- Over the maximal `2`-step solvable quotient of the absolute Galois group of a
mixed-characteristic local field, a Tate-module system exists at every prime: the source takes
the subgroups fixing the fields `K (ζ_{ℓ ^ ν})` inside the maximal `2`-step solvable extension,
and the transfers exist by `Atlas.Knowledge.exists_isProfiniteTransfer`. Claim recorded ahead
of its proof ([Hyeon 2025, §3, p.11][Hyeon2025]). -/
theorem exists_isTateSystem (ℓ : ℕ) [Fact ℓ.Prime] (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] :
    ∃ (H : ℕ → Subgroup (mStepSolvableQuotient (Field.absoluteGaloisGroup K) 2))
      (V : ∀ ν, TopologicalAbelianization ↥(H ν) →* TopologicalAbelianization ↥(H (ν + 1))),
      IsTateSystem ℓ (mStepSolvableQuotient (Field.absoluteGaloisGroup K) 2) H V := by
  sorry

end Atlas.Knowledge
