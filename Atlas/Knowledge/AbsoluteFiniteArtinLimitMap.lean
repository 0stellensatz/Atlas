import Mathlib
import Atlas.Knowledge.AbsoluteFiniteArtinLimit
import Atlas.Knowledge.AbsoluteFiniteArtinMap
import Atlas.Knowledge.AbsoluteFiniteQuotientTransition

/-!
# absolute finite Artin limit map

The finite Artin coordinates of a mixed-characteristic local field
commute with quotient transition, so they assemble into a single
homomorphism from `Kˣ` into the inverse limit of the finite quotients
of the abelianized absolute Galois group — the compatible cone — and
surjectivity at every coordinate makes its range dense in the limit
topology (#104).

## Main definitions

* `absoluteFiniteArtinLimitMap` — the finite Artin coordinates
  assembled into the inverse limit.

## Main statements

* `absoluteFiniteArtinLimitMap_apply` — the coordinate of the assembled
  map at `N` is the finite Artin coordinate at `N`; proved.
* `absoluteFiniteArtinLimitMap_denseRange` — the assembled map has
  dense range; proved.

## Implementation notes

The continuity fork of the arc, first:
`Atlas.Knowledge.IsLocalReciprocity` has no continuity field, so the
source's `→ₜ*` form of the assembled cone is restated as the plain
`→*`, dropping the `continuous_toFun` field with its discrete-topology
`letI` and identity-homomorphism scaffolding (its `:144`–`:160`) — the
fork strips continuity of the reciprocity homomorphisms. The dense
range stays: it is a statement about the bare function and the target's
topology — the exact shape of the structure's `denseRange` field — and
the source's proof route ports unchanged (`dense_iff_inter_open`,
`isOpen_pi_iff`, the finite `iInf` open normal subgroup, coordinate
surjectivity there, the `CategoryTheory.leOfHom` transport), consuming
only the limit topology and
`Atlas.Knowledge.absoluteFiniteArtinMap_surjective`, never continuity
of the map. The coordinates are indexed by the layer's unbundled
`OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)` where
the source indexes over its `ProfiniteGrp` bundle; the two spellings
are definitionally equal through `ProfiniteGrp.of`, and unification
crosses the re-bundling freely — the bundling is an abbreviation,
unlike the recorded `Field.absoluteGaloisGroup` instance seam. In the
cone's compatibility field the source's `change` recasting the
diagram's transition arrow to the named transition map survives
verbatim: the layer's
`Atlas.Knowledge.absoluteFiniteQuotientTransition` differs from the
functor's `QuotientGroup.map` only in its proof-irrelevant inclusion
argument. The variable block is the local-field Type-pinned block of
the consumed coordinates, that block's recorded universe seam. The
source's placeholder docstrings are replaced by content. Everything
else ports token-for-token; the file is the source's
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:123`–`:202`, less
the continuity field.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

open CategoryTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]

/-- **The compatible cone of the finite Artin coordinates**: the
homomorphism from `Kˣ` into the inverse limit of the finite quotients
whose coordinate at `N` is the finite Artin coordinate at `N`,
compatible along quotient transition ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:123`]
[Yamaguchi2026]). -/
noncomputable def absoluteFiniteArtinLimitMap :
    Kˣ →* absoluteFiniteArtinLimit K where
  toFun a :=
    ⟨fun N => absoluteFiniteArtinMap K N a, by
      intro N M i
      change
        absoluteFiniteQuotientTransition K (CategoryTheory.leOfHom i)
            (absoluteFiniteArtinMap K N a) =
          absoluteFiniteArtinMap K M a
      exact DFunLike.congr_fun
        (absoluteFiniteArtinMap_transition K (CategoryTheory.leOfHom i)) a⟩
  map_one' := by
    apply Subtype.ext
    funext N
    exact (absoluteFiniteArtinMap K N).map_one
  map_mul' x y := by
    apply Subtype.ext
    funext N
    exact (absoluteFiniteArtinMap K N).map_mul x y

/-- The coordinate of the assembled cone at an open normal subgroup is
the finite Artin coordinate there — definitionally ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:164`]
[Yamaguchi2026]). -/
@[simp]
theorem absoluteFiniteArtinLimitMap_apply
    (N : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K)) (a : Kˣ) :
    (absoluteFiniteArtinLimitMap K a).1 N = absoluteFiniteArtinMap K N a :=
  rfl

/-- **Surjectivity at every finite Artin coordinate makes the assembled
cone dense in the inverse limit** ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:172`]
[Yamaguchi2026]). -/
theorem absoluteFiniteArtinLimitMap_denseRange :
    DenseRange (absoluteFiniteArtinLimitMap K) := by
  apply dense_iff_inter_open.mpr
  rintro U ⟨s, hsO, hsv⟩ ⟨⟨spc, hspc⟩, uDefaultSpec⟩
  rw [← hsv] at uDefaultSpec
  rcases (isOpen_pi_iff.mp hsO) _ uDefaultSpec with ⟨J, fJ, hJ1, hJ2⟩
  let M := iInf (fun (j : J) => j.1.1.1)
  have hM : M.Normal :=
    Subgroup.normal_iInf_normal fun j => j.1.isNormal'
  have hMOpen :
      IsOpen (M : Set (Field.absoluteGaloisGroupAbelianization K)) := by
    rw [Subgroup.coe_iInf]
    exact isOpen_iInter_of_finite fun i => i.1.1.isOpen'
  let m : OpenNormalSubgroup (Field.absoluteGaloisGroupAbelianization K) :=
    { M with isOpen' := hMOpen }
  rcases absoluteFiniteArtinMap_surjective K m (spc m) with
    ⟨origin, horigin⟩
  use absoluteFiniteArtinLimitMap K origin
  refine ⟨?_, origin, rfl⟩
  rw [← hsv]
  apply hJ2
  intro a a_in_J
  let M_to_Na : m ⟶ a :=
    (iInf_le (fun (j : J) => j.1.1.1) ⟨a, a_in_J⟩).hom
  rw [← (absoluteFiniteArtinLimitMap K origin).property M_to_Na]
  change
    ((ProfiniteGrp.of
        (Field.absoluteGaloisGroupAbelianization K)).toFiniteQuotientFunctor ⋙
      forget₂ FiniteGrp ProfiniteGrp).map M_to_Na
        (absoluteFiniteArtinMap K m origin) ∈ _
  rw [horigin]
  exact Set.mem_of_eq_of_mem (hspc M_to_Na) (hJ1 a a_in_J).2

end

end Atlas.Knowledge
