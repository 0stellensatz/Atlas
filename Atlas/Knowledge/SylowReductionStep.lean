import Mathlib
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.IntermediateGaloisCorrespondence

/-!
# Sylow reduction step

The group-theoretic part of the first reduction: for a Sylow
`p`-subgroup `P` of the actual finite quotient `G(L/K)`, the fixed
field `M = L^P` is an actual (not necessarily Galois) intermediate
field whose lower quotient `G(L/M)` is a `p`-group — hence solvable —
while `[M:K] = (G(L/K) : P)` is prime to `p`; and in a possibly
infinite abelian target, every Sylow `p`-subgroup lies in the image of
the `[M:K]`-fold map, the input the identity `N_{M/K} ∘ i = [M:K]`
later converts into norm-map containment. The ambient norm quotient is
at this point only known to have bounded exponent, so the
abelian-target lemma assumes no finiteness — no reciprocity
surjectivity or finite-reciprocity comparison enters (#104).

## Main statements

* `FiniteGaloisSubextension.abstractReciprocity_sylow_lowerQuotient_isSolvable`
  — `G(L/M)` is solvable; proved through the `p`-group chain.
* `FiniteGaloisSubextension.abstractReciprocity_sylowAddSubgroup_le_intermediateDegree_nsmul_range`
  — the Sylow subgroup of the target lies in the `[M:K]`-fold image;
  proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
and two correspondence names are the layer's renames:
`extensionSubgroup_intermediateField_eq` is
`subgroupOf_intermediateField_eq`, and
`extensionSubgroup_index_eq_degree` is `subgroup_index_eq_degree`. The
file mentions no representation, so everything keeps the source's
`Type*` generality. `sylowAddSubgroup_le_nsmul_range_of_coprime` sheds
the source's `[Fact p.Prime]`: the elaborated proof never consumes it
and it is not derivable from the kept binders, so the ported statement
is strictly more general — Mathlib's `IsPGroup.powEquiv` needs only the
coprimality. The one consumer, the specialization below it, keeps the
instance its own coprimality argument requires. This completes the
`Reciprocity/Sylow.lean` source file whole.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- For `M = L^P`, the actual lower quotient `G(L/M)` is a `p`-group —
the identification `G(L/M) ≃ P` applied to an actual Sylow subgroup of
the actual finite quotient `G(L/K)` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Sylow.lean:43`). -/
theorem abstractReciprocity_sylow_lowerQuotient_isPGroup
    (L : FiniteGaloisSubextension K) {p : ℕ}
    (P : Sylow p L.extensionQuotient) :
    IsPGroup p
      ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
        L.field.toSubgroup.subgroupOf
          (L.intermediateField
            (P : Subgroup L.extensionQuotient)).toSubgroup) := by
  exact P.isPGroup'.of_equiv
    (L.lowerQuotientEquiv (P : Subgroup L.extensionQuotient)).symm

/-- **Consequently, the actual extension `L/M` cut out by a Sylow
subgroup is solvable** — by the standard chain finite `p`-group ⇒
nilpotent ⇒ solvable (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Sylow.lean:58`). -/
theorem abstractReciprocity_sylow_lowerQuotient_isSolvable
    (L : FiniteGaloisSubextension K) {p : ℕ} [Fact p.Prime]
    (P : Sylow p L.extensionQuotient) :
    IsSolvable
      ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
        L.field.toSubgroup.subgroupOf
          (L.intermediateField
            (P : Subgroup L.extensionQuotient)).toSubgroup) := by
  letI : Finite
      ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
        L.field.toSubgroup.subgroupOf
          (L.intermediateField
            (P : Subgroup L.extensionQuotient)).toSubgroup) :=
    L.extension_over_intermediate_finite
      (P : Subgroup L.extensionQuotient)
  letI : Group.IsNilpotent
      ((L.intermediateField (P : Subgroup L.extensionQuotient)).toSubgroup ⧸
        L.field.toSubgroup.subgroupOf
          (L.intermediateField
            (P : Subgroup L.extensionQuotient)).toSubgroup) :=
    (L.abstractReciprocity_sylow_lowerQuotient_isPGroup P).isNilpotent
  infer_instance

/-- The degree of the actual fixed field `M = L^P` over `K` is the
index of `P` in `G(L/K)`; no normality of `P`, and hence none of
`M/K`, is used (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Sylow.lean:87`). -/
theorem abstractReciprocity_sylow_intermediateDegree_eq_index
    (L : FiniteGaloisSubextension K) {p : ℕ}
    (P : Sylow p L.extensionQuotient) :
    (L.intermediateFiniteAbstractExtension
      (P : Subgroup L.extensionQuotient)).degree =
      (P : Subgroup L.extensionQuotient).index := by
  rw [← (L.intermediateFiniteAbstractExtension
    (P : Subgroup L.extensionQuotient)).subgroup_index_eq_degree]
  change ((L.intermediateField
    (P : Subgroup L.extensionQuotient)).toSubgroup.subgroupOf
      K.toSubgroup).index = _
  rw [L.subgroupOf_intermediateField_eq
    (P : Subgroup L.extensionQuotient)]
  exact (P : Subgroup L.extensionQuotient).index_comap_of_surjective
    (QuotientGroup.mk'_surjective
      (L.field.toSubgroup.subgroupOf K.toSubgroup))

/-- Hence the actual degree `[M:K]` is prime to the chosen Sylow prime
`p` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Sylow.lean:106`). -/
theorem abstractReciprocity_sylow_intermediateDegree_coprime
    (L : FiniteGaloisSubextension K) {p : ℕ} [Fact p.Prime]
    (P : Sylow p L.extensionQuotient) :
    Nat.Coprime
      (L.intermediateFiniteAbstractExtension
        (P : Subgroup L.extensionQuotient)).degree p := by
  rw [L.abstractReciprocity_sylow_intermediateDegree_eq_index P]
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
  exact P.not_dvd_index

/-- Let `S` be a Sylow `p`-subgroup of an abelian group `B`; if `n` is
prime to `p`, then `S` lies in the range of the additive `n`-fold map
on `B` — `S` has `p`-power order, so the `n`-fold map is a bijection on
`S`, and a preimage in `S` is in particular a preimage in `B`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Sylow.lean:125`). -/
theorem sylowAddSubgroup_le_nsmul_range_of_coprime
    {B : Type*} [AddCommGroup B]
    {p n : ℕ}
    (S : Sylow p (Multiplicative B)) (hn : Nat.Coprime n p) :
    Subgroup.toAddSubgroup'
        (S : Subgroup (Multiplicative B)) ≤
      (nsmulAddMonoidHom (α := B) n).range := by
  intro x hx
  let xS : S := ⟨Multiplicative.ofAdd x, hx⟩
  let e : S ≃ S := S.isPGroup'.powEquiv hn.symm
  let yS : S := e.symm xS
  refine ⟨yS.1.toAdd, ?_⟩
  have hy : yS ^ n = xS := e.apply_symm_apply xS
  have hyval : yS.1 ^ n = xS.1 := congrArg Subtype.val hy
  simpa [xS] using congrArg Multiplicative.toAdd hyval

/-- **The exact specialization: for `M = L^P`, every Sylow `p`-subgroup
of an abelian group `B` lies in the image of the `[M:K]`-fold map on
`B`** — the group-theoretic input the identity `N_{M/K} ∘ i = [M:K]`
later converts into norm-map containment (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Sylow.lean:145`). -/
theorem abstractReciprocity_sylowAddSubgroup_le_intermediateDegree_nsmul_range
    (L : FiniteGaloisSubextension K) {p : ℕ} [Fact p.Prime]
    (P : Sylow p L.extensionQuotient)
    {B : Type*} [AddCommGroup B]
    (S : Sylow p (Multiplicative B)) :
    Subgroup.toAddSubgroup'
        (S : Subgroup (Multiplicative B)) ≤
      (nsmulAddMonoidHom (α := B)
        (L.intermediateFiniteAbstractExtension
          (P : Subgroup L.extensionQuotient)).degree).range := by
  exact sylowAddSubgroup_le_nsmul_range_of_coprime S
    (L.abstractReciprocity_sylow_intermediateDegree_coprime P)

end FiniteGaloisSubextension

end

end Atlas.Knowledge
