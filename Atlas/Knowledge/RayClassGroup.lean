import Mathlib
import Atlas.Knowledge.IdeleClassGroup
import Atlas.Knowledge.IdeleGroup
import Atlas.Knowledge.Modulus
import Atlas.Knowledge.PrincipalIdele

/-!
# ray class group

The ray class group of a modulus: the idele class group cut by the congruence conditions
the modulus imposes — units congruent to `1` to the prescribed depth at the finite places
of the modulus, positive at its real places. The congruence subgroup is assembled from
local pieces that are each one Mathlib construction: the local higher unit groups are
kernels of unit reduction modulo powers of the maximal ideal of the completion's integers,
and real positivity is one comap of the positive-reals subgroup along the real embedding.
The definitions land proved; the one recorded claim is the closedness of the congruence
subgroup in the idele class group, which is what feeds these subgroups to the existence
theorem.

## Main definitions

* `localHigherUnitGroup` — `U_v^(n)` inside `(v.adicCompletion K)ˣ`.
* `realPositiveSubgroup` — positivity at one real place.
* `ideleCongruenceSubgroup`, `congruenceSubgroup` — the modulus's condition at idele and
  class level.
* `RayClassGroup` — `C_K ⧸ congruenceSubgroup m`.

## Main statements

* `localHigherUnitGroup_zero` — at level zero the condition is integrality alone; proved.
* `mem_realPositiveSubgroup_iff`, `mem_finiteIdeleCongruenceSubgroup_iff`,
  `mem_ideleCongruenceSubgroup_iff` — membership read off componentwise; proved.
* `congruenceSubgroup_eq_map` — the join with the principal ideles is absorbed by the
  quotient, so the congruence subgroup is the bare image; proved.
* `isClosed_congruenceSubgroup` — recorded ahead of its proof.

## Implementation notes

The finite congruence condition is an infimum of comaps along Mathlib's restricted-product
evaluations, so membership is the pointwise condition at every place — including
integrality outside the modulus's support, where the level is zero and
`localHigherUnitGroup_zero` applies; this is the literature's `U (𝔪)`. The real-place
condition comaps `Units.posSubgroup ℝ` along
`InfinitePlace.Completion.extensionEmbeddingOfIsReal`, replacing the source's if-then-else
over all infinite places and its `piUnits` transport
(`AlgebraicNumberTheory/RayClass/Basic.lean:93`, `FullModulus.lean:214, :252`) by one
comap over the modulus's real places. The class-level subgroup joins the principal ideles before
mapping down, as the source does (`FullModulus.lean:330`).

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- Reduction of local integral units mod the `n`-th power of the maximal ideal. -/
noncomputable def localUnitReduction (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (v.adicCompletionIntegers K).units →*
      ((v.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)ˣ :=
  (Units.map (Ideal.Quotient.mk
      ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)).toMonoidHom).comp
    (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.toMonoidHom

/-- The **local higher unit group** `U_v^(n)`: integral units congruent to `1` modulo the
`n`-th power of the maximal ideal ([Milne 2020, Chap. V, §4, p.172][MilneCFT];
Yamaguchi 2026, `AlgebraicNumberTheory/RayClass/Basic.lean:42`). -/
noncomputable def localHigherUnitGroup (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (v.adicCompletion K)ˣ :=
  Subgroup.map ((v.adicCompletionIntegers K).units).subtype
    (localUnitReduction K v n).ker

/-- Membership through the integral-unit lift and the vanishing of the reduction
([Milne 2020, Chap. V, §4, p.172][MilneCFT]). -/
theorem mem_localHigherUnitGroup_iff (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ localHigherUnitGroup K v n ↔
      ∃ y : (v.adicCompletionIntegers K).units,
        (y : (v.adicCompletion K)ˣ) = x ∧ localUnitReduction K v n y = 1 := by
  rw [localHigherUnitGroup, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, rfl, MonoidHom.mem_ker.mp hy⟩
  · rintro ⟨y, rfl, hy⟩
    exact ⟨y, MonoidHom.mem_ker.mpr hy, rfl⟩

/-- At level zero the congruence condition is vacuous: `U_v^(0)` is the full integral-unit
subgroup — the reason the finite congruence condition imposes only integrality outside a
modulus's support ([Milne 2020, Chap. V, §4, p.172][MilneCFT]). -/
theorem localHigherUnitGroup_zero (v : HeightOneSpectrum (𝓞 K)) :
    localHigherUnitGroup K v 0 = (v.adicCompletionIntegers K).units := by
  ext x
  rw [mem_localHigherUnitGroup_iff]
  constructor
  · rintro ⟨y, rfl, _hy⟩
    exact y.property
  · intro hx
    refine ⟨⟨x, hx⟩, rfl, ?_⟩
    letI : Subsingleton
        ((v.adicCompletionIntegers K) ⧸
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by simp)
    exact Units.ext (Subsingleton.elim _ _)

/-- The subgroup of infinite-adele units **positive at the real place** `v`
([Milne 2020, Chap. V, §4, p.172][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/RayClass/Basic.lean:93`). -/
noncomputable def realPositiveSubgroup (v : RealPlace K) :
    Subgroup (InfiniteAdeleRing K)ˣ :=
  Subgroup.comap
    (Units.map ((InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2).comp
      (Pi.evalRingHom (fun w : InfinitePlace K => w.Completion) v.1)).toMonoidHom)
    (Units.posSubgroup ℝ)

omit [NumberField K] in
/-- Positivity at a real place, read on the component: the real embedding of the
`v`-coordinate is positive ([Milne 2020, Chap. V, §4, p.172][MilneCFT]). -/
theorem mem_realPositiveSubgroup_iff (v : RealPlace K) (x : (InfiniteAdeleRing K)ˣ) :
    x ∈ realPositiveSubgroup K v ↔
      0 < InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2
        ((x : InfiniteAdeleRing K) v.1) := by
  rw [realPositiveSubgroup, Subgroup.mem_comap, Units.mem_posSubgroup, Units.coe_map]
  rfl

/-- The finite congruence subgroup of a finite modulus: the congruence condition at every
finite place, to the modulus's depth ([Milne 2020, Chap. V, §4, p.172][MilneCFT];
Yamaguchi 2026, `AlgebraicNumberTheory/RayClass/Basic.lean:120`). -/
noncomputable def finiteIdeleCongruenceSubgroup (m : HeightOneSpectrum (𝓞 K) →₀ ℕ) :
    Subgroup (Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (v.adicCompletionIntegers K).units]) :=
  ⨅ v, Subgroup.comap (RestrictedProduct.evalMonoidHom _ v)
    (localHigherUnitGroup K v (m v))

/-- Membership in the finite congruence subgroup is the local condition at every finite
place ([Milne 2020, Chap. V, §4, p.172][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/RayClass/Basic.lean:130`). -/
theorem mem_finiteIdeleCongruenceSubgroup_iff (m : HeightOneSpectrum (𝓞 K) →₀ ℕ)
    (y : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (v.adicCompletionIntegers K).units]) :
    y ∈ finiteIdeleCongruenceSubgroup K m ↔ ∀ v, y v ∈ localHigherUnitGroup K v (m v) := by
  unfold finiteIdeleCongruenceSubgroup
  simp only [Subgroup.mem_iInf, Subgroup.mem_comap, RestrictedProduct.evalMonoidHom_apply]

/-- The **idele congruence subgroup** of a modulus: real positivity at its real places,
finite congruence everywhere ([Milne 2020, Chap. V, §4, p.172][MilneCFT];
Yamaguchi 2026, `AlgebraicNumberTheory/RayClass/FullModulus.lean:307`). -/
noncomputable def ideleCongruenceSubgroup (m : Modulus K) : Subgroup (IdeleGroup K) :=
  (⨅ v ∈ m.infinitePart, realPositiveSubgroup K v).prod
    (finiteIdeleCongruenceSubgroup K m.finitePart)

/-- Membership in the idele congruence subgroup: positive at the modulus's real places,
locally congruent at every finite place ([Milne 2020, Chap. V, §4, p.172][MilneCFT];
Yamaguchi 2026, `AlgebraicNumberTheory/RayClass/FullModulus.lean:313`). -/
theorem mem_ideleCongruenceSubgroup_iff (m : Modulus K) (y : IdeleGroup K) :
    y ∈ ideleCongruenceSubgroup K m ↔
      (∀ v ∈ m.infinitePart, y.1 ∈ realPositiveSubgroup K v) ∧
        ∀ v, y.2 v ∈ localHigherUnitGroup K v (m.finitePart v) := by
  unfold ideleCongruenceSubgroup
  rw [Subgroup.mem_prod, mem_finiteIdeleCongruenceSubgroup_iff]
  simp only [Subgroup.mem_iInf]

/-- The **congruence subgroup** of the idele class group: the modulus's condition joined
with the principal ideles, mapped down to `C_K`
([Milne 2020, Chap. V, §4, p.172][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/RayClass/FullModulus.lean:330`). -/
noncomputable def congruenceSubgroup (m : Modulus K) : Subgroup (IdeleClassGroup K) :=
  Subgroup.map (QuotientGroup.mk' (principalIdeleSubgroup K))
    (ideleCongruenceSubgroup K m ⊔ principalIdeleSubgroup K)

/-- The principal ideles die in the quotient, so the congruence subgroup is the bare image
of the idele congruence subgroup ([Milne 2020, Chap. V, §4, p.172][MilneCFT]). -/
theorem congruenceSubgroup_eq_map (m : Modulus K) :
    congruenceSubgroup K m =
      (ideleCongruenceSubgroup K m).map (QuotientGroup.mk' (principalIdeleSubgroup K)) := by
  unfold congruenceSubgroup
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq]

/-- The **ray class group** of a modulus, `C_K ⧸ C_K^𝔪`
([Milne 2020, Chap. V, §1, p.149][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/RayClass/FullModulus.lean:345`). -/
abbrev RayClassGroup (m : Modulus K) : Type _ :=
  IdeleClassGroup K ⧸ congruenceSubgroup K m

/-- The congruence subgroup is closed in the idele class group — what qualifies it as
input to the existence theorem. Claim recorded ahead of its proof
([Milne 2020, Chap. V, §5, Thm. 5.5, p.179][MilneCFT]; Yamaguchi 2026,
`AlgebraicNumberTheory/RayClass/Topology.lean:906`). -/
theorem isClosed_congruenceSubgroup (m : Modulus K) :
    IsClosed (congruenceSubgroup K m : Set (IdeleClassGroup K)) := by
  sorry

end Atlas.Knowledge

end
