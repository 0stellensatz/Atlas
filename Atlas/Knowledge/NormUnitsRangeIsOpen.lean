import Mathlib

/-!
# openness of the norm subgroup

The norm subgroup of a finite separable extension of a nonarchimedean local field is open
in the multiplicative group of the base. This supplies the topological input to the
finiteness of `Atlas.Knowledge.ConductorExponent` in either characteristic.

## Main statements

* `normUnits_range_isOpen` — the range of the norm on units is open.

## Implementation notes

The source proves openness for finite Galois extensions by showing that the image of the
integer units is compact and using the finite norm index from reciprocity. Here an
analytic proof supplies the same input without requiring reciprocity in equal
characteristic. For a primitive element, its minimal polynomial satisfies
`p.eval t = Algebra.norm K (algebraMap K L t - b.gen)`. Separability makes its derivative
nonzero. Since the base field is infinite, some `a` makes both `p.eval a` and
`p.derivative.eval a` nonzero. Mathlib's `Polynomial.hasStrictDerivAt` and
`HasStrictDerivAt.map_nhds_eq` then put a neighborhood of `p.eval a` in the polynomial's
range. Pulling back to `Kˣ` puts a neighborhood in the norm subgroup; a subgroup containing
a neighborhood of any of its points is open.

The normed-field structure used by the inverse function theorem is installed only on the
base, through `Valued.toNontriviallyNormedField`, preserving its given topology. The
extension needs no valuation or topology, and its universe is independent of the base's.
The proof needs separability, and therefore covers the finite abelian extensions used by
the conductor theorem without any characteristic restriction.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

open scoped Topology
open Filter Polynomial

private theorem normUnits_range_isOpen_of_normed (K L : Type*)
    [NontriviallyNormedField K] [CompleteSpace K]
    [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsOpen ((Units.map (Algebra.norm K : L →* K)).range : Set Kˣ) := by
  classical
  let b := Field.powerBasisOfFiniteOfSeparable K L
  let p := minpoly K b.gen
  have hp : p ≠ 0 := minpoly.ne_zero (b.isIntegral_gen)
  have hd : p.derivative ≠ 0 :=
    (separable_iff_derivative_ne_zero (minpoly.irreducible b.isIntegral_gen)).mp
      (Algebra.IsSeparable.isSeparable K b.gen)
  obtain ⟨a, ha⟩ : ∃ a : K, (p * p.derivative).eval a ≠ 0 := by
    by_contra! h
    exact mul_ne_zero hp hd (Polynomial.zero_of_eval_zero _ h)
  have ha' := mul_ne_zero_iff.mp (by simpa only [eval_mul] using ha)
  have heval (t : K) : p.eval t = Algebra.norm K (algebraMap K L t - b.gen) := by
    rw [Algebra.norm_eq_matrix_det b.basis, map_sub, AlgHom.commutes]
    change p.eval t = (Matrix.scalar (Fin b.dim) t - Algebra.leftMulMatrix b.basis b.gen).det
    rw [← Matrix.eval_charpoly, charpoly_leftMulMatrix b]
  have hrange : Set.range p.eval ∈ 𝓝 (p.eval a) := by
    rw [← (p.hasStrictDerivAt a).map_nhds_eq ha'.2]
    exact Filter.range_mem_map
  let u : Kˣ := Units.mk0 (p.eval a) ha'.1
  apply Subgroup.isOpen_of_mem_nhds (g := u)
  apply Filter.mem_of_superset (Filter.mem_map.mp ((Units.continuous_val.tendsto u) hrange))
  rintro x ⟨t, ht⟩
  change p.eval t = (x : K) at ht
  have ht0 : algebraMap K L t - b.gen ≠ 0 := by
    intro h
    rw [heval, h, Algebra.norm_zero] at ht
    exact x.ne_zero ht.symm
  refine ⟨Units.mk0 (algebraMap K L t - b.gen) ht0, ?_⟩
  apply Units.ext
  exact (heval t).symm.trans ht

open ValuativeRel
/-- The norm subgroup of a finite separable extension of a nonarchimedean local field is
open in `Kˣ` (Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean:204`, with the
Galois hypothesis relaxed to separability). -/
theorem normUnits_range_isOpen (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    IsOpen ((Units.map (Algebra.norm K : L →* K)).range : Set Kˣ) := by
  letI : UniformSpace K := IsTopologicalAddGroup.rightUniformSpace K
  letI : IsUniformAddGroup K := isUniformAddGroup_of_addCommGroup
  letI : Valued K (ValueGroupWithZero K) := inferInstance
  letI : (Valued.v : Valuation K (ValueGroupWithZero K)).RankOne :=
    { hom' := ValuativeRel.IsRankLeOne.nonempty.some.emb (R := K) |>.comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := ValuativeRel.IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField K :=
    Valued.toNontriviallyNormedField (L := K) (Γ₀ := ValueGroupWithZero K)
  letI : CompleteSpace K := inferInstance
  exact normUnits_range_isOpen_of_normed K L

end Atlas.Knowledge
