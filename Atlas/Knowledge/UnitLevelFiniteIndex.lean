import Mathlib
import Atlas.Knowledge.HigherUnitGroup
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.UnitsFiniteIndexOpen

/-!
# finite index of a unit level

A higher unit group of a mixed-characteristic local field has finite index in the
valuation-one units: the kernel of the normalized valuation is compact — it is carried
homeomorphically onto a closed subset of the product of two unit spheres by the unit
embedding — and the level is an open subgroup, so the quotient is finite and discrete.
This is the compactness step in Milne's computation of the Herbrand quotient of the
units, and one of the two finiteness inputs of the class field axiom.

## Main statements

* `unitLevelFiniteIndex` — the quotient of the valuation-one units by a unit level is
  finite; proved.

## Implementation notes

The compactness of the kernel goes through `Units.isEmbedding_embedProduct`: the image of
the kernel in `L × Lᵐᵒᵖ` is the set of pairs `(x, op y)` with `x * y = 1` and both
valuations `1`, a closed subset of the product of the unit sphere with its opposite copy,
each compact as a closed subset of the compact integer ball. The sphere's closedness needs
the two strict balls open — `<` directly ultrametrically, `>` by the ultrametric equality
`v z = v x` on the small ball about `x`. The Hausdorff hypothesis of the closedness
arguments enters through the rank-one normed structure the field carries compatibly with
its topology, as in `Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField`. The openness
of the level is `Atlas.Knowledge.higherUnitGroup_isOpen` read on the extension field.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (L : Type*) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsMixedCharLocalField L]

/- Open balls about the origin are open: the ultrametric inequality, strictly. -/
private theorem isOpen_valuation_lt {γ : ValueGroupWithZero L} (hγ : γ ≠ 0) :
    IsOpen {y : L | valuation L y < γ} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  refine (IsValuativeTopology.hasBasis_nhds' x).mem_iff.mpr ⟨γ, hγ, fun y hy => ?_⟩
  calc valuation L y = valuation L ((y - x) + x) := by rw [sub_add_cancel]
  _ ≤ max (valuation L (y - x)) (valuation L x) := Valuation.map_add _ _ _
  _ < γ := max_lt hy hx

/- Outsides of closed balls are open: on the small ball about a member the valuation is
constant, by the ultrametric equality. -/
private theorem isOpen_valuation_gt {γ : ValueGroupWithZero L} :
    IsOpen {y : L | γ < valuation L y} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  have hx0 : valuation L x ≠ 0 := fun h0 => absurd hx (by simp [h0])
  refine (IsValuativeTopology.hasBasis_nhds' x).mem_iff.mpr
    ⟨valuation L x, hx0, fun y hy => ?_⟩
  have heq : valuation L y = valuation L x := by
    have h1 : valuation L y ≤ max (valuation L (y - x)) (valuation L x) := by
      calc valuation L y = valuation L ((y - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (valuation L (y - x)) (valuation L x) := Valuation.map_add _ _ _
    have h2 : valuation L x ≤ max (valuation L (x - y)) (valuation L y) := by
      calc valuation L x = valuation L ((x - y) + y) := by rw [sub_add_cancel]
      _ ≤ max (valuation L (x - y)) (valuation L y) := Valuation.map_add _ _ _
    rcases le_or_gt (valuation L x) (valuation L y) with hle | hlt
    · refine le_antisymm ?_ hle
      exact h1.trans (max_le (le_of_lt hy) le_rfl)
    · exfalso
      have hxy : valuation L (x - y) = valuation L (y - x) := by
        rw [show x - y = -(y - x) by ring, Valuation.map_neg]
      rw [hxy] at h2
      exact absurd (h2.trans_lt (max_lt hy hlt)) (lt_irrefl _)
  rw [Set.mem_setOf_eq, heq]
  exact hx

/- The unit sphere is closed: the complement is the union of the two open strict balls. -/
private theorem isClosed_valuation_sphere : IsClosed {y : L | valuation L y = 1} := by
  have hset : {y : L | valuation L y = 1} =
      {y : L | (1 : ValueGroupWithZero L) < valuation L y}ᶜ ∩ {y : L | valuation L y < 1}ᶜ := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt]
    constructor
    · exact fun h => ⟨le_of_eq h, le_of_eq h.symm⟩
    · rintro ⟨h1, h2⟩
      exact le_antisymm h1 h2
  rw [hset]
  exact IsClosed.inter (isOpen_valuation_gt L).isClosed_compl
    (isOpen_valuation_lt L one_ne_zero).isClosed_compl

/-- **A unit level has finite index in the valuation-one units**: the kernel of the
normalized valuation is compact and the level is open, so the quotient is finite —
"because `U_L` is compact, the quotient `U_L/V` is finite"
([Milne 2020, Chap. III, Lemma 2.5, p.105][MilneCFT];
[Yamaguchi 2026, `LocalClassFieldTheory/ClassFormation/NormalBasisFiniteQuotient.lean:77`]
[Yamaguchi2026]). -/
theorem unitLevelFiniteIndex (i : ℕ+) :
    Finite (↥(normalizedValuationHom L).ker ⧸
      (higherUnitGroup L i).subgroupOf (normalizedValuationHom L).ker) := by
  letI : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  haveI : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := L)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := L).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField L := Valued.toNontriviallyNormedField L (ValueGroupWithZero L)
  haveI : T2Space L := inferInstance
  -- the unit sphere of the field is compact
  have hOcompact : IsCompact (Set.range ((↑) : ↥𝒪[L] → L)) :=
    isCompact_range continuous_subtype_val
  have hrange : Set.range ((↑) : ↥𝒪[L] → L) = {y : L | valuation L y ≤ 1} := by
    ext y
    simp only [Subtype.range_coe_subtype, Set.mem_setOf_eq]
    exact Valuation.mem_integer_iff _ _
  have hsphere : IsCompact {y : L | valuation L y = 1} := by
    refine IsCompact.of_isClosed_subset (hrange ▸ hOcompact) (isClosed_valuation_sphere L) ?_
    intro y hy
    exact le_of_eq hy
  -- the valuation-one units are the embedded product's preimage of a compact set
  have hker_compact : IsCompact (((normalizedValuationHom L).ker : Subgroup Lˣ) : Set Lˣ) := by
    have hemb := Units.isEmbedding_embedProduct (M := L)
    rw [hemb.isCompact_iff]
    have himg : (Units.embedProduct L) ''
        (((normalizedValuationHom L).ker : Subgroup Lˣ) : Set Lˣ) =
        ({p : L × Lᵐᵒᵖ | p.1 * p.2.unop = 1} ∩
          ({p : L × Lᵐᵒᵖ | valuation L p.1 = 1} ∩
            {p : L × Lᵐᵒᵖ | valuation L p.2.unop = 1})) := by
      ext p
      constructor
      · rintro ⟨u, hu, rfl⟩
        have hu1 : valuation L ((u : Lˣ) : L) = 1 :=
          (mem_ker_normalizedValuationHom L u).mp hu
        have huinv : valuation L ((u⁻¹ : Lˣ) : L) = 1 := by
          have hmul : valuation L ((u : Lˣ) : L) * valuation L ((u⁻¹ : Lˣ) : L) = 1 := by
            rw [← map_mul]
            simp
          rw [hu1, one_mul] at hmul
          exact hmul
        refine ⟨?_, hu1, huinv⟩
        change ((u : Lˣ) : L) * ((u⁻¹ : Lˣ) : L) = 1
        rw [← Units.val_mul]
        simp
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨p.1, p.2.unop, h1, by rw [mul_comm]; exact h1⟩, ?_, ?_⟩
        · exact (mem_ker_normalizedValuationHom L _).mpr h2
        · change (p.1, MulOpposite.op p.2.unop) = p
          simp
    rw [himg]
    have hclosed : IsClosed ({p : L × Lᵐᵒᵖ | p.1 * p.2.unop = 1} ∩
        ({p : L × Lᵐᵒᵖ | valuation L p.1 = 1} ∩
          {p : L × Lᵐᵒᵖ | valuation L p.2.unop = 1})) := by
      refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
      · exact isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd))
          continuous_const
      · exact (isClosed_valuation_sphere L).preimage continuous_fst
      · exact (isClosed_valuation_sphere L).preimage
          (MulOpposite.continuous_unop.comp continuous_snd)
    have hprod : IsCompact ({y : L | valuation L y = 1} ×ˢ
        (MulOpposite.op '' {y : L | valuation L y = 1})) :=
      hsphere.prod (hsphere.image MulOpposite.continuous_op)
    refine IsCompact.of_isClosed_subset hprod hclosed ?_
    rintro p ⟨h1, h2, h3⟩
    refine ⟨h2, ?_⟩
    exact ⟨p.2.unop, h3, by simp⟩
  haveI : CompactSpace ↥(normalizedValuationHom L).ker :=
    isCompact_iff_compactSpace.mp hker_compact
  have hopen : IsOpen (((higherUnitGroup L i).subgroupOf (normalizedValuationHom L).ker :
      Subgroup ↥(normalizedValuationHom L).ker) : Set ↥(normalizedValuationHom L).ker) := by
    have hset : (((higherUnitGroup L i).subgroupOf (normalizedValuationHom L).ker :
        Subgroup ↥(normalizedValuationHom L).ker) : Set ↥(normalizedValuationHom L).ker) =
        (Subtype.val : ↥(normalizedValuationHom L).ker → Lˣ) ⁻¹'
          (higherUnitGroup L i : Set Lˣ) := rfl
    rw [hset]
    exact (higherUnitGroup_isOpen L i).preimage continuous_subtype_val
  exact Subgroup.quotient_finite_of_isOpen _ hopen

end Atlas.Knowledge
