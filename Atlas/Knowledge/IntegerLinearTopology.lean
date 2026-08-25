import Mathlib
import Atlas.Knowledge.GalIdealPowCounts
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# linear topology of the integers

The integer ring of a mixed-characteristic local field as a topological coefficient ring
for evaluation: the maximal-ideal powers are a neighborhood basis of zero, so the ring is
linearly topologized; it is Hausdorff, and its maximal-ideal elements are topologically
nilpotent — the `PowerSeries.HasEval` points at which the Lubin–Tate formal module will
be evaluated. Completeness is a one-liner at every use site: the ring is compact and
Hausdorff, so any compatible uniformity is complete.

## Main statements

* `isTopologicallyNilpotent_of_mem_maximalIdeal` / `powerSeries_hasEval_of_mem_maximalIdeal`
  — maximal-ideal elements are evaluation points; proved.
* `hasBasis_nhds_zero_integer` — the ideal-power neighborhood basis; proved.
* The `IsLinearTopology` and `T2Space` instances on `↥𝒪[E]`; proved.

## Implementation notes

No `UniformSpace` instance is declared: the evaluation theory treats coefficient rings
through the discrete uniformity and targets through a proof-local
`IsTopologicalAddGroup.rightUniformSpace`, and a global choice here would collide with
both. The Hausdorff instance reaches the field's rank-one normed structure through the
usual staging, once, inside its own proof; compactness is ambient, so
`complete_of_compact` closes completeness wherever a uniformity has been staged. The
valuative utilities consumed here — `Atlas.Knowledge.exists_pow_le` and
`Atlas.Knowledge.mem_idealPow_iff_val` — went public in
`Atlas.Knowledge.GalIdealPowCounts` for this file.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer
  New York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsMixedCharLocalField E]

/- Maximal-ideal elements of the integers are topologically nilpotent: powers sink below
every valuative ball. -/
/- Maximal-ideal elements of the integers are topologically nilpotent: powers sink below
every valuative ball. -/
/- Local copy of GalIdealPowCounts' private exists_pow_le — promote there at PR time. -/
private theorem exists_pow_le' (γ δ : ValueGroupWithZero E) (hγ1 : γ < 1) (hγ0 : γ ≠ 0)
    (hδ0 : δ ≠ 0) : ∃ N : ℕ, γ ^ N ≤ δ := by
  set e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E
  have hγe : e γ < 1 := by
    have := e.strictMono hγ1
    rwa [map_one] at this
  have hγe0 : e γ ≠ 0 := by simp [hγ0]
  have hδe0 : e δ ≠ 0 := by simp [hδ0]
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.mp hγe0
  obtain ⟨d, hd⟩ := WithZero.ne_zero_iff_exists.mp hδe0
  have haneg : Multiplicative.toAdd a ≤ -1 := by
    have h1 : (a : WithZero (Multiplicative ℤ)) < 1 := by
      rw [ha]
      exact hγe
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h1
    have h2 : Multiplicative.toAdd a < Multiplicative.toAdd (1 : Multiplicative ℤ) :=
      Multiplicative.toAdd_lt.mpr h1
    simp only [toAdd_one] at h2
    omega
  refine ⟨(Multiplicative.toAdd d).natAbs, ?_⟩
  have hmono := e.strictMono.le_iff_le (a := γ ^ (Multiplicative.toAdd d).natAbs) (b := δ)
  rw [← hmono, map_pow, ← ha, ← hd, ← WithZero.coe_pow, WithZero.coe_le_coe]
  rw [← Multiplicative.toAdd_le, _root_.toAdd_pow, nsmul_eq_mul]
  set t := Multiplicative.toAdd a
  set u := Multiplicative.toAdd d
  have hprod : ((Int.natAbs u : ℤ)) * (t + 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg _) (by omega)
  have : ((Int.natAbs u : ℤ)) * t ≤ u := by
    rcases Int.natAbs_eq u with hu | hu
    · nlinarith [Int.natCast_nonneg (Int.natAbs u)]
    · nlinarith [Int.natCast_nonneg (Int.natAbs u)]
  exact this

/- Maximal-ideal elements of the integers are topologically nilpotent: powers sink below
every valuative ball. -/
theorem isTopologicallyNilpotent_of_mem_maximalIdeal {x : ↥𝒪[E]}
    (hx : x ∈ 𝓂[E]) : IsTopologicallyNilpotent x := by
  have hxv : valuation E ((x : ↥𝒪[E]) : E) < 1 := by
    have hnonunit : ¬IsUnit x := fun hunit =>
      IsLocalRing.maximalIdeal.isMaximal ↥𝒪[E] |>.ne_top
        (Ideal.eq_top_of_isUnit_mem _ hx hunit)
    rwa [← Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  rw [IsTopologicallyNilpotent]
  rw [tendsto_subtype_rng]
  rw [show (fun n : ℕ => ((x ^ n : ↥𝒪[E]) : E)) = fun n : ℕ => ((x : ↥𝒪[E]) : E) ^ n
    from funext fun n => by push_cast; rfl]
  rw [show (((0 : ↥𝒪[E]) : E)) = 0 from rfl]
  rw [(IsValuativeTopology.hasBasis_nhds_zero E).tendsto_right_iff]
  rintro γ -
  rcases eq_or_ne (valuation E ((x : ↥𝒪[E]) : E)) 0 with hx0 | hx0
  · refine Filter.eventually_atTop.mpr ⟨1, fun n hn => ?_⟩
    have hz : valuation E (((x : ↥𝒪[E]) : E) ^ n) = 0 := by
      rw [map_pow, hx0, zero_pow (by omega)]
    simp only [Set.mem_setOf_eq, map_pow, hx0, zero_pow (show n ≠ 0 by omega)]
    exact zero_lt_iff.mpr γ.ne_zero
  · obtain ⟨N, hN⟩ := exists_pow_le E (valuation E ((x : ↥𝒪[E]) : E))
      (γ : ValueGroupWithZero E) hxv hx0 γ.ne_zero
    refine Filter.eventually_atTop.mpr ⟨N + 1, fun n hn => ?_⟩
    simp only [Set.mem_setOf_eq, map_pow]
    calc valuation E ((x : ↥𝒪[E]) : E) ^ n
        ≤ valuation E ((x : ↥𝒪[E]) : E) ^ (N + 1) :=
          pow_le_pow_right_of_le_one' (le_of_lt hxv) hn
    _ < valuation E ((x : ↥𝒪[E]) : E) ^ N :=
          pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.mpr hx0) hxv (Nat.lt_succ_self N)
    _ ≤ (γ : ValueGroupWithZero E) := hN

/- The maximal-ideal powers are a neighborhood basis of zero in the integers: the
valuative balls restrict to them. -/
theorem hasBasis_nhds_zero_integer :
    (nhds (0 : ↥𝒪[E])).HasBasis (fun _ : ℕ => True)
      (fun n => ((𝓂[E] ^ n : Ideal ↥𝒪[E]) : Set ↥𝒪[E])) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (↥𝒪[E])
  have hϖ0 : (ϖ : E) ≠ 0 := fun h0 => hϖ.ne_zero (Subtype.ext h0)
  have hϖv0 : valuation E ((ϖ : E)) ≠ 0 := (Valuation.ne_zero_iff _).mpr hϖ0
  have hϖv1 : valuation E ((ϖ : E)) < 1 :=
    (Valuation.integer.integers (v := valuation E)).valuation_irreducible_lt_one hϖ
  have hcomap : (nhds (0 : ↥𝒪[E])) =
      Filter.comap (Subtype.val) (nhds ((0 : ↥𝒪[E]) : E)) := nhds_subtype _ _
  rw [hcomap, show (((0 : ↥𝒪[E])) : E) = 0 from rfl]
  refine ((IsValuativeTopology.hasBasis_nhds_zero E).comap Subtype.val).to_hasBasis ?_ ?_
  · rintro γ -
    obtain ⟨N, hN⟩ := exists_pow_le E (valuation E ((ϖ : E)))
      (γ : ValueGroupWithZero E) hϖv1 hϖv0 γ.ne_zero
    refine ⟨N + 1, trivial, fun x hx => ?_⟩
    have hxv := (mem_idealPow_iff_val hϖ (N + 1) x).mp hx
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    calc valuation E ((x : ↥𝒪[E]) : E) ≤ valuation E ((ϖ : E)) ^ (N + 1) := hxv
    _ < valuation E ((ϖ : E)) ^ N :=
        pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.mpr hϖv0) hϖv1 (Nat.lt_succ_self N)
    _ ≤ (γ : ValueGroupWithZero E) := hN
  · rintro n -
    refine ⟨Units.mk0 (valuation E ((ϖ : E)) ^ n) (pow_ne_zero _ hϖv0), trivial,
      fun x hx => ?_⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hx
    exact (mem_idealPow_iff_val hϖ n x).mpr (le_of_lt hx)

/- The integers are linearly topologized: the ideal-power basis. -/
instance : IsLinearTopology ↥𝒪[E] ↥𝒪[E] := by
  refine IsLinearTopology.mk_of_hasBasis' (R := ↥𝒪[E]) (S := Ideal ↥𝒪[E])
    (hasBasis_nhds_zero_integer E) ?_
  intro s r m hm
  exact Ideal.mul_mem_left s r hm

section Uniform

/- The integers are Hausdorff: the field is, under the rank-one norm its topology
carries. -/
instance : T2Space ↥𝒪[E] := by
  letI : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  haveI : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  letI : (Valued.v (R := E)).RankOne :=
    { hom' := IsRankLeOne.nonempty.some.emb (R := E).comp
        MonoidWithZeroHom.ValueGroup₀.embedding
      strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  letI : NontriviallyNormedField E := Valued.toNontriviallyNormedField E (ValueGroupWithZero E)
  haveI : T2Space E := inferInstance
  infer_instance

/- Maximal-ideal elements evaluate power series: they are topologically nilpotent. -/
theorem powerSeries_hasEval_of_mem_maximalIdeal {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) :
    PowerSeries.HasEval x :=
  (PowerSeries.hasEval_def x).mpr (isTopologicallyNilpotent_of_mem_maximalIdeal E hx)

end Uniform

end Atlas.Knowledge
