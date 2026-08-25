import Mathlib
import Atlas.Knowledge.IntegerLinearTopology
import Atlas.Knowledge.LubinTateFormalGroup
import Atlas.Knowledge.NormalizedValuationAlgEquiv

/-!
# Lubin–Tate module

The formal module, evaluated: on the integers of a finite extension of the base local
field, the Lubin–Tate group law and scalars evaluate through
`MvPowerSeries.eval₂` at maximal-ideal points, giving the operations from which the
module structure on the maximal ideal is assembled — the addition
`x +[e] y = F_e (x, y)`, the scalars `[a] x`, closure in the ideal, commutativity,
associativity, the identity `x +[e] 0 = x`, the negation by `[-1]` with its
cancellation, `[a] ([b] x) = [a b] x`,
`[a] (x + y) = [a] x + [a] y`, `[a + b] x = [a] x + [b] x`, `[1] x = x` — with every law
the evaluation of the corresponding series identity of
`Atlas.Knowledge.lubinTateFormalGroupPowerSeries`, and the whole structure equivariant
under the `K`-automorphisms of the extension. This is the carrier of the torsion towers
of local class field theory.

## Main definitions

* `lubinTateAdd` / `lubinTateSMul` — the evaluated group law and scalars.

## Main statements

* `eval₂_mem_maximalIdeal` — evaluation of a constant-term-zero series at maximal-ideal
  points lands in the maximal ideal; proved.
* `lubinTateAdd_mem_maximalIdeal` / `lubinTateSMul_mem_maximalIdeal` — the evaluated
  operations stay in the maximal ideal; proved.
* `lubinTateAdd_comm` / `lubinTateAdd_assoc` / `lubinTateAdd_zero` / `zero_lubinTateAdd`
  / `lubinTateAdd_neg` / `lubinTateAdd_right_cancel` — the evaluated abelian-group laws;
  proved.
* `lubinTateSMul_smul` / `lubinTateSMul_add` / `lubinTateSMul_lubinTateAdd` /
  `lubinTateSMul_one` / `lubinTateSMul_zero` / `lubinTateSMul_map_zero` — the evaluated
  module laws; proved.
* `lubinTateSMul_eq_zero_iff` / `lubinTateSMul_sub_eq_zero` — unit scalars kill nothing,
  and coincident scalars differ by an annihilator; proved.
* `eval₂_algEquiv` — the `K`-automorphisms commute with evaluation; proved.
* `eval₂_subst_collapse` — evaluation of a substituted series collapses to evaluation at
  the evaluated family; proved.
* `hasEval_of_mem_maximalIdeal` — a finite maximal-ideal family is an evaluation family;
  proved.

## Implementation notes

Uniform structures appear only through `letI`: the coefficient integers carry the discrete
uniformity — under which every coefficient map is continuous and
`MvPowerSeries.eval₂_subst` applies — and the target integers the right uniformity of
their additive group, complete by compactness. The topology clash this invites is real:
the ambient subtype topology wins unification against the staged one, so the coefficient
continuity is pinned as `@Continuous _ _ uK.toTopologicalSpace uE.toTopologicalSpace`
against named `letI`s. Membership in the maximal ideal follows the sum: every evaluated
monomial of positive degree carries an ideal factor, the constant one vanishes, and the
ideal is closed because it is open. The equivariance is Mathlib's
`MvPowerSeries.comp_eval₂` at the restricted automorphism, whose coefficient side is the
tower identity `σ ∘ algebraMap = algebraMap`. The tree's other substitution-value
transfer, `Atlas.Knowledge.PowerSeriesCompositionValue`, lives across a real boundary —
rational coefficients over a complete normed field, where that item's implementation
notes record that Mathlib's `eval₂` is unusable and the value is a `tsum` — so the two
theorems are correctly separate, not one general lemma awaiting unification.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
variable (E : Type*) [Field E] [ValuativeRel E] [TopologicalSpace E] [Algebra K E]
  [ValuativeExtension K E] [FiniteDimensional K E] [IsMixedCharLocalField E]

variable {π : ↥𝒪[K]}

/-- The **evaluated formal-group addition** on the integers of the extension
([Milne 2020, Chap. I, §2, Cor. 2.17 and the remark following it, p.34][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/CompletedEvaluation.lean:109`][Yamaguchi2026]). -/
noncomputable def lubinTateAdd (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    (x y : ↥𝒪[E]) : ↥𝒪[E] :=
  letI : UniformSpace ↥𝒪[K] := ⊥
  letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace _
  MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![x, y]
    (lubinTateFormalGroupPowerSeries hπ e)

/-- The **evaluated scalar action**
([Milne 2020, Chap. I, §2, Cor. 2.17 and the remark following it, p.34][MilneCFT]). -/
noncomputable def lubinTateSMul (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    (a : ↥𝒪[K]) (x : ↥𝒪[E]) : ↥𝒪[E] :=
  letI : UniformSpace ↥𝒪[K] := ⊥
  letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace _
  MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) (fun _ : Unit => x)
    (lubinTateScalar hπ e a)

omit [FiniteDimensional K E] in
/-- A finite family of maximal-ideal elements is an evaluation family. -/
theorem hasEval_of_mem_maximalIdeal {σ : Type*} [Finite σ] {v : σ → ↥𝒪[E]}
    (hv : ∀ s, v s ∈ 𝓂[E]) : MvPowerSeries.HasEval v where
  hpow s := isTopologicallyNilpotent_of_mem_maximalIdeal E (hv s)
  tendsto_zero := by simp [Filter.cofinite_eq_bot]

omit [TopologicalSpace K] [IsMixedCharLocalField K] [FiniteDimensional K E] in
/-- The **evaluation of a substituted series** at maximal-ideal points **collapses** to
the evaluation at the evaluated family — `MvPowerSeries.eval₂_subst` staged. -/
theorem eval₂_subst_collapse {σ τ : Type*} [Finite σ] [Finite τ]
    {v : σ → ↥𝒪[E]} (hv : ∀ s, v s ∈ 𝓂[E])
    (g : τ → MvPowerSeries σ ↥𝒪[K])
    (hg0 : ∀ i, MvPowerSeries.constantCoeff (g i) = 0)
    (F : MvPowerSeries τ ↥𝒪[K]) :
    (letI : UniformSpace ↥𝒪[K] := ⊥
     letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace _
     MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) v (MvPowerSeries.subst g F)) =
    (letI : UniformSpace ↥𝒪[K] := ⊥
     letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace _
     MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E])
      (fun i => MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) v (g i)) F) := by
  letI uK : UniformSpace ↥𝒪[K] := ⊥
  haveI : DiscreteUniformity ↥𝒪[K] := by infer_instance
  letI uE : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  haveI : IsUniformAddGroup ↥𝒪[E] := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace ↥𝒪[E] := complete_of_compact
  exact MvPowerSeries.eval₂_subst
    (MvPowerSeries.hasSubst_of_constantCoeff_zero hg0)
    (hasEval_of_mem_maximalIdeal E hv) F

omit [TopologicalSpace K] [IsMixedCharLocalField K] [FiniteDimensional K E] in
/-- **Evaluation of a constant-term-zero series at maximal-ideal points lands in the
maximal ideal**: every monomial does, and the ideal is closed
([Milne 2020, Chap. I, §2, the remark after Cor. 2.17, p.34][MilneCFT]). -/
theorem eval₂_mem_maximalIdeal {σ : Type*} [Finite σ]
    {F : MvPowerSeries σ ↥𝒪[K]}
    (hF : MvPowerSeries.constantCoeff F = 0) {v : σ → ↥𝒪[E]}
    (hv : ∀ s, v s ∈ 𝓂[E]) :
    (letI : UniformSpace ↥𝒪[K] := ⊥
     letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace _
     MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) v F) ∈ 𝓂[E] := by
  letI uK : UniformSpace ↥𝒪[K] := ⊥
  haveI : DiscreteUniformity ↥𝒪[K] := by infer_instance
  letI uE : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  haveI : IsUniformAddGroup ↥𝒪[E] := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace ↥𝒪[E] := complete_of_compact
  have hb : MvPowerSeries.HasEval v := hasEval_of_mem_maximalIdeal E hv
  haveI hdt : @DiscreteTopology ↥𝒪[K] uK.toTopologicalSpace := inferInstance
  have hφc : @Continuous _ _ uK.toTopologicalSpace uE.toTopologicalSpace
      (algebraMap ↥𝒪[K] ↥𝒪[E]) :=
    @continuous_of_discreteTopology _ uK.toTopologicalSpace hdt _
      uE.toTopologicalSpace _
  have hsum := MvPowerSeries.hasSum_eval₂ hφc hb F
  have hclosed : IsClosed ((𝓂[E] : Ideal ↥𝒪[E]) : Set ↥𝒪[E]) := by
    refine AddSubgroup.isClosed_of_isOpen (𝓂[E] : Ideal ↥𝒪[E]).toAddSubgroup ?_
    have h1 := (hasBasis_nhds_zero_integer E).mem_of_mem (i := 1) trivial
    have h2 : ((𝓂[E] ^ 1 : Ideal ↥𝒪[E]) : Set ↥𝒪[E]) =
        ((𝓂[E] : Ideal ↥𝒪[E]) : Set ↥𝒪[E]) := by rw [pow_one]
    rw [h2] at h1
    exact (𝓂[E] : Ideal ↥𝒪[E]).toAddSubgroup.isOpen_of_mem_nhds h1
  have hterm : ∀ d : σ →₀ ℕ,
      (algebraMap ↥𝒪[K] ↥𝒪[E]) (MvPowerSeries.coeff d F) *
        (d.prod fun s e => (v s) ^ e) ∈ 𝓂[E] := by
    intro d
    rcases eq_or_ne d 0 with rfl | hd0
    · rw [show MvPowerSeries.coeff (0 : σ →₀ ℕ) F =
        MvPowerSeries.constantCoeff F from rfl, hF, map_zero, zero_mul]
      exact Ideal.zero_mem _
    · obtain ⟨s, hs⟩ := d.support_nonempty_iff.mpr hd0
      refine Ideal.mul_mem_left _ _ ?_
      have hmem : (v s) ^ (d s) ∈ 𝓂[E] :=
        Ideal.pow_mem_of_mem _ (hv s) _
          (Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hs))
      classical
      rw [Finsupp.prod, ← Finset.prod_erase_mul _ _ hs]
      exact Ideal.mul_mem_left _ _ hmem
  refine hclosed.mem_of_tendsto hsum ?_
  exact Filter.Eventually.of_forall fun s => sum_mem fun d _ => hterm d

omit [FiniteDimensional K E] in
/-- **The evaluated addition stays in the maximal ideal**
([Milne 2020, Chap. I, §2, the remark after Cor. 2.17, p.34][MilneCFT]). -/
theorem lubinTateAdd_mem_maximalIdeal (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    {x y : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) (hy : y ∈ 𝓂[E]) :
    lubinTateAdd K E hπ e x y ∈ 𝓂[E] :=
  eval₂_mem_maximalIdeal K E
    (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).constantCoeff_eq_zero
    (fun s => by fin_cases s <;> assumption)

omit [FiniteDimensional K E] in
/-- **The evaluated scalar stays in the maximal ideal**
([Milne 2020, Chap. I, §2, the remark after Cor. 2.17, p.34][MilneCFT]). -/
theorem lubinTateSMul_mem_maximalIdeal (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    (a : ↥𝒪[K]) {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) :
    lubinTateSMul K E hπ e a x ∈ 𝓂[E] :=
  eval₂_mem_maximalIdeal K E
    (lubinTateScalar_hasLinearTerm hπ e a).constantCoeff_eq_zero
    (fun _ => hx)

omit [TopologicalSpace K] [IsMixedCharLocalField K] [FiniteDimensional K E] in
/-- **Evaluation of a constant-term-zero series at the zero family is zero**: the
substitution of the zero family collapses the series to its constant term
([Milne 2020, Chap. I, §2, the remark after Cor. 2.17, p.34][MilneCFT]). -/
theorem eval₂_apply_zero {σ : Type*} [Finite σ] {F : MvPowerSeries σ ↥𝒪[K]}
    (hF : MvPowerSeries.constantCoeff F = 0) :
    (letI : UniformSpace ↥𝒪[K] := ⊥
     letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace _
     MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) (fun _ : σ => (0 : ↥𝒪[E])) F) = 0 := by
  have hv : ∀ s : Unit, (fun _ : Unit => (0 : ↥𝒪[E])) s ∈ 𝓂[E] := fun _ => Ideal.zero_mem _
  have hcol := eval₂_subst_collapse K E (v := fun _ : Unit => (0 : ↥𝒪[E])) hv
    (fun _ : σ => (0 : MvPowerSeries Unit ↥𝒪[K])) (fun _ => map_zero _) F
  letI : UniformSpace ↥𝒪[K] := ⊥
  letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  have hzero : MvPowerSeries.subst (fun _ : σ => (0 : MvPowerSeries Unit ↥𝒪[K])) F = 0 := by
    rw [show (fun _ : σ => (0 : MvPowerSeries Unit ↥𝒪[K])) = 0 from rfl]
    exact MvPowerSeries.subst_zero_of_constantCoeff_zero hF
  rw [hzero] at hcol
  have h0 : MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) (fun _ : Unit => (0 : ↥𝒪[E]))
      (0 : MvPowerSeries Unit ↥𝒪[K]) = 0 := by
    rw [← map_zero (MvPowerSeries.C : ↥𝒪[K] →+* MvPowerSeries Unit ↥𝒪[K]),
      MvPowerSeries.eval₂_C, map_zero]
  simp only [h0] at hcol
  exact hcol.symm

omit [FiniteDimensional K E] in
/-- **Commutativity of the evaluated addition**
([Milne 2020, Chap. I, §2, Prop. 2.12, p.33][MilneCFT]). -/
theorem lubinTateAdd_comm (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    {x y : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) (hy : y ∈ 𝓂[E]) :
    lubinTateAdd K E hπ e x y = lubinTateAdd K E hπ e y x := by
  unfold lubinTateAdd
  letI : UniformSpace ↥𝒪[K] := ⊥
  haveI : DiscreteUniformity ↥𝒪[K] := by
    infer_instance
  letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  haveI : IsUniformAddGroup ↥𝒪[E] := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace ↥𝒪[E] := complete_of_compact
  have hb : MvPowerSeries.HasEval ![x, y] :=
    hasEval_of_mem_maximalIdeal E (fun s => by fin_cases s <;> assumption)
  have hb' : MvPowerSeries.HasEval ![y, x] :=
    hasEval_of_mem_maximalIdeal E (fun s => by fin_cases s <;> assumption)
  have hswap : MvPowerSeries.HasSubst
      (![MvPowerSeries.X 1, MvPowerSeries.X 0] :
        Fin 2 → MvPowerSeries (Fin 2) ↥𝒪[K]) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun t => by fin_cases t <;> simp)
  conv_lhs => rw [← lubinTateFormalGroupPowerSeries_comm hπ e]
  rw [MvPowerSeries.eval₂_subst hswap hb]
  congr 1
  funext t
  fin_cases t <;> simp [MvPowerSeries.eval₂_X]

omit [FiniteDimensional K E] in
/-- **Associativity of the evaluated addition**: both bracketings evaluate the
series-level associativity at the triple
([Milne 2020, Chap. I, §2, Prop. 2.12, p.33][MilneCFT]). -/
theorem lubinTateAdd_assoc (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    {x y z : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) (hy : y ∈ 𝓂[E]) (hz : z ∈ 𝓂[E]) :
    lubinTateAdd K E hπ e (lubinTateAdd K E hπ e x y) z =
      lubinTateAdd K E hπ e x (lubinTateAdd K E hπ e y z) := by
  have hF0 : MvPowerSeries.constantCoeff (lubinTateFormalGroupPowerSeries hπ e) = 0 :=
    (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).constantCoeff_eq_zero
  have hv : ∀ s : Fin 3, (![x, y, z]) s ∈ 𝓂[E] := fun s => by fin_cases s <;> assumption
  have hpair01 : ∀ i, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
          Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K]) (lubinTateFormalGroupPowerSeries hπ e),
        MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K]) i) = 0 := by
    intro i
    fin_cases i
    · exact MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun t => by fin_cases t <;> simp))
        (fun t => by fin_cases t <;> simp) hF0
    · simp
  have hpair12 : ∀ i, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X 0,
        MvPowerSeries.subst (![MvPowerSeries.X 1, MvPowerSeries.X 2] :
          Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K]) (lubinTateFormalGroupPowerSeries hπ e)] :
          Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K]) i) = 0 := by
    intro i
    fin_cases i
    · simp
    · exact MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun t => by fin_cases t <;> simp))
        (fun t => by fin_cases t <;> simp) hF0
  have hL := eval₂_subst_collapse K E (v := ![x, y, z]) hv
    (![MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K]) (lubinTateFormalGroupPowerSeries hπ e),
      MvPowerSeries.X 2]) hpair01 (lubinTateFormalGroupPowerSeries hπ e)
  have hR := eval₂_subst_collapse K E (v := ![x, y, z]) hv
    (![MvPowerSeries.X 0,
      MvPowerSeries.subst (![MvPowerSeries.X 1, MvPowerSeries.X 2] :
        Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K]) (lubinTateFormalGroupPowerSeries hπ e)])
    hpair12 (lubinTateFormalGroupPowerSeries hπ e)
  have hinner01 := eval₂_subst_collapse K E (v := ![x, y, z]) hv
    (![MvPowerSeries.X 0, MvPowerSeries.X 1]) (fun i => by fin_cases i <;> simp)
    (lubinTateFormalGroupPowerSeries hπ e)
  have hinner12 := eval₂_subst_collapse K E (v := ![x, y, z]) hv
    (![MvPowerSeries.X 1, MvPowerSeries.X 2]) (fun i => by fin_cases i <;> simp)
    (lubinTateFormalGroupPowerSeries hπ e)
  unfold lubinTateAdd
  letI : UniformSpace ↥𝒪[K] := ⊥
  letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  calc _ = _ := rfl
  _ = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E])
        (fun i : Fin 2 => MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![x, y, z]
          ((![MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
              Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K])
              (lubinTateFormalGroupPowerSeries hπ e),
            MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K]) i))
        (lubinTateFormalGroupPowerSeries hπ e) := by
      congr 1
      funext i
      fin_cases i
      · change MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![x, y]
            (lubinTateFormalGroupPowerSeries hπ e) =
          MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![x, y, z]
            (MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
              Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K]) (lubinTateFormalGroupPowerSeries hπ e))
        rw [hinner01]
        congr 1
        funext j
        fin_cases j <;> simp [MvPowerSeries.eval₂_X]
      · change z = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![x, y, z]
            (MvPowerSeries.X 2)
        rw [MvPowerSeries.eval₂_X]
        rfl
  _ = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![x, y, z]
        (MvPowerSeries.subst
          (![MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
              Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K])
              (lubinTateFormalGroupPowerSeries hπ e),
            MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K])
          (lubinTateFormalGroupPowerSeries hπ e)) := hL.symm
  _ = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![x, y, z]
        (MvPowerSeries.subst
          (![MvPowerSeries.X 0,
            MvPowerSeries.subst (![MvPowerSeries.X 1, MvPowerSeries.X 2] :
              Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K])
              (lubinTateFormalGroupPowerSeries hπ e)] :
            Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K])
          (lubinTateFormalGroupPowerSeries hπ e)) := by
      rw [lubinTateFormalGroupPowerSeries_assoc hπ e]
  _ = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E])
        (fun i : Fin 2 => MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![x, y, z]
          ((![MvPowerSeries.X 0,
            MvPowerSeries.subst (![MvPowerSeries.X 1, MvPowerSeries.X 2] :
              Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K])
              (lubinTateFormalGroupPowerSeries hπ e)] :
            Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K]) i))
        (lubinTateFormalGroupPowerSeries hπ e) := hR
  _ = _ := by
      congr 1
      funext i
      fin_cases i
      · change MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![x, y, z]
            (MvPowerSeries.X 0) = x
        rw [MvPowerSeries.eval₂_X]
        rfl
      · change MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![x, y, z]
            (MvPowerSeries.subst (![MvPowerSeries.X 1, MvPowerSeries.X 2] :
              Fin 2 → MvPowerSeries (Fin 3) ↥𝒪[K])
              (lubinTateFormalGroupPowerSeries hπ e)) =
          MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![y, z]
            (lubinTateFormalGroupPowerSeries hπ e)
        rw [hinner12]
        congr 1
        funext j
        fin_cases j <;> simp [MvPowerSeries.eval₂_X]

omit [FiniteDimensional K E] in
/-- **Zero is the identity of the evaluated addition**: the series identity is the
`FormalGroup.add_zero` of the bundled group
([Milne 2020, Chap. I, §2, the remark after Cor. 2.17, p.34][MilneCFT]). -/
theorem lubinTateAdd_zero (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) :
    lubinTateAdd K E hπ e x 0 = x := by
  have hv : ∀ s : Unit, (fun _ : Unit => x) s ∈ 𝓂[E] := fun _ => hx
  have hg0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      ((![MvPowerSeries.X (), 0] : Fin 2 → MvPowerSeries Unit ↥𝒪[K]) i) = 0 := by
    intro i
    fin_cases i <;> simp
  have hcol := eval₂_subst_collapse K E (v := fun _ : Unit => x) hv
    (![MvPowerSeries.X (), 0] : Fin 2 → MvPowerSeries Unit ↥𝒪[K]) hg0
    (lubinTateFormalGroupPowerSeries hπ e)
  have hzero : MvPowerSeries.subst
      (![MvPowerSeries.X (), 0] : Fin 2 → MvPowerSeries Unit ↥𝒪[K])
      (lubinTateFormalGroupPowerSeries hπ e) = MvPowerSeries.X () :=
    (lubinTateFormalGroup hπ e).add_zero
      (PowerSeries.HasSubst.of_constantCoeff_zero (by simp))
  unfold lubinTateAdd
  letI : UniformSpace ↥𝒪[K] := ⊥
  letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  calc _ = _ := rfl
  _ = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E])
        (fun i : Fin 2 => MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E])
          (fun _ : Unit => x)
          ((![MvPowerSeries.X (), 0] : Fin 2 → MvPowerSeries Unit ↥𝒪[K]) i))
        (lubinTateFormalGroupPowerSeries hπ e) := by
      congr 1
      funext i
      fin_cases i
      · change x = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) (fun _ : Unit => x)
          (MvPowerSeries.X ())
        rw [MvPowerSeries.eval₂_X]
      · change (0 : ↥𝒪[E]) = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E])
          (fun _ : Unit => x) 0
        rw [← map_zero (MvPowerSeries.C : ↥𝒪[K] →+* MvPowerSeries Unit ↥𝒪[K]),
          MvPowerSeries.eval₂_C, map_zero]
  _ = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) (fun _ : Unit => x)
        (MvPowerSeries.subst
          (![MvPowerSeries.X (), 0] : Fin 2 → MvPowerSeries Unit ↥𝒪[K])
          (lubinTateFormalGroupPowerSeries hπ e)) := hcol.symm
  _ = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) (fun _ : Unit => x)
        (MvPowerSeries.X ()) := by rw [hzero]
  _ = x := by rw [MvPowerSeries.eval₂_X]

omit [FiniteDimensional K E] in
/-- **Zero is a left identity of the evaluated addition**
([Milne 2020, Chap. I, §2, the remark after Cor. 2.17, p.34][MilneCFT]). -/
theorem zero_lubinTateAdd (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) :
    lubinTateAdd K E hπ e 0 x = x :=
  (lubinTateAdd_comm K E hπ e (Ideal.zero_mem _) hx).trans
    (lubinTateAdd_zero K E hπ e hx)

omit [FiniteDimensional K E] in
/-- **Composition of the evaluated scalars**: `[a] ([b] x) = [a b] x`
([Milne 2020, Chap. I, §2, Prop. 2.15, p.34][MilneCFT]). -/
theorem lubinTateSMul_smul (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    (a b : ↥𝒪[K]) {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) :
    lubinTateSMul K E hπ e a (lubinTateSMul K E hπ e b x) =
      lubinTateSMul K E hπ e (a * b) x := by
  have hv : ∀ s : Unit, (fun _ : Unit => x) s ∈ 𝓂[E] := fun _ => hx
  have hg0 : ∀ i : Unit, MvPowerSeries.constantCoeff
      ((fun _ : Unit => (lubinTateScalar hπ e b : MvPowerSeries Unit ↥𝒪[K])) i) = 0 :=
    fun _ => (lubinTateScalar_hasLinearTerm hπ e b).constantCoeff_eq_zero
  have hcol := eval₂_subst_collapse K E (v := fun _ : Unit => x) hv
    (fun _ : Unit => (lubinTateScalar hπ e b : MvPowerSeries Unit ↥𝒪[K])) hg0
    (lubinTateScalar hπ e a : MvPowerSeries Unit ↥𝒪[K])
  unfold lubinTateSMul
  letI : UniformSpace ↥𝒪[K] := ⊥
  letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  calc _ = _ := rfl
  _ = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) (fun _ : Unit => x)
        (MvPowerSeries.subst
          (fun _ : Unit => (lubinTateScalar hπ e b : MvPowerSeries Unit ↥𝒪[K]))
          (lubinTateScalar hπ e a : MvPowerSeries Unit ↥𝒪[K])) := hcol.symm
  _ = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) (fun _ : Unit => x)
        (lubinTateScalar hπ e (a * b) : MvPowerSeries Unit ↥𝒪[K]) := by
      rw [show MvPowerSeries.subst
          (fun _ : Unit => (lubinTateScalar hπ e b : MvPowerSeries Unit ↥𝒪[K]))
          (lubinTateScalar hπ e a : MvPowerSeries Unit ↥𝒪[K]) =
          (lubinTateScalar hπ e (a * b) : MvPowerSeries Unit ↥𝒪[K]) from ?_]
      rw [← lubinTateScalar_comp hπ e a b, PowerSeries.subst_def]
  _ = _ := rfl

omit [FiniteDimensional K E] in
/-- **The evaluated endomorphism law**: `[a] (x +[e] y) = [a] x +[e] [a] y`
([Milne 2020, Chap. I, §2, Prop. 2.14, p.34][MilneCFT]). -/
theorem lubinTateSMul_lubinTateAdd (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    (a : ↥𝒪[K]) {x y : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) (hy : y ∈ 𝓂[E]) :
    lubinTateSMul K E hπ e a (lubinTateAdd K E hπ e x y) =
      lubinTateAdd K E hπ e (lubinTateSMul K E hπ e a x) (lubinTateSMul K E hπ e a y) := by
  have hF0 : MvPowerSeries.constantCoeff (lubinTateFormalGroupPowerSeries hπ e) = 0 :=
    (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).constantCoeff_eq_zero
  have hv : ∀ s : Fin 2, (![x, y]) s ∈ 𝓂[E] := fun s => by fin_cases s <;> assumption
  -- LHS: [a] evaluated at (F evaluated) = eval of (subst (fun _ => F) [a]) at ![x,y]
  have hLcol := eval₂_subst_collapse K E (v := ![x, y]) hv
    (fun _ : Unit => lubinTateFormalGroupPowerSeries hπ e) (fun _ => hF0)
    (lubinTateScalar hπ e a : MvPowerSeries Unit ↥𝒪[K])
  -- RHS: F evaluated at ([a]-in-variable evaluations) = eval of (subst fam F) at ![x,y]
  have hfam0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      ((fun t : Fin 2 => PowerSeries.subst
        (MvPowerSeries.X t : MvPowerSeries (Fin 2) ↥𝒪[K]) (lubinTateScalar hπ e a)) i) = 0 := by
    intro i
    change MvPowerSeries.constantCoeff (PowerSeries.subst
      (MvPowerSeries.X i : MvPowerSeries (Fin 2) ↥𝒪[K]) (lubinTateScalar hπ e a)) = 0
    rw [PowerSeries.subst_def]
    exact MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp))
      (fun _ => by simp)
      (lubinTateScalar_hasLinearTerm hπ e a).constantCoeff_eq_zero
  have hRcol := eval₂_subst_collapse K E (v := ![x, y]) hv
    (fun t : Fin 2 => PowerSeries.subst
      (MvPowerSeries.X t : MvPowerSeries (Fin 2) ↥𝒪[K]) (lubinTateScalar hπ e a)) hfam0
  have hinner : ∀ t : Fin 2,
      (letI : UniformSpace ↥𝒪[K] := ⊥
       letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace _
       MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![x, y]
        (PowerSeries.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) ↥𝒪[K])
          (lubinTateScalar hπ e a))) =
      lubinTateSMul K E hπ e a ((![x, y]) t) := by
    intro t
    have h := eval₂_subst_collapse K E (v := ![x, y]) hv
      (fun _ : Unit => (MvPowerSeries.X t : MvPowerSeries (Fin 2) ↥𝒪[K]))
      (fun _ => by simp) (lubinTateScalar hπ e a : MvPowerSeries Unit ↥𝒪[K])
    letI : UniformSpace ↥𝒪[K] := ⊥
    letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
    rw [PowerSeries.subst_def]
    calc _ = _ := h
    _ = _ := by
        unfold lubinTateSMul
        congr 1
        funext u
        cases u
        rw [MvPowerSeries.eval₂_X]
  unfold lubinTateSMul lubinTateAdd
  letI : UniformSpace ↥𝒪[K] := ⊥
  letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  calc _ = _ := rfl
  _ = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![x, y]
        (MvPowerSeries.subst (fun _ : Unit => lubinTateFormalGroupPowerSeries hπ e)
          (lubinTateScalar hπ e a : MvPowerSeries Unit ↥𝒪[K])) := by
      rw [hLcol]
  _ = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) ![x, y]
        (MvPowerSeries.subst
          (fun t : Fin 2 => PowerSeries.subst
            (MvPowerSeries.X t : MvPowerSeries (Fin 2) ↥𝒪[K]) (lubinTateScalar hπ e a))
          (lubinTateFormalGroupPowerSeries hπ e)) := by
      rw [show MvPowerSeries.subst (fun _ : Unit => lubinTateFormalGroupPowerSeries hπ e)
          (lubinTateScalar hπ e a : MvPowerSeries Unit ↥𝒪[K]) =
        MvPowerSeries.subst
          (fun t : Fin 2 => PowerSeries.subst
            (MvPowerSeries.X t : MvPowerSeries (Fin 2) ↥𝒪[K]) (lubinTateScalar hπ e a))
          (lubinTateFormalGroupPowerSeries hπ e) from by
        have h := lubinTateScalar_lubinTateFormalGroupPowerSeries hπ e a
        rw [PowerSeries.subst_def] at h
        exact h]
  _ = _ := by
      rw [hRcol]
      congr 1
      funext t
      fin_cases t
      · exact (hinner 0).trans rfl
      · exact (hinner 1).trans rfl

omit [FiniteDimensional K E] in
/-- **The evaluated scalar of one is the identity**
([Milne 2020, Chap. I, §2, Cor. 2.17, p.34][MilneCFT]). -/
theorem lubinTateSMul_one (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    (x : ↥𝒪[E]) :
    lubinTateSMul K E hπ e 1 x = x := by
  unfold lubinTateSMul
  letI uK : UniformSpace ↥𝒪[K] := ⊥
  haveI : DiscreteUniformity ↥𝒪[K] := by infer_instance
  letI uE : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  rw [lubinTateScalar_one hπ e]
  rw [show (PowerSeries.X : PowerSeries ↥𝒪[K]) =
    (MvPowerSeries.X (() : Unit) : MvPowerSeries Unit ↥𝒪[K]) from rfl]
  rw [MvPowerSeries.eval₂_X]

omit [FiniteDimensional K E] in
/-- **The evaluated scalar of the zero scalar is zero**: `[0] x = 0` with no membership
hypothesis — the scalar series itself is zero
([Milne 2020, Chap. I, §2, the remark after Cor. 2.17, p.34][MilneCFT]). -/
theorem lubinTateSMul_zero (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    (x : ↥𝒪[E]) :
    lubinTateSMul K E hπ e 0 x = 0 := by
  unfold lubinTateSMul
  letI : UniformSpace ↥𝒪[K] := ⊥
  letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  rw [lubinTateScalar_zero hπ e]
  rw [← map_zero (MvPowerSeries.C : ↥𝒪[K] →+* MvPowerSeries Unit ↥𝒪[K]),
    MvPowerSeries.eval₂_C, map_zero]

omit [FiniteDimensional K E] in
/-- **The evaluated scalar of the zero point is zero**: `[a] 0 = 0`
([Milne 2020, Chap. I, §2, the remark after Cor. 2.17, p.34][MilneCFT]). -/
theorem lubinTateSMul_map_zero (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    (a : ↥𝒪[K]) :
    lubinTateSMul K E hπ e a 0 = 0 := by
  unfold lubinTateSMul
  exact eval₂_apply_zero K E (lubinTateScalar_hasLinearTerm hπ e a).constantCoeff_eq_zero

omit [FiniteDimensional K E] in
/-- **The evaluated scalar addition**: `[a + b] x = [a] x +[e] [b] x`
([Milne 2020, Chap. I, §2, Prop. 2.15, p.34][MilneCFT]). -/
theorem lubinTateSMul_add (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    (a b : ↥𝒪[K]) {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) :
    lubinTateSMul K E hπ e (a + b) x =
      lubinTateAdd K E hπ e (lubinTateSMul K E hπ e a x) (lubinTateSMul K E hπ e b x) := by
  have hv : ∀ s : Unit, (fun _ : Unit => x) s ∈ 𝓂[E] := fun _ => hx
  have hfam0 : ∀ i : Fin 2, MvPowerSeries.constantCoeff
      ((![(lubinTateScalar hπ e a : MvPowerSeries Unit ↥𝒪[K]),
          (lubinTateScalar hπ e b : MvPowerSeries Unit ↥𝒪[K])] :
        Fin 2 → MvPowerSeries Unit ↥𝒪[K]) i) = 0 := by
    intro i
    fin_cases i
    · exact (lubinTateScalar_hasLinearTerm hπ e a).constantCoeff_eq_zero
    · exact (lubinTateScalar_hasLinearTerm hπ e b).constantCoeff_eq_zero
  have hcol := eval₂_subst_collapse K E (v := fun _ : Unit => x) hv
    (![(lubinTateScalar hπ e a : MvPowerSeries Unit ↥𝒪[K]),
       (lubinTateScalar hπ e b : MvPowerSeries Unit ↥𝒪[K])] :
      Fin 2 → MvPowerSeries Unit ↥𝒪[K]) hfam0
    (lubinTateFormalGroupPowerSeries hπ e)
  unfold lubinTateSMul lubinTateAdd
  letI : UniformSpace ↥𝒪[K] := ⊥
  letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  calc _ = _ := rfl
  _ = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) (fun _ : Unit => x)
        (MvPowerSeries.subst
          (![(lubinTateScalar hπ e a : MvPowerSeries Unit ↥𝒪[K]),
             (lubinTateScalar hπ e b : MvPowerSeries Unit ↥𝒪[K])] :
            Fin 2 → MvPowerSeries Unit ↥𝒪[K])
          (lubinTateFormalGroupPowerSeries hπ e)) := by
      rw [lubinTateScalar_add hπ e a b]
  _ = MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E])
        (fun i : Fin 2 => MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E])
          (fun _ : Unit => x)
          ((![(lubinTateScalar hπ e a : MvPowerSeries Unit ↥𝒪[K]),
              (lubinTateScalar hπ e b : MvPowerSeries Unit ↥𝒪[K])] :
            Fin 2 → MvPowerSeries Unit ↥𝒪[K]) i))
        (lubinTateFormalGroupPowerSeries hπ e) := hcol
  _ = _ := by
      congr 1
      funext i
      fin_cases i <;> rfl

omit [FiniteDimensional K E] in
/-- **The evaluated negation**: the scalar `-1` inverts the evaluated addition
([Milne 2020, Chap. I, §2, the remark after Cor. 2.17, p.34][MilneCFT]). -/
theorem lubinTateAdd_neg (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) :
    lubinTateAdd K E hπ e x (lubinTateSMul K E hπ e (-1) x) = 0 := by
  have h1 : lubinTateAdd K E hπ e x (lubinTateSMul K E hπ e (-1) x) =
      lubinTateAdd K E hπ e (lubinTateSMul K E hπ e 1 x)
        (lubinTateSMul K E hπ e (-1) x) := by
    rw [lubinTateSMul_one K E hπ e x]
  rw [h1, ← lubinTateSMul_add K E hπ e 1 (-1) hx, add_neg_cancel,
    lubinTateSMul_zero K E hπ e x]

omit [FiniteDimensional K E] in
/-- **Right cancellation of the evaluated addition**, through the negation
([Milne 2020, Chap. I, §2, the remark after Cor. 2.17, p.34][MilneCFT]). -/
theorem lubinTateAdd_right_cancel (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    {x y z : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) (hy : y ∈ 𝓂[E]) (hz : z ∈ 𝓂[E])
    (h : lubinTateAdd K E hπ e x z = lubinTateAdd K E hπ e y z) : x = y := by
  have hnz : lubinTateSMul K E hπ e (-1) z ∈ 𝓂[E] :=
    lubinTateSMul_mem_maximalIdeal K E hπ e (-1) hz
  calc x = lubinTateAdd K E hπ e x 0 := (lubinTateAdd_zero K E hπ e hx).symm
  _ = lubinTateAdd K E hπ e x
        (lubinTateAdd K E hπ e z (lubinTateSMul K E hπ e (-1) z)) := by
      rw [lubinTateAdd_neg K E hπ e hz]
  _ = lubinTateAdd K E hπ e (lubinTateAdd K E hπ e x z)
        (lubinTateSMul K E hπ e (-1) z) :=
      (lubinTateAdd_assoc K E hπ e hx hz hnz).symm
  _ = lubinTateAdd K E hπ e (lubinTateAdd K E hπ e y z)
        (lubinTateSMul K E hπ e (-1) z) := by rw [h]
  _ = lubinTateAdd K E hπ e y
        (lubinTateAdd K E hπ e z (lubinTateSMul K E hπ e (-1) z)) :=
      lubinTateAdd_assoc K E hπ e hy hz hnz
  _ = lubinTateAdd K E hπ e y 0 := by rw [lubinTateAdd_neg K E hπ e hz]
  _ = y := lubinTateAdd_zero K E hπ e hy

omit [FiniteDimensional K E] in
/-- **Unit scalars kill nothing**: for a unit scalar `a`, `[a] x = 0` iff `x = 0`
([Milne 2020, Chap. I, §2, the remark after Cor. 2.17, p.34][MilneCFT]). -/
theorem lubinTateSMul_eq_zero_iff (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    {a : ↥𝒪[K]} (ha : IsUnit a) {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E]) :
    lubinTateSMul K E hπ e a x = 0 ↔ x = 0 := by
  constructor
  · intro h0
    obtain ⟨u, rfl⟩ := ha
    have hchain := lubinTateSMul_smul K E hπ e (↑u⁻¹) (↑u) hx
    rw [h0, lubinTateSMul_map_zero K E hπ e (↑u⁻¹ : ↥𝒪[K]), Units.inv_mul,
      lubinTateSMul_one K E hπ e x] at hchain
    exact hchain.symm
  · rintro rfl
    exact lubinTateSMul_map_zero K E hπ e a

omit [FiniteDimensional K E] in
/-- **Coincident scalars differ by an annihilator**: `[a] x = [b] x` forces
`[a − b] x = 0`
([Milne 2020, Chap. I, §2, the remark after Cor. 2.17, p.34][MilneCFT]). -/
theorem lubinTateSMul_sub_eq_zero (hπ : Irreducible π) (e : LubinTateSeries ↥𝒪[K] π)
    {a b : ↥𝒪[K]} {x : ↥𝒪[E]} (hx : x ∈ 𝓂[E])
    (h : lubinTateSMul K E hπ e a x = lubinTateSMul K E hπ e b x) :
    lubinTateSMul K E hπ e (a - b) x = 0 := by
  have hsub : lubinTateSMul K E hπ e a x =
      lubinTateAdd K E hπ e (lubinTateSMul K E hπ e (a - b) x)
        (lubinTateSMul K E hπ e b x) := by
    rw [← lubinTateSMul_add K E hπ e (a - b) b hx, sub_add_cancel]
  refine lubinTateAdd_right_cancel K E hπ e
    (lubinTateSMul_mem_maximalIdeal K E hπ e (a - b) hx) (Ideal.zero_mem _)
    (lubinTateSMul_mem_maximalIdeal K E hπ e b hx) ?_
  rw [← hsub, h,
    zero_lubinTateAdd K E hπ e (lubinTateSMul_mem_maximalIdeal K E hπ e b hx)]

/-- **The `K`-automorphisms commute with evaluation**: the coefficients are fixed and
the evaluation points transported
([Milne 2020, Chap. I, §3, Lem. 3.5, p.38][MilneCFT];
[Yamaguchi 2026, `LubinTate/FiniteLevel/LevelAutomorphisms.lean:362`][Yamaguchi2026]). -/
theorem eval₂_algEquiv (σ : E ≃ₐ[K] E) {τ : Type*} [Finite τ]
    {v : τ → ↥𝒪[E]} (hv : ∀ s, v s ∈ 𝓂[E]) (F : MvPowerSeries τ ↥𝒪[K]) :
    algEquivIntegerRestrict K E σ
      (letI : UniformSpace ↥𝒪[K] := ⊥
       letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace _
       MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) v F) =
    (letI : UniformSpace ↥𝒪[K] := ⊥
     letI : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace _
     MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E])
      (fun s => algEquivIntegerRestrict K E σ (v s)) F) := by
  letI uK : UniformSpace ↥𝒪[K] := ⊥
  haveI : DiscreteUniformity ↥𝒪[K] := by infer_instance
  letI uE : UniformSpace ↥𝒪[E] := IsTopologicalAddGroup.rightUniformSpace ↥𝒪[E]
  haveI : IsUniformAddGroup ↥𝒪[E] := isUniformAddGroup_of_addCommGroup
  haveI : CompleteSpace ↥𝒪[E] := complete_of_compact
  haveI hdt : @DiscreteTopology ↥𝒪[K] uK.toTopologicalSpace := inferInstance
  have hφc : @Continuous _ _ uK.toTopologicalSpace uE.toTopologicalSpace
      (algebraMap ↥𝒪[K] ↥𝒪[E]) :=
    @continuous_of_discreteTopology _ uK.toTopologicalSpace hdt _
      uE.toTopologicalSpace _
  have hb : MvPowerSeries.HasEval v := hasEval_of_mem_maximalIdeal E hv
  have hσc : Continuous ((algEquivIntegerRestrict K E σ : ↥𝒪[E] ≃+* ↥𝒪[E]) :
      ↥𝒪[E] → ↥𝒪[E]) := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_algEquiv K E σ).comp continuous_subtype_val
  have hcomp := MvPowerSeries.comp_eval₂ hφc hb
    (ε := ((algEquivIntegerRestrict K E σ : ↥𝒪[E] ≃+* ↥𝒪[E]) : ↥𝒪[E] →+* ↥𝒪[E])) hσc
  have happ := congrFun hcomp F
  simp only [Function.comp_apply] at happ
  rw [show (algEquivIntegerRestrict K E σ)
      (MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) v F) =
    ((algEquivIntegerRestrict K E σ : ↥𝒪[E] ≃+* ↥𝒪[E]) :
      ↥𝒪[E] →+* ↥𝒪[E]) (MvPowerSeries.eval₂ (algebraMap ↥𝒪[K] ↥𝒪[E]) v F) from rfl]
  rw [happ]
  congr 1
  · ext c
    have hbase : ((algebraMap ↥𝒪[K] ↥𝒪[E] c : ↥𝒪[E]) : E) = algebraMap K E (c : K) := by
      have h1 := IsScalarTower.algebraMap_apply ↥𝒪[K] ↥𝒪[E] E c
      have h2 := IsScalarTower.algebraMap_apply ↥𝒪[K] K E c
      rw [h1] at h2
      exact h2.symm
    change σ ((algebraMap ↥𝒪[K] ↥𝒪[E] c : ↥𝒪[E]) : E) =
      ((algebraMap ↥𝒪[K] ↥𝒪[E] c : ↥𝒪[E]) : E)
    rw [hbase, AlgEquiv.commutes]

end Atlas.Knowledge
