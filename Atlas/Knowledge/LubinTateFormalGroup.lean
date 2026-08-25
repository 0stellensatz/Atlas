import Mathlib
import Atlas.Knowledge.LubinTateIntertwiner
import Atlas.Knowledge.LubinTateSeries

/-!
# Lubin–Tate formal group

The formal group law of a Lubin–Tate series and its scalar endomorphisms, with the whole
module structure, each law a uniqueness instance of the fundamental lemma
`Atlas.Knowledge.existsUnique_lubinTateIntertwiner`: the group law `F_e` is the unique
self-intertwiner with linear term `X + Y`, the scalar `[a]` the one with linear term
`a X`, and every identity — commutativity, associativity, `[a] ∘ [b] = [a b]`,
`[a + b] = F ([a], [b])`, `[c] ∘ F = F ([c], [c])`, `[1] = X`, `[π] = e`,
`[0] = 0` — holds because both sides carry the same linear term and intertwine. This is the algebra that makes the
maximal ideal of a complete extension an `A`-module, the carrier of the torsion towers of
local class field theory.

## Main definitions

* `lubinTateFormalGroupPowerSeries` — the group law `F_e`, linear term `X + Y`.
* `lubinTateScalar` — the scalar series `[a]`, linear term `a X`.
* `lubinTateFormalGroup` — the law bundled into Mathlib's `FormalGroup`, with its
  `IsComm` instance.

## Main statements

* `lubinTateFormalGroupPowerSeries_comm` / `lubinTateFormalGroupPowerSeries_assoc` — the
  group-law identities; proved.
* `lubinTateScalar_comp` / `lubinTateScalar_add` / `lubinTateScalar_lubinTateFormalGroupPowerSeries`
  — the module identities; proved.
* `lubinTateScalar_one` / `lubinTateScalar_pi` / `lubinTateScalar_zero` — the
  normalizations `[1] = X`, `[π] = e`, `[0] = 0`; proved.
* `hasLinearTerm_subst` / `intertwines_subst` — the composition engine: substitution
  composes linear terms and preserves intertwining; proved.

## Implementation notes

The two composition lemmas are the whole method: a composite's difference from its
composed linear form splits into a sum of order-two pieces bounded by
`MvPowerSeries.le_order_subst` and `MvPowerSeries.le_order_mul`, and a composite of
intertwiners intertwines by shuffling `MvPowerSeries.subst_comp_subst_apply` five times.
The scalars are indexed by `Unit` so that `PowerSeries A` is definitionally the carrier
and no conversion intervenes; the binary and ternary laws run over `Fin 2` and `Fin 3`
with explicitly ascribed `![…]` families, since bare vector notation lets the index type
collapse into `ℕ`. Everything is stated over the abstract discrete valuation ring of
`Atlas.Knowledge.LubinTateSeries` — no completeness, no field.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open MvPowerSeries

namespace Atlas.Knowledge

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Finite (IsLocalRing.ResidueField A)] {π : A}

/-- The **Lubin–Tate formal group law**: the unique self-intertwiner of `e` with linear
term `X + Y` ([Milne 2020, Chap. I, §2, Prop. 2.12, p.33][MilneCFT];
[Yamaguchi 2026, `LubinTate/FormalModule/StandardFormalGroup.lean:497`][Yamaguchi2026]). -/
noncomputable def lubinTateFormalGroupPowerSeries (hπ : Irreducible π) (e : LubinTateSeries A π) :
    MvPowerSeries (Fin 2) A :=
  lubinTateIntertwiner hπ e e (fun _ => 1)

/-- The **scalar series** `[a]`: the unique self-intertwiner of `e` with linear term
`a X` — Milne's `[a]_f` ([Milne 2020, Chap. I, §2, Cor. 2.17, p.34][MilneCFT];
[Yamaguchi 2026, `LubinTate/FormalModule/StandardFormalGroup.lean:901`][Yamaguchi2026]). -/
noncomputable def lubinTateScalar (hπ : Irreducible π) (e : LubinTateSeries A π) (a : A) :
    PowerSeries A :=
  lubinTateIntertwiner hπ e e (fun _ : Unit => a)

theorem lubinTateFormalGroupPowerSeries_hasLinearTerm (hπ : Irreducible π)
    (e : LubinTateSeries A π) :
    LubinTateHasLinearTerm (lubinTateFormalGroupPowerSeries hπ e) (fun _ => 1) :=
  lubinTateIntertwiner_hasLinearTerm hπ e e _

theorem lubinTateFormalGroupPowerSeries_intertwines (hπ : Irreducible π) (e : LubinTateSeries A π) :
    LubinTateIntertwines e e (lubinTateFormalGroupPowerSeries hπ e) :=
  lubinTateIntertwiner_intertwines hπ e e _

theorem lubinTateScalar_hasLinearTerm (hπ : Irreducible π) (e : LubinTateSeries A π)
    (a : A) :
    LubinTateHasLinearTerm (lubinTateScalar hπ e a) (fun _ : Unit => a) :=
  lubinTateIntertwiner_hasLinearTerm hπ e e _

theorem lubinTateScalar_intertwines (hπ : Irreducible π) (e : LubinTateSeries A π)
    (a : A) :
    LubinTateIntertwines e e (lubinTateScalar hπ e a) :=
  lubinTateIntertwiner_intertwines hπ e e _

omit [Finite (IsLocalRing.ResidueField A)] in
/-- The Lubin–Tate series, read over the one-variable index, has linear term `π X`. -/
theorem toPowerSeries_hasLinearTerm (e : LubinTateSeries A π) :
    LubinTateHasLinearTerm (e.toPowerSeries : MvPowerSeries Unit A) (fun _ : Unit => π) := by
  refine MvPowerSeries.le_order ?_
  intro d hd
  have hdeg : d.degree < 2 := by exact_mod_cast hd
  have hsingle : d = Finsupp.single () (d ()) := by
    refine Finsupp.ext fun u => ?_
    cases u
    simp
  have hd0 : d.degree = d () := by
    conv_lhs => rw [hsingle]
    rw [Finsupp.degree_single]
  have hval : d () < 2 := hd0 ▸ hdeg
  have hcases : d = 0 ∨ d = Finsupp.single () 1 := by
    rcases (by omega : d () = 0 ∨ d () = 1) with h0 | h1
    · left
      refine Finsupp.ext fun u => ?_
      cases u
      simpa using h0
    · right
      refine Finsupp.ext fun u => ?_
      cases u
      simp [h1]
  rcases hcases with rfl | rfl
  · rw [map_sub, sub_eq_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_lubinTateLinearForm]
    exact e.constantCoeff_eq_zero
  · rw [map_sub, sub_eq_zero, coeff_lubinTateLinearForm_single]
    exact e.coeff_one_eq

omit [Finite (IsLocalRing.ResidueField A)] in
/-- The one-variable insertion over the one-variable index is the series itself. -/
theorem lubinTateInVariable_unit (e : LubinTateSeries A π) :
    lubinTateInVariable (σ := Unit) e () = (e.toPowerSeries : MvPowerSeries Unit A) := by
  have h2 : (fun _ : Unit => (MvPowerSeries.X (() : Unit) : MvPowerSeries Unit A)) =
      (MvPowerSeries.X : Unit → MvPowerSeries Unit A) := by
    funext u
    cases u
    rfl
  have h1 : lubinTateInVariable (σ := Unit) e () =
      PowerSeries.subst (MvPowerSeries.X (() : Unit) : MvPowerSeries Unit A)
        e.toPowerSeries := rfl
  rw [h1, PowerSeries.subst_def, h2, MvPowerSeries.subst_self]
  rfl

omit [Finite (IsLocalRing.ResidueField A)] in
/-- The Lubin–Tate series intertwines itself with itself: both sides are `e ∘ e`. -/
theorem toPowerSeries_intertwines (e : LubinTateSeries A π) :
    LubinTateIntertwines e e (e.toPowerSeries : MvPowerSeries Unit A) := by
  change PowerSeries.subst (e.toPowerSeries : MvPowerSeries Unit A) e.toPowerSeries =
    MvPowerSeries.subst (fun i : Unit => lubinTateInVariable e i)
      (e.toPowerSeries : MvPowerSeries Unit A)
  rw [PowerSeries.subst_def]
  congr 1
  funext u
  cases u
  exact (lubinTateInVariable_unit e).symm

/-- **Multiplication by `π` is the Lubin–Tate series itself**: `e` has the linear term
and the intertwining that define `[π]`
([Milne 2020, Chap. I, §2, Rem. 2.19 (a), p.35][MilneCFT]). -/
theorem lubinTateScalar_pi (hπ : Irreducible π) (e : LubinTateSeries A π) :
    lubinTateScalar hπ e π = e.toPowerSeries :=
  LubinTateIntertwines.eq_of_hasLinearTerm hπ
    (lubinTateScalar_hasLinearTerm hπ e π) (lubinTateScalar_intertwines hπ e π)
    (toPowerSeries_hasLinearTerm e) (toPowerSeries_intertwines e)

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] in
/-- The zero series has linear term `0 · X`: it is its own linear form. -/
private theorem zero_hasLinearTerm :
    LubinTateHasLinearTerm (0 : MvPowerSeries Unit A) (fun _ : Unit => (0 : A)) := by
  have h := lubinTateLinearForm_hasLinearTerm (fun _ : Unit => (0 : A))
  rwa [show lubinTateLinearForm (fun _ : Unit => (0 : A)) = 0 from by
    simp [lubinTateLinearForm]] at h

omit [Finite (IsLocalRing.ResidueField A)] in
/-- The zero series intertwines `e` with itself: both sides collapse to zero. -/
private theorem zero_intertwines (e : LubinTateSeries A π) :
    LubinTateIntertwines e e (0 : MvPowerSeries Unit A) := by
  unfold LubinTateIntertwines
  rw [PowerSeries.subst_def]
  rw [show (fun _ : Unit => (0 : MvPowerSeries Unit A)) = 0 from rfl,
    MvPowerSeries.subst_zero_of_constantCoeff_zero e.constantCoeff_eq_zero,
    ← MvPowerSeries.coe_substAlgHom (hasSubst_lubinTateInVariable e), map_zero]

/-- **The scalar of zero is the zero series**: the zero series has linear term `0 · X`
and intertwines `e` with itself, so the uniqueness of the scalar identifies them
([Milne 2020, Chap. I, §2, Cor. 2.17, p.34][MilneCFT]). -/
theorem lubinTateScalar_zero (hπ : Irreducible π) (e : LubinTateSeries A π) :
    lubinTateScalar hπ e 0 = 0 :=
  LubinTateIntertwines.eq_of_hasLinearTerm hπ
    (lubinTateScalar_hasLinearTerm hπ e 0) (lubinTateScalar_intertwines hπ e 0)
    zero_hasLinearTerm (zero_intertwines e)

section Composition

variable {σ : Type*}

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] in
/-- Transport of the prescribed linear term along an equality of linear forms. -/
theorem LubinTateHasLinearTerm.congr [Fintype σ] {H : MvPowerSeries σ A}
    {L L' : σ → A} (h : LubinTateHasLinearTerm H L) (hLL : L = L') :
    LubinTateHasLinearTerm H L' := hLL ▸ h

variable {τ : Type*}

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] in
/-- The multivariable composite of linear-term series has the composed linear term
([Milne 2020, Chap. I, §2, the closure computations inside Props. 2.12 and 2.14,
pp.33–34][MilneCFT]). -/
theorem hasLinearTerm_subst [Fintype σ] [Fintype τ]
    {F : MvPowerSeries τ A} {M : τ → A} (hF : LubinTateHasLinearTerm F M)
    {fam : τ → MvPowerSeries σ A} {L : τ → σ → A}
    (hfam : ∀ t, LubinTateHasLinearTerm (fam t) (L t)) :
    LubinTateHasLinearTerm (MvPowerSeries.subst fam F)
      (fun i => ∑ t, M t * L t i) := by
  classical
  have hfam0 : ∀ t, MvPowerSeries.constantCoeff (fam t) = 0 :=
    fun t => (hfam t).constantCoeff_eq_zero
  have hfs : MvPowerSeries.HasSubst fam :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hfam0
  have hlinsub : MvPowerSeries.subst fam (lubinTateLinearForm M) =
      ∑ t, MvPowerSeries.C (M t) * fam t := by
    rw [lubinTateLinearForm, ← MvPowerSeries.substAlgHom_apply hfs, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, MvPowerSeries.substAlgHom_apply hfs, MvPowerSeries.substAlgHom_apply hfs,
      MvPowerSeries.subst_C, MvPowerSeries.subst_X hfs]
  have hcomp : (∑ t, MvPowerSeries.C (M t) * lubinTateLinearForm (L t) :
      MvPowerSeries σ A) = lubinTateLinearForm (fun i => ∑ t, M t * L t i) := by
    simp_rw [lubinTateLinearForm, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [← mul_assoc, ← map_mul]
  have hdecF : MvPowerSeries.subst fam F =
      MvPowerSeries.subst fam (lubinTateLinearForm M) +
        MvPowerSeries.subst fam (F - lubinTateLinearForm M) := by
    rw [← MvPowerSeries.subst_add hfs]
    congr 1
    ring
  have harr : MvPowerSeries.subst fam F -
      lubinTateLinearForm (fun i => ∑ t, M t * L t i) =
      (∑ t, MvPowerSeries.C (M t) * (fam t - lubinTateLinearForm (L t))) +
        MvPowerSeries.subst fam (F - lubinTateLinearForm M) := by
    rw [hdecF, hlinsub, ← hcomp]
    rw [show (∑ t, MvPowerSeries.C (M t) * fam t) +
        MvPowerSeries.subst fam (F - lubinTateLinearForm M) -
        ∑ t, MvPowerSeries.C (M t) * lubinTateLinearForm (L t) =
        ((∑ t, MvPowerSeries.C (M t) * fam t) -
          ∑ t, MvPowerSeries.C (M t) * lubinTateLinearForm (L t)) +
        MvPowerSeries.subst fam (F - lubinTateLinearForm M) from by ring]
    rw [← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_sub]
  rw [LubinTateHasLinearTerm, harr]
  refine le_trans (le_min ?_ ?_) MvPowerSeries.min_order_le_add
  · refine le_order_finset_sum _ _ _ fun t _ => ?_
    refine le_trans ?_ MvPowerSeries.le_order_mul
    calc (2 : ℕ∞) ≤ (fam t - lubinTateLinearForm (L t)).order := hfam t
    _ ≤ (MvPowerSeries.C (M t) : MvPowerSeries σ A).order +
        (fam t - lubinTateLinearForm (L t)).order := le_add_self
  · have h1 : (1 : ℕ∞) ≤ ⨅ t, MvPowerSeries.order (fam t) := by
      refine le_iInf fun t => ?_
      exact (hfam t).one_le_order
    have h2 := hF
    rw [LubinTateHasLinearTerm] at h2
    calc (2 : ℕ∞) = 1 * 2 := (one_mul _).symm
    _ ≤ (⨅ t, MvPowerSeries.order (fam t)) *
        MvPowerSeries.order (F - lubinTateLinearForm M) := mul_le_mul' h1 h2
    _ ≤ _ := MvPowerSeries.le_order_subst hfs (F - lubinTateLinearForm M)

omit [Finite (IsLocalRing.ResidueField A)] in
/-- The multivariable composite of intertwining series intertwines
([Milne 2020, Chap. I, §2, the closure computations inside Props. 2.12 and 2.14,
pp.33–34][MilneCFT]). -/
theorem intertwines_subst [Finite σ] [Finite τ] {e : LubinTateSeries A π}
    {F : MvPowerSeries τ A} (hFI : LubinTateIntertwines e e F)
    (hF0 : MvPowerSeries.constantCoeff F = 0)
    {fam : τ → MvPowerSeries σ A} (hfamI : ∀ t, LubinTateIntertwines e e (fam t))
    (hfam0 : ∀ t, MvPowerSeries.constantCoeff (fam t) = 0) :
    LubinTateIntertwines e e (MvPowerSeries.subst fam F) := by
  classical
  have hfs : MvPowerSeries.HasSubst fam :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero hfam0
  have hFs : MvPowerSeries.HasSubst (fun _ : Unit => F) :=
    PowerSeries.hasSubst_iff.mp (PowerSeries.HasSubst.of_constantCoeff_zero hF0)
  have hEsT : MvPowerSeries.HasSubst (fun t : τ => lubinTateInVariable e t) :=
    hasSubst_lubinTateInVariable e
  have hEsS : MvPowerSeries.HasSubst (fun i : σ => lubinTateInVariable e i) :=
    hasSubst_lubinTateInVariable e
  change PowerSeries.subst (MvPowerSeries.subst fam F) e.toPowerSeries =
    MvPowerSeries.subst (fun i : σ => lubinTateInVariable e i)
      (MvPowerSeries.subst fam F)
  calc PowerSeries.subst (MvPowerSeries.subst fam F) e.toPowerSeries
      = MvPowerSeries.subst fam
          (PowerSeries.subst F e.toPowerSeries) := by
        simp only [PowerSeries.subst_def]
        rw [MvPowerSeries.subst_comp_subst_apply hFs hfs]
  _ = MvPowerSeries.subst fam
        (MvPowerSeries.subst (fun t : τ => lubinTateInVariable e t) F) := by rw [hFI]
  _ = MvPowerSeries.subst (fun t : τ => MvPowerSeries.subst fam (lubinTateInVariable e t))
        F := by
        rw [MvPowerSeries.subst_comp_subst_apply hEsT hfs]
  _ = MvPowerSeries.subst (fun t : τ =>
        MvPowerSeries.subst (fun i : σ => lubinTateInVariable e i) (fam t)) F := by
        congr 1
        funext t
        have h1 : MvPowerSeries.subst fam (lubinTateInVariable e t) =
            PowerSeries.subst (fam t) e.toPowerSeries := by
          rw [show lubinTateInVariable e t =
            PowerSeries.subst (MvPowerSeries.X t : MvPowerSeries τ A) e.toPowerSeries
            from rfl]
          simp only [PowerSeries.subst_def]
          rw [MvPowerSeries.subst_comp_subst_apply
            (MvPowerSeries.hasSubst_of_constantCoeff_zero
              (fun _ : Unit => by simp) :
              MvPowerSeries.HasSubst (fun _ : Unit => (MvPowerSeries.X t :
                MvPowerSeries τ A))) hfs]
          congr 1
          funext u
          cases u
          rw [MvPowerSeries.subst_X hfs]
        rw [h1, hfamI t]
  _ = MvPowerSeries.subst (fun i : σ => lubinTateInVariable e i)
        (MvPowerSeries.subst fam F) := by
        rw [MvPowerSeries.subst_comp_subst_apply hfs hEsS]

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] in
/-- The one-variable face of `Atlas.Knowledge.hasLinearTerm_subst`: substituting a
linear-term-`L` series into a linear-term-`c` one-variable series has linear term `c • L`
([Milne 2020, Chap. I, §2, the closure computations inside Props. 2.12 and 2.14,
pp.33–34][MilneCFT]). -/
theorem hasLinearTerm_powerSeries_subst [Fintype σ]
    {H : PowerSeries A} {c : A}
    (hH : LubinTateHasLinearTerm (H : MvPowerSeries Unit A) (fun _ : Unit => c))
    {G : MvPowerSeries σ A} {L : σ → A} (hG : LubinTateHasLinearTerm G L) :
    LubinTateHasLinearTerm (PowerSeries.subst G H) (fun i => c * L i) := by
  have h := hasLinearTerm_subst hH (fam := fun _ : Unit => G) (L := fun _ : Unit => L)
    (fun _ => hG)
  rw [PowerSeries.subst_def]
  exact h.congr (funext fun i => by simp)

omit [Finite (IsLocalRing.ResidueField A)] in
/-- The one-variable face of `Atlas.Knowledge.intertwines_subst`
([Milne 2020, Chap. I, §2, the closure computations inside Props. 2.12 and 2.14,
pp.33–34][MilneCFT]). -/
theorem intertwines_powerSeries_subst [Finite σ] {e : LubinTateSeries A π}
    {H : PowerSeries A}
    (hHI : LubinTateIntertwines e e (H : MvPowerSeries Unit A))
    (hH0 : MvPowerSeries.constantCoeff (H : MvPowerSeries Unit A) = 0)
    {G : MvPowerSeries σ A} (hGI : LubinTateIntertwines e e G)
    (hG0 : MvPowerSeries.constantCoeff G = 0) :
    LubinTateIntertwines e e (PowerSeries.subst G H) := by
  have h := intertwines_subst (e := e) hHI hH0 (fam := fun _ : Unit => G)
    (fun _ => hGI) (fun _ => hG0)
  rw [PowerSeries.subst_def]
  exact h

omit [IsDomain A] [IsDiscreteValuationRing A] [Finite (IsLocalRing.ResidueField A)] in
/-- A variable has the indicator linear term: it is that linear form. -/
theorem X_hasLinearTerm_mv [Fintype σ] [DecidableEq σ] (j : σ) :
    LubinTateHasLinearTerm (MvPowerSeries.X j : MvPowerSeries σ A)
      (fun i => if i = j then 1 else 0) := by
  have hX : (MvPowerSeries.X j : MvPowerSeries σ A) =
      lubinTateLinearForm (fun i => if i = j then 1 else 0) := by
    rw [lubinTateLinearForm, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [if_neg hb]
    · simp
  rw [hX]
  exact lubinTateLinearForm_hasLinearTerm _

omit [Finite (IsLocalRing.ResidueField A)] in
/-- A variable intertwines: both sides are the series in that variable. -/
theorem X_intertwines_mv [Finite σ] (e : LubinTateSeries A π) (j : σ) :
    LubinTateIntertwines e e (MvPowerSeries.X j : MvPowerSeries σ A) := by
  change PowerSeries.subst (MvPowerSeries.X j : MvPowerSeries σ A) e.toPowerSeries =
    MvPowerSeries.subst (fun i : σ => lubinTateInVariable e i)
      (MvPowerSeries.X j : MvPowerSeries σ A)
  rw [MvPowerSeries.subst_X (hasSubst_lubinTateInVariable e)]
  rfl

end Composition

section Laws

/-- **Commutativity of the formal group law**: the swapped series has the same linear
term and intertwines, so uniqueness closes
([Milne 2020, Chap. I, §2, Prop. 2.12, p.33][MilneCFT];
[Yamaguchi 2026, `LubinTate/FormalModule/StandardFormalGroup.lean:625`][Yamaguchi2026]). -/
theorem lubinTateFormalGroupPowerSeries_comm (hπ : Irreducible π) (e : LubinTateSeries A π) :
    MvPowerSeries.subst (![MvPowerSeries.X 1, MvPowerSeries.X 0] :
      Fin 2 → MvPowerSeries (Fin 2) A) (lubinTateFormalGroupPowerSeries hπ e) =
      lubinTateFormalGroupPowerSeries hπ e := by
  have hlin := hasLinearTerm_subst (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e)
    (fam := (![MvPowerSeries.X 1, MvPowerSeries.X 0] :
      Fin 2 → MvPowerSeries (Fin 2) A))
    (L := (![fun i => if i = 1 then 1 else 0, fun i => if i = 0 then 1 else 0] :
      Fin 2 → Fin 2 → A))
    (fun t => by fin_cases t <;> exact X_hasLinearTerm_mv _)
  have hI := intertwines_subst (e := e) (lubinTateFormalGroupPowerSeries_intertwines hπ e)
    (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).constantCoeff_eq_zero
    (fam := (![MvPowerSeries.X 1, MvPowerSeries.X 0] :
      Fin 2 → MvPowerSeries (Fin 2) A))
    (fun t => by fin_cases t <;> exact X_intertwines_mv e _)
    (fun t => by fin_cases t <;> simp)
  have hfun : (fun i : Fin 2 => ∑ t : Fin 2, 1 *
      (![fun i => if i = 1 then 1 else 0, fun i => if i = 0 then 1 else 0] :
        Fin 2 → Fin 2 → A) t i) = fun _ : Fin 2 => (1 : A) := by
    funext i
    fin_cases i <;> simp [Fin.sum_univ_two]
  rw [hfun] at hlin
  exact LubinTateIntertwines.eq_of_hasLinearTerm hπ hlin hI
    (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e)
    (lubinTateFormalGroupPowerSeries_intertwines hπ e)

/-- **Composition of scalars multiplies**: `[a] ∘ [b] = [a b]`
([Milne 2020, Chap. I, §2, Prop. 2.15, p.34][MilneCFT]). -/
theorem lubinTateScalar_comp (hπ : Irreducible π) (e : LubinTateSeries A π) (a b : A) :
    PowerSeries.subst (lubinTateScalar hπ e b) (lubinTateScalar hπ e a) =
      lubinTateScalar hπ e (a * b) := by
  have hlin := hasLinearTerm_powerSeries_subst
    (lubinTateScalar_hasLinearTerm hπ e a) (lubinTateScalar_hasLinearTerm hπ e b)
  have hI := intertwines_powerSeries_subst
    (lubinTateScalar_intertwines hπ e a)
    (lubinTateScalar_hasLinearTerm hπ e a).constantCoeff_eq_zero
    (lubinTateScalar_intertwines hπ e b)
    (lubinTateScalar_hasLinearTerm hπ e b).constantCoeff_eq_zero
  exact LubinTateIntertwines.eq_of_hasLinearTerm hπ hlin hI
    (lubinTateScalar_hasLinearTerm hπ e (a * b))
    (lubinTateScalar_intertwines hπ e (a * b))

/-- **Scalar addition**: `[a + b] = F ([a] X, [b] X)`
([Milne 2020, Chap. I, §2, Prop. 2.15, p.34][MilneCFT]). -/
theorem lubinTateScalar_add (hπ : Irreducible π) (e : LubinTateSeries A π) (a b : A) :
    MvPowerSeries.subst
      (![(lubinTateScalar hπ e a : MvPowerSeries Unit A),
         (lubinTateScalar hπ e b : MvPowerSeries Unit A)] :
        Fin 2 → MvPowerSeries Unit A) (lubinTateFormalGroupPowerSeries hπ e) =
      lubinTateScalar hπ e (a + b) := by
  have hlin := hasLinearTerm_subst (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e)
    (fam := (![(lubinTateScalar hπ e a : MvPowerSeries Unit A),
      (lubinTateScalar hπ e b : MvPowerSeries Unit A)] : Fin 2 → MvPowerSeries Unit A))
    (L := (![fun _ : Unit => a, fun _ : Unit => b] : Fin 2 → Unit → A))
    (fun t => by fin_cases t <;>
      [exact lubinTateScalar_hasLinearTerm hπ e a;
       exact lubinTateScalar_hasLinearTerm hπ e b])
  have hI := intertwines_subst (e := e) (lubinTateFormalGroupPowerSeries_intertwines hπ e)
    (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).constantCoeff_eq_zero
    (fam := (![(lubinTateScalar hπ e a : MvPowerSeries Unit A),
      (lubinTateScalar hπ e b : MvPowerSeries Unit A)] : Fin 2 → MvPowerSeries Unit A))
    (fun t => by fin_cases t <;>
      [exact lubinTateScalar_intertwines hπ e a;
       exact lubinTateScalar_intertwines hπ e b])
    (fun t => by fin_cases t <;>
      [exact (lubinTateScalar_hasLinearTerm hπ e a).constantCoeff_eq_zero;
       exact (lubinTateScalar_hasLinearTerm hπ e b).constantCoeff_eq_zero])
  have hfun : (fun i : Unit => ∑ t : Fin 2, 1 *
      (![fun _ : Unit => a, fun _ : Unit => b] : Fin 2 → Unit → A) t i) =
      fun _ : Unit => a + b := by
    funext i
    simp [Fin.sum_univ_two]
  rw [hfun] at hlin
  exact LubinTateIntertwines.eq_of_hasLinearTerm hπ hlin hI
    (lubinTateScalar_hasLinearTerm hπ e (a + b))
    (lubinTateScalar_intertwines hπ e (a + b))

/-- **Scalars distribute over the law**: `[c] (F (X, Y)) = F ([c] X, [c] Y)` — the
endomorphism property ([Milne 2020, Chap. I, §2, Prop. 2.14, p.34][MilneCFT]). -/
theorem lubinTateScalar_lubinTateFormalGroupPowerSeries (hπ : Irreducible π)
    (e : LubinTateSeries A π)
    (c : A) :
    PowerSeries.subst (lubinTateFormalGroupPowerSeries hπ e) (lubinTateScalar hπ e c) =
      MvPowerSeries.subst
        (fun t : Fin 2 => PowerSeries.subst
          (MvPowerSeries.X t : MvPowerSeries (Fin 2) A) (lubinTateScalar hπ e c))
        (lubinTateFormalGroupPowerSeries hπ e) := by
  have hlinL := hasLinearTerm_powerSeries_subst
    (lubinTateScalar_hasLinearTerm hπ e c) (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e)
  have hIL := intertwines_powerSeries_subst
    (lubinTateScalar_intertwines hπ e c)
    (lubinTateScalar_hasLinearTerm hπ e c).constantCoeff_eq_zero
    (lubinTateFormalGroupPowerSeries_intertwines hπ e)
    (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).constantCoeff_eq_zero
  have hfamlin : ∀ t : Fin 2, LubinTateHasLinearTerm
      (PowerSeries.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) A)
        (lubinTateScalar hπ e c)) (fun i => c * (if i = t then 1 else 0)) :=
    fun t => hasLinearTerm_powerSeries_subst
      (lubinTateScalar_hasLinearTerm hπ e c) (X_hasLinearTerm_mv t)
  have hfamI : ∀ t : Fin 2, LubinTateIntertwines e e
      (PowerSeries.subst (MvPowerSeries.X t : MvPowerSeries (Fin 2) A)
        (lubinTateScalar hπ e c)) :=
    fun t => intertwines_powerSeries_subst
      (lubinTateScalar_intertwines hπ e c)
      (lubinTateScalar_hasLinearTerm hπ e c).constantCoeff_eq_zero
      (X_intertwines_mv e t)
      (by simp)
  have hlinR := hasLinearTerm_subst (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e)
    (fam := fun t : Fin 2 => PowerSeries.subst
      (MvPowerSeries.X t : MvPowerSeries (Fin 2) A) (lubinTateScalar hπ e c))
    (L := fun t i => c * (if i = t then 1 else 0)) hfamlin
  have hIR := intertwines_subst (e := e) (lubinTateFormalGroupPowerSeries_intertwines hπ e)
    (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).constantCoeff_eq_zero
    (fam := fun t : Fin 2 => PowerSeries.subst
      (MvPowerSeries.X t : MvPowerSeries (Fin 2) A) (lubinTateScalar hπ e c))
    hfamI (fun t => (hfamlin t).constantCoeff_eq_zero)
  have hfunL : (fun i : Fin 2 => c * (fun _ : Fin 2 => (1 : A)) i) =
      fun _ : Fin 2 => c := by
    funext i
    simp
  have hfunR : (fun i : Fin 2 => ∑ t : Fin 2, 1 * (c * (if i = t then 1 else 0))) =
      fun _ : Fin 2 => c := by
    funext i
    fin_cases i <;> simp
  rw [hfunL] at hlinL
  rw [hfunR] at hlinR
  exact LubinTateIntertwines.eq_of_hasLinearTerm hπ hlinL hIL hlinR hIR

/-- **Associativity of the formal group law**: both bracketings have linear term
`X₀ + X₁ + X₂` and intertwine
([Milne 2020, Chap. I, §2, Prop. 2.12, p.33][MilneCFT];
[Yamaguchi 2026, `LubinTate/FormalModule/StandardFormalGroup.lean:497`][Yamaguchi2026]). -/
theorem lubinTateFormalGroupPowerSeries_assoc (hπ : Irreducible π) (e : LubinTateSeries A π) :
    MvPowerSeries.subst
      (![MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
          Fin 2 → MvPowerSeries (Fin 3) A) (lubinTateFormalGroupPowerSeries hπ e),
        MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) A)
      (lubinTateFormalGroupPowerSeries hπ e) =
    MvPowerSeries.subst
      (![MvPowerSeries.X 0,
        MvPowerSeries.subst (![MvPowerSeries.X 1, MvPowerSeries.X 2] :
          Fin 2 → MvPowerSeries (Fin 3) A) (lubinTateFormalGroupPowerSeries hπ e)] :
        Fin 2 → MvPowerSeries (Fin 3) A)
      (lubinTateFormalGroupPowerSeries hπ e) := by
  classical
  have hXlin : ∀ j : Fin 3, LubinTateHasLinearTerm
      (MvPowerSeries.X j : MvPowerSeries (Fin 3) A)
      (fun i => if i = j then 1 else 0) := fun j => X_hasLinearTerm_mv j
  have hpairlin : ∀ j k : Fin 3, LubinTateHasLinearTerm
      (MvPowerSeries.subst (![MvPowerSeries.X j, MvPowerSeries.X k] :
        Fin 2 → MvPowerSeries (Fin 3) A) (lubinTateFormalGroupPowerSeries hπ e))
      (fun i => ∑ t : Fin 2, 1 *
        (![fun i => if i = j then 1 else 0, fun i => if i = k then 1 else 0] :
          Fin 2 → Fin 3 → A) t i) :=
    fun j k => hasLinearTerm_subst (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e)
      (fun t => by fin_cases t <;> exact X_hasLinearTerm_mv _)
  have hpairI : ∀ j k : Fin 3, LubinTateIntertwines e e
      (MvPowerSeries.subst (![MvPowerSeries.X j, MvPowerSeries.X k] :
        Fin 2 → MvPowerSeries (Fin 3) A) (lubinTateFormalGroupPowerSeries hπ e)) :=
    fun j k => intertwines_subst (e := e) (lubinTateFormalGroupPowerSeries_intertwines hπ e)
      (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).constantCoeff_eq_zero
      (fun t => by fin_cases t <;> exact X_intertwines_mv e _)
      (fun t => by fin_cases t <;> simp)
  have hlinL := hasLinearTerm_subst (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e)
    (fam := (![MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 3) A) (lubinTateFormalGroupPowerSeries hπ e),
      MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) A))
    (L := (![fun i : Fin 3 => ∑ t : Fin 2, 1 *
        (![fun i => if i = (0 : Fin 3) then 1 else 0,
           fun i => if i = (1 : Fin 3) then 1 else 0] : Fin 2 → Fin 3 → A) t i,
      fun i : Fin 3 => if i = 2 then 1 else 0] : Fin 2 → Fin 3 → A))
    (fun t => by fin_cases t <;>
      [exact hpairlin 0 1; exact X_hasLinearTerm_mv 2])
  have hIL := intertwines_subst (e := e) (lubinTateFormalGroupPowerSeries_intertwines hπ e)
    (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).constantCoeff_eq_zero
    (fam := (![MvPowerSeries.subst (![MvPowerSeries.X 0, MvPowerSeries.X 1] :
        Fin 2 → MvPowerSeries (Fin 3) A) (lubinTateFormalGroupPowerSeries hπ e),
      MvPowerSeries.X 2] : Fin 2 → MvPowerSeries (Fin 3) A))
    (fun t => by fin_cases t <;> [exact hpairI 0 1; exact X_intertwines_mv e 2])
    (fun t => by fin_cases t <;>
      [exact (hpairlin 0 1).constantCoeff_eq_zero; simp])
  have hlinR := hasLinearTerm_subst (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e)
    (fam := (![MvPowerSeries.X 0,
      MvPowerSeries.subst (![MvPowerSeries.X 1, MvPowerSeries.X 2] :
        Fin 2 → MvPowerSeries (Fin 3) A) (lubinTateFormalGroupPowerSeries hπ e)] :
        Fin 2 → MvPowerSeries (Fin 3) A))
    (L := (![fun i : Fin 3 => if i = 0 then 1 else 0,
      fun i : Fin 3 => ∑ t : Fin 2, 1 *
        (![fun i => if i = (1 : Fin 3) then 1 else 0,
           fun i => if i = (2 : Fin 3) then 1 else 0] : Fin 2 → Fin 3 → A) t i] :
        Fin 2 → Fin 3 → A))
    (fun t => by fin_cases t <;>
      [exact X_hasLinearTerm_mv 0; exact hpairlin 1 2])
  have hIR := intertwines_subst (e := e) (lubinTateFormalGroupPowerSeries_intertwines hπ e)
    (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).constantCoeff_eq_zero
    (fam := (![MvPowerSeries.X 0,
      MvPowerSeries.subst (![MvPowerSeries.X 1, MvPowerSeries.X 2] :
        Fin 2 → MvPowerSeries (Fin 3) A) (lubinTateFormalGroupPowerSeries hπ e)] :
        Fin 2 → MvPowerSeries (Fin 3) A))
    (fun t => by fin_cases t <;> [exact X_intertwines_mv e 0; exact hpairI 1 2])
    (fun t => by fin_cases t <;>
      [simp; exact (hpairlin 1 2).constantCoeff_eq_zero])
  have hfunL : (fun i : Fin 3 => ∑ t : Fin 2, 1 *
      (![fun i : Fin 3 => ∑ t : Fin 2, 1 *
        (![fun i => if i = (0 : Fin 3) then 1 else 0,
           fun i => if i = (1 : Fin 3) then 1 else 0] : Fin 2 → Fin 3 → A) t i,
        fun i : Fin 3 => if i = 2 then 1 else 0] : Fin 2 → Fin 3 → A) t i) =
      fun _ : Fin 3 => (1 : A) := by
    funext i
    fin_cases i <;> simp [Fin.sum_univ_two]
  have hfunR : (fun i : Fin 3 => ∑ t : Fin 2, 1 *
      (![fun i : Fin 3 => if i = 0 then 1 else 0,
        fun i : Fin 3 => ∑ t : Fin 2, 1 *
          (![fun i => if i = (1 : Fin 3) then 1 else 0,
             fun i => if i = (2 : Fin 3) then 1 else 0] : Fin 2 → Fin 3 → A) t i] :
        Fin 2 → Fin 3 → A) t i) = fun _ : Fin 3 => (1 : A) := by
    funext i
    fin_cases i <;> simp [Fin.sum_univ_two]
  rw [hfunL] at hlinL
  rw [hfunR] at hlinR
  exact LubinTateIntertwines.eq_of_hasLinearTerm hπ hlinL hIL hlinR hIR

/-- **Multiplication by one is the identity**: the variable has linear term `X` and
intertwines `e` with itself ([Milne 2020, Chap. I, §2, Cor. 2.17, p.34][MilneCFT]). -/
theorem lubinTateScalar_one (hπ : Irreducible π) (e : LubinTateSeries A π) :
    lubinTateScalar hπ e 1 = PowerSeries.X := by
  have hXlin : LubinTateHasLinearTerm (PowerSeries.X : MvPowerSeries Unit A)
      (fun _ : Unit => (1 : A)) :=
    (X_hasLinearTerm_mv (σ := Unit) ()).congr (funext fun i => by simp)
  have hXI : LubinTateIntertwines e e (PowerSeries.X : MvPowerSeries Unit A) :=
    X_intertwines_mv e ()
  exact LubinTateIntertwines.eq_of_hasLinearTerm hπ
    (lubinTateScalar_hasLinearTerm hπ e 1) (lubinTateScalar_intertwines hπ e 1)
    hXlin hXI

end Laws

section Bundle

/-- The **Lubin–Tate formal group**, in Mathlib's own `FormalGroup`: the group law
bundled with its associativity
([Milne 2020, Chap. I, §2, Prop. 2.12, p.33][MilneCFT];
[Yamaguchi 2026, `LubinTate/FormalModule/StandardFormalGroup.lean:497`][Yamaguchi2026]). -/
noncomputable def lubinTateFormalGroup (hπ : Irreducible π) (e : LubinTateSeries A π) :
    FormalGroup A where
  toPowerSeries := lubinTateFormalGroupPowerSeries hπ e
  zero_constantCoeff :=
    (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).constantCoeff_eq_zero
  lin_coeff_X := by
    have := (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).coeff_single 0
    simpa using this
  lin_coeff_Y := by
    have := (lubinTateFormalGroupPowerSeries_hasLinearTerm hπ e).coeff_single 1
    simpa using this
  assoc := by
    have := lubinTateFormalGroupPowerSeries_assoc hπ e
    simpa using this

/-- The Lubin–Tate formal group is **commutative**
([Milne 2020, Chap. I, §2, Prop. 2.12, p.33][MilneCFT];
[Yamaguchi 2026, `LubinTate/FormalModule/StandardFormalGroup.lean:625`][Yamaguchi2026]). -/
instance lubinTateFormalGroup_isComm (hπ : Irreducible π) (e : LubinTateSeries A π) :
    (lubinTateFormalGroup hπ e).IsComm where
  comm := by
    have := lubinTateFormalGroupPowerSeries_comm hπ e
    simpa [lubinTateFormalGroup] using this.symm

end Bundle

end Atlas.Knowledge
