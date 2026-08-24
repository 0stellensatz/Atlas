import Mathlib
import Atlas.Knowledge.AxSenTate
import Atlas.Knowledge.PadicComplexGaloisAction
import Atlas.Knowledge.TateTwist
import Atlas.Knowledge.TateTwistVanishing

/-!
# semi-invariant independence

The Serre–Tate independence lemma: in a module over `ℂ_[p]` on which an open subgroup of the
absolute Galois group acts semilinearly, elements that transform by distinct powers of the
cyclotomic character are linearly independent over `ℂ_[p]`, as soon as, within each weight,
they are independent over the fixed field. The consumer is the twisted tensor representation
of `Atlas.Knowledge.hodgeTateNumber`: its invariants at weight `i` are the weight-`i`
semi-invariants of the untwisted action, so this lemma bounds all the Hodge–Tate numbers of
a representation at once against the `ℂ_[p]`-dimension of the base-changed space—the
finiteness and the sum bound recorded there both fall out of the single inequality.

## Main statements

* `semiInvariantIndependence` — families of semi-invariants of a semilinear action of an
  open subgroup, independent over the fixed field within each weight, are independent over
  `ℂ_[p]`.
* `SemiInvariantIndependence.linearIndependent_of_vanish` — the engine, with the two
  analytic inputs as hypotheses: vanishing of nonzero-weight semi-invariant scalars, and
  descent of invariant scalars to the fixed field.

## Implementation notes

The statement is about an abstract semilinear action: a family of `ℚ_[p]`-linear maps `T σ`
on a `ℂ_[p]`-module, moving a `ℂ_[p]` scalar by the Galois action on `ℂ_[p]`. That is the
whole structure the argument reads—the twisted tensor actions downstream are instances, and
the lemma sits upstream of the module that defines them, bounding the invariants it is
consumed by. The scalar towers `ℚ_[p] → ℂ_[p]` and fixed field `→ ℂ_[p]` enter as instance
hypotheses because the module is abstract.

The proof is the minimal-length descent of Serre and Tate recast as a strong induction on
the support of a linear relation: normalize the pivot coefficient to `1`, hit the relation
with a group element, subtract the rescaled original, and the pivot term drops out, so the
induction hypothesis kills the difference and every remaining coefficient is a
semi-invariant scalar of some relative weight. Nonzero relative weights die by
`Atlas.Knowledge.tateTwistVanishing`; weight zero descends to the fixed field by the open
case of `Atlas.Knowledge.axSenTate`, where the relation contradicts the per-weight
independence. The engine keeps those two inputs as hypotheses so that the analytic content
and the algebra stay separable; the headline discharges them.

## References

* [BrinonConrad2009] O. Brinon, B. Conrad, *CMI Summer School notes on p-adic Hodge theory
  (preliminary version)*, available at math.stanford.edu/~conrad/papers/notes.pdf, 2009.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

open PadicComplexGaloisAction

namespace SemiInvariantIndependence

variable {p : ℕ} [Fact p.Prime] {H : Subgroup (Field.absoluteGaloisGroup ℚ_[p])}
  {M : Type*} [AddCommGroup M] [Module ℚ_[p] M] [Module ℂ_[p] M]
  [IsScalarTower ℚ_[p] ℂ_[p] M]
  [Module ↥(IntermediateField.fixedField (toGalSubgroup H)) M]
  [IsScalarTower ↥(IntermediateField.fixedField (toGalSubgroup H)) ℂ_[p] M]

/-- The independence engine, its two analytic inputs as hypotheses: a family of
semi-invariants of a semilinear action, independent over the fixed field within each weight,
is independent over `ℂ_[p]`. Strong induction on the support of a relation, the pivot
normalized to `1` so that the twisted difference relation drops it
([Brinon–Conrad 2009, Lemma 2.3.1, p.16][BrinonConrad2009], the minimal-length descent of
its proof). -/
theorem linearIndependent_of_vanish (T : ↥H → M →ₗ[ℚ_[p]] M)
    (hT : ∀ (σ : ↥H) (c : ℂ_[p]) (x : M),
      T σ (c • x) = padicComplexGaloisAction p ↑σ c • T σ x)
    (hvanish : ∀ r : ℤ, r ≠ 0 → ∀ c : ℂ_[p],
      (∀ σ : ↥H, padicComplexGaloisAction p ↑σ c
        = ((TateTwist.padicCyclotomicCharacter p ℚ_[p] σ.1 : ℚ_[p]) ^ r) • c) → c = 0)
    (hfixed : ∀ c : ℂ_[p], (∀ σ : ↥H, padicComplexGaloisAction p ↑σ c = c) →
      ∃ a : ↥(IntermediateField.fixedField (toGalSubgroup H)),
        algebraMap ↥(IntermediateField.fixedField (toGalSubgroup H)) ℂ_[p] a = c)
    {ι : Type*} (y : ι → M) (w : ι → ℤ)
    (hy : ∀ j, ∀ σ : ↥H, T σ (y j)
      = ((TateTwist.padicCyclotomicCharacter p ℚ_[p] σ.1 : ℚ_[p]) ^ (w j)) • y j)
    (hind : ∀ i : ℤ,
      LinearIndependent (R := ↥(IntermediateField.fixedField (toGalSubgroup H)))
        (fun j : {j // w j = i} => y j.1)) :
    LinearIndependent ℂ_[p] y := by
  classical
  set χ : ↥H → ℚ_[p] :=
    fun σ => (TateTwist.padicCyclotomicCharacter p ℚ_[p] σ.1 : ℚ_[p]) with hχdef
  have hχ0 : ∀ σ : ↥H, χ σ ≠ 0 := fun σ => Units.ne_zero _
  rw [linearIndependent_iff']
  suffices h : ∀ n (s : Finset ι), s.card ≤ n → ∀ g : ι → ℂ_[p],
      ∑ j ∈ s, g j • y j = 0 → ∀ j ∈ s, g j = 0 by
    intro s g hg j hj
    exact h s.card s le_rfl g hg j hj
  intro n
  induction n with
  | zero =>
      intro s hcard g _ j hj
      rw [Nat.le_zero, Finset.card_eq_zero] at hcard
      simp [hcard] at hj
  | succ n IH =>
  intro s hcard g hrel j0 hj0
  by_contra hne
  -- normalize the pivot coefficient to `1`
  set g' : ι → ℂ_[p] := fun j => (g j0)⁻¹ * g j with hg'def
  have hg'j0 : g' j0 = 1 := inv_mul_cancel₀ hne
  have hrel' : ∑ j ∈ s, g' j • y j = 0 := by
    have h1 : ∑ j ∈ s, g' j • y j = (g j0)⁻¹ • ∑ j ∈ s, g j • y j := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [hg'def]; rw [mul_smul]
    rw [h1, hrel, smul_zero]
  -- the relation transported by `σ`, through the semilinearity and the eigenvector law
  have htwist : ∀ σ : ↥H, ∑ j ∈ s,
      ((padicComplexGaloisAction p ↑σ (g' j)
        * algebraMap ℚ_[p] ℂ_[p] (χ σ ^ w j)) • y j) = 0 := by
    intro σ
    have happ := congrArg (T σ) hrel'
    rw [map_sum, map_zero] at happ
    calc ∑ j ∈ s, ((padicComplexGaloisAction p ↑σ (g' j)
            * algebraMap ℚ_[p] ℂ_[p] (χ σ ^ w j)) • y j)
        = ∑ j ∈ s, T σ (g' j • y j) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hT, hy j σ, mul_smul, algebraMap_smul]
    _ = 0 := happ
  -- the difference relation drops the pivot, and the inductive hypothesis kills it
  have hsemi : ∀ σ : ↥H, ∀ j ∈ s.erase j0,
      padicComplexGaloisAction p ↑σ (g' j) * algebraMap ℚ_[p] ℂ_[p] (χ σ ^ w j)
        = g' j * algebraMap ℚ_[p] ℂ_[p] (χ σ ^ w j0) := by
    intro σ j hj
    set d : ι → ℂ_[p] := fun j =>
      padicComplexGaloisAction p ↑σ (g' j) * algebraMap ℚ_[p] ℂ_[p] (χ σ ^ w j)
        - g' j * algebraMap ℚ_[p] ℂ_[p] (χ σ ^ w j0) with hddef
    have hdrel : ∑ j ∈ s, d j • y j = 0 := by
      have h1 : ∑ j ∈ s, d j • y j
          = ∑ j ∈ s, ((padicComplexGaloisAction p ↑σ (g' j)
              * algebraMap ℚ_[p] ℂ_[p] (χ σ ^ w j)) • y j)
            - algebraMap ℚ_[p] ℂ_[p] (χ σ ^ w j0) • ∑ j ∈ s, g' j • y j := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hddef, sub_smul, mul_smul, mul_comm (g' j), mul_smul]
      rw [h1, htwist σ, hrel', smul_zero, sub_zero]
    have hd0 : d j0 = 0 := by
      simp only [hddef, hg'j0, map_one, one_mul, sub_self]
    have hdrel' : ∑ j ∈ s.erase j0, d j • y j = 0 := by
      have h2 := Finset.add_sum_erase s (fun j => d j • y j) hj0
      rw [hd0, zero_smul, zero_add] at h2
      rw [h2, hdrel]
    have hcard' : (s.erase j0).card ≤ n := by
      have := Finset.card_erase_of_mem hj0
      omega
    have hdj := IH (s.erase j0) hcard' d hdrel' j hj
    simp only [hddef] at hdj
    exact sub_eq_zero.mp hdj
  -- every non-pivot coefficient is a semi-invariant scalar of the relative weight
  have hsemi' : ∀ j ∈ s.erase j0, ∀ σ : ↥H,
      padicComplexGaloisAction p ↑σ (g' j) = (χ σ ^ (w j0 - w j)) • g' j := by
    intro j hj σ
    have h := hsemi σ j hj
    have hA : algebraMap ℚ_[p] ℂ_[p] (χ σ ^ w j) ≠ 0 := by
      simp only [ne_eq, map_eq_zero]
      exact zpow_ne_zero _ (hχ0 σ)
    rw [Algebra.smul_def, zpow_sub₀ (hχ0 σ), map_div₀, div_mul_eq_mul_div, eq_div_iff hA]
    linear_combination h
  have hzero : ∀ j ∈ s.erase j0, w j ≠ w j0 → g' j = 0 := by
    intro j hj hw
    exact hvanish (w j0 - w j) (sub_ne_zero.mpr hw.symm) (g' j) (fun σ => hsemi' j hj σ)
  have hL : ∀ j ∈ s.erase j0, w j = w j0 →
      ∃ a : ↥(IntermediateField.fixedField (toGalSubgroup H)),
        algebraMap ↥(IntermediateField.fixedField (toGalSubgroup H)) ℂ_[p] a = g' j := by
    intro j hj hw
    refine hfixed (g' j) fun σ => ?_
    have h := hsemi' j hj σ
    rw [hw, sub_self, zpow_zero, one_smul] at h
    exact h
  -- the surviving relation lives at the pivot's weight, over the fixed field
  set t : Finset ι := s.filter (fun j => w j = w j0) with htdef
  have hj0t : j0 ∈ t := Finset.mem_filter.mpr ⟨hj0, rfl⟩
  have hrelt : ∑ j ∈ t, g' j • y j = 0 := by
    rw [← hrel']
    refine Finset.sum_subset (Finset.filter_subset (fun j => w j = w j0) s) ?_
    intro j hjs hjt
    have hw : w j ≠ w j0 := fun h => hjt (Finset.mem_filter.mpr ⟨hjs, h⟩)
    have hjerase : j ∈ s.erase j0 := Finset.mem_erase.mpr ⟨fun h => hw (h ▸ rfl), hjs⟩
    rw [hzero j hjerase hw, zero_smul]
  have hchoice : ∀ j ∈ t,
      ∃ a : ↥(IntermediateField.fixedField (toGalSubgroup H)),
        algebraMap ↥(IntermediateField.fixedField (toGalSubgroup H)) ℂ_[p] a = g' j := by
    intro j hjt
    obtain ⟨hjs, hw⟩ := Finset.mem_filter.mp hjt
    by_cases hjj0 : j = j0
    · subst hjj0
      exact ⟨1, by rw [map_one, hg'j0]⟩
    · exact hL j (Finset.mem_erase.mpr ⟨hjj0, hjs⟩) hw
  choose! a ha using hchoice
  have hmemw : ∀ j ∈ t, w j = w j0 := fun j hj => (Finset.mem_filter.mp hj).2
  have hLrel : ∑ j ∈ t.subtype (fun j => w j = w j0), a j.1 • y (j.1 : ι) = 0 := by
    rw [Finset.sum_subtype_eq_sum_filter (fun i => a i • y i) (p := fun j => w j = w j0),
      Finset.filter_true_of_mem hmemw]
    calc ∑ j ∈ t, a j • y j = ∑ j ∈ t, g' j • y j := by
          refine Finset.sum_congr rfl fun j hj => ?_
          rw [← algebraMap_smul (R := ↥(IntermediateField.fixedField (toGalSubgroup H)))
            ℂ_[p] (a j) (y j), ha j hj]
      _ = 0 := hrelt
  have hall := linearIndependent_iff'.mp (hind (w j0))
    (t.subtype (fun j => w j = w j0)) (fun j => a j.1) hLrel
    ⟨j0, rfl⟩ (Finset.mem_subtype.mpr hj0t)
  have hcontra : (1 : ℂ_[p]) = 0 := by
    rw [← hg'j0, ← ha j0 hj0t, hall, map_zero]
  exact one_ne_zero hcontra

end SemiInvariantIndependence

open SemiInvariantIndependence in
/-- The **Serre–Tate independence lemma**: for a semilinear action of an open subgroup on a
`ℂ_[p]`-module, a family of semi-invariants of the cyclotomic character's powers, linearly
independent over the fixed field within each weight, is linearly independent over
`ℂ_[p]`—the injectivity that bounds every Hodge–Tate number at once
([Brinon–Conrad 2009, Lemma 2.3.1, p.16][BrinonConrad2009];
[Hyeon 2025, §5, p.18][Hyeon2025], where the boundedness of the numbers is used through the
sum over `ℤ`). -/
theorem semiInvariantIndependence (p : ℕ) [Fact p.Prime]
    (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p])))
    {M : Type*} [AddCommGroup M] [Module ℚ_[p] M] [Module ℂ_[p] M]
    [IsScalarTower ℚ_[p] ℂ_[p] M]
    [Module ↥(IntermediateField.fixedField (toGalSubgroup H)) M]
    [IsScalarTower ↥(IntermediateField.fixedField (toGalSubgroup H)) ℂ_[p] M]
    (T : ↥H → M →ₗ[ℚ_[p]] M)
    (hT : ∀ (σ : ↥H) (c : ℂ_[p]) (x : M),
      T σ (c • x) = padicComplexGaloisAction p ↑σ c • T σ x)
    {ι : Type*} (y : ι → M) (w : ι → ℤ)
    (hy : ∀ j, ∀ σ : ↥H, T σ (y j)
      = ((TateTwist.padicCyclotomicCharacter p ℚ_[p] σ.1 : ℚ_[p]) ^ (w j)) • y j)
    (hind : ∀ i : ℤ,
      LinearIndependent (R := ↥(IntermediateField.fixedField (toGalSubgroup H)))
        (fun j : {j // w j = i} => y j.1)) :
    LinearIndependent ℂ_[p] y := by
  refine linearIndependent_of_vanish T hT ?_ ?_ y w hy hind
  · intro r hr c hc
    exact tateTwistVanishing p H hH hr (fun σ hσ => hc ⟨σ, hσ⟩)
  · intro c hc
    exact AxSenTate.exists_algebraMap_eq_of_isOpen p H hH (fun σ hσ => hc ⟨σ, hσ⟩)

end Atlas.Knowledge
