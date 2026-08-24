import Mathlib
import Atlas.Knowledge.AxSenTate
import Atlas.Knowledge.ConjugateDiameterBound
import Atlas.Knowledge.CyclotomicIntegerBasis
import Atlas.Knowledge.CyclotomicNormalizedTraceBound
import Atlas.Knowledge.PadicComplexGaloisAction
import Atlas.Knowledge.TateTwist

/-!
# Tate twist vanishing

Tate's vanishing theorem: `ℂ_[p]` has no invariants in nonzero twists. An element of `ℂ_[p]`
on which an open subgroup of the absolute Galois group acts through a nonzero integer power
of the cyclotomic character `Atlas.Knowledge.TateTwist.padicCyclotomicCharacter` is zero.
Together with the trivial-twist case—`Atlas.Knowledge.axSenTate`, which identifies the actual
fixed points—this computes the invariants of every character twist of `ℂ_[p]` by a power of
the cyclotomic character, and it is the input that makes the independence argument of
`Atlas.Knowledge.semiInvariantIndependence` kill coefficients across distinct weights. That
independence is what bounds the Hodge–Tate numbers of `Atlas.Knowledge.hodgeTateNumber`.

## Main statements

* `tateTwistVanishing` — an element of `ℂ_[p]` that transforms under an open subgroup by a
  nonzero power of the cyclotomic character is zero.
* `TateTwistVanishing.vanish_of_bound` — the master step: vanishing follows from a uniform
  bound on the normalized traces of the level tower.
* `TateTwistVanishing.levelTraceBound` — that bound, extended from the cyclotomic tower of
  `Atlas.Knowledge.cyclotomicNormalizedTraceBound` to the levels over the fixed field.

## Implementation notes

The statement quantifies the transformation law over the elements of an open subgroup `H` of
the absolute Galois group and asserts vanishing outright, rather than phrasing an equality of
invariant submodules: every consumer destructures the submodule statement to exactly this
form, and stating it pointwise keeps the twist a scalar factor rather than a new action. The
openness is essential, not a convenience—the fixed field of `H` must be a finite extension of
`ℚ_[p]` for the descent along the cyclotomic tower to terminate—and the claim is about `H`
through its fixed field alone, the transformation law being inherited by every smaller
subgroup while the conclusion stays the same.

The proof is Tate's, run on the levels `M n`, the fixed fields of `H` intersected with the
fixing subgroups of a coherent tower of `p`-power roots of unity. An element with the
transformation law is fixed by `H` meeting the whole tower's stabilizer, which
`cyclotomicCharacter.spec` places inside the character's kernel, so the
Ax–Sen–Tate theorem approximates it by algebraic elements, and a compactness argument in the
profinite group places each approximant at a finite level. At a fixed level the normalized
trace of the approximants converges; the limit is killed because some level automorphism
carries the character out of the roots of `X ^ r - 1`—at deep enough levels the conjugates
of a primitive root outnumber them—while the traces of the approximants converge back to the
element as the level grows. The trace bound that drives both limits reduces to the
cyclotomic tower's: the level is the compositum of the fixed field with the cyclotomic
layer by the Krull correspondence, and coordinates along a trace-dual basis of the fixed
field are themselves plain traces, bounded with no normalization because conjugation
preserves the spectral norm ([Brinon–Conrad 2009, §14.1, Lem. 14.1.4, p.238, with the
linear-disjointness reduction of p.237][BrinonConrad2009]).

## References

* [BrinonConrad2009] O. Brinon, B. Conrad, *CMI Summer School notes on p-adic Hodge theory
  (preliminary version)*, available at math.stanford.edu/~conrad/papers/notes.pdf, 2009.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

open PadicComplexGaloisAction

namespace TateTwistVanishing

variable {p : ℕ} [Fact p.Prime]

/-- scaffolding: a coherent tower of primitive `p ^ n`th roots of unity in the algebraic
closure—each level a `p`th root of the one below, the level-zero root being `1`. -/
theorem exists_rootTower (p : ℕ) [Fact p.Prime] :
    ∃ ζ : ℕ → PadicAlgCl p, ζ 0 = 1 ∧ (∀ n, IsPrimitiveRoot (ζ n) (p ^ n))
      ∧ ∀ n, (ζ (n + 1)) ^ p = ζ n := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  -- build the sequence by recursion: a primitive seed at level one, then successive roots
  obtain ⟨z₁, hz₁⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ 1)
  have hstep : ∀ n : ℕ, 1 ≤ n → ∀ z : PadicAlgCl p, IsPrimitiveRoot z (p ^ n) →
      ∃ z' : PadicAlgCl p, IsPrimitiveRoot z' (p ^ (n + 1)) ∧ z' ^ p = z := by
    intro n hn z hz
    have hdeg : (Polynomial.X ^ p - Polynomial.C z).degree ≠ 0 := by
      rw [Polynomial.degree_X_pow_sub_C (by omega)]
      exact_mod_cast (by omega : (p : ℤ) ≠ 0)
    obtain ⟨z', hz'⟩ := IsAlgClosed.exists_root (k := PadicAlgCl p) _ hdeg
    have hz'p : z' ^ p = z := by
      have h := hz'
      rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, sub_eq_zero] at h
      exact h
    refine ⟨z', ?_, hz'p⟩
    -- `z'` has order dividing `p ^ (n + 1)` and its `p ^ n`th power is not `1`
    have hpow1 : z' ^ p ^ (n + 1) = 1 := by
      rw [pow_succ', pow_mul, hz'p, hz.pow_eq_one]
    have hne : z' ^ p ^ n ≠ 1 := by
      have hh : z' ^ p ^ n = z ^ p ^ (n - 1) := by
        rw [show p ^ n = p * p ^ (n - 1) by rw [← pow_succ']; congr 1; omega, pow_mul, hz'p]
      rw [hh]
      have h2 : p ^ (n - 1) < p ^ n := Nat.pow_lt_pow_right hp1 (by omega : n - 1 < n)
      exact hz.pow_ne_one_of_pos_of_lt (Nat.pow_pos (by omega : 0 < p)).ne' h2
    -- conclude primitivity: the order is a `p`-power dividing `p ^ (n + 1)` but not `p ^ n`
    have hord_dvd : orderOf z' ∣ p ^ (n + 1) := orderOf_dvd_of_pow_eq_one hpow1
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hord_dvd
    have hj1 : j = n + 1 := by
      by_contra hne'
      exact hne (orderOf_dvd_iff_pow_eq_one.mp
        (hjeq ▸ pow_dvd_pow p (by omega : j ≤ n)))
    have hord : orderOf z' = p ^ (n + 1) := by rw [hjeq, hj1]
    have hprim := IsPrimitiveRoot.orderOf z'
    rwa [hord] at hprim
  -- assemble the sequence by recursion, levels shifted by one past the seed
  let G : (n : ℕ) → {z : PadicAlgCl p // IsPrimitiveRoot z (p ^ (n + 1))} :=
    fun n => Nat.rec (motive := fun k => {z : PadicAlgCl p // IsPrimitiveRoot z (p ^ (k + 1))})
      ⟨z₁, by simpa using hz₁⟩
      (fun k ih => ⟨Classical.choose (hstep (k + 1) (by omega) ih.1 ih.2),
        (Classical.choose_spec (hstep (k + 1) (by omega) ih.1 ih.2)).1⟩) n
  refine ⟨fun n => Nat.rec 1 (fun k _ => (G k).1) n, rfl, ?_, ?_⟩
  · intro n
    cases n with
    | zero => simp
    | succ k => exact (G k).2
  · intro n
    cases n with
    | zero =>
        have h1 := hz₁.pow_eq_one
        rw [pow_one] at h1
        exact h1
    | succ k => exact (Classical.choose_spec (hstep (k + 1) (by omega) (G k).1 (G k).2)).2

/-- scaffolding: an automorphism fixing every `p`-power root of unity lies in the kernel of
the cyclotomic character. -/
theorem padicCyclotomicCharacter_eq_one {σ : Field.absoluteGaloisGroup ℚ_[p]}
    (hσ : ∀ t : PadicAlgCl p, (∃ k : ℕ, t ^ (p ^ k) = 1) → toAlgEquiv σ t = t) :
    TateTwist.padicCyclotomicCharacter p ℚ_[p] σ = 1 := by
  set u : ℤ_[p]ˣ := cyclotomicCharacter (AlgebraicClosure ℚ_[p]) p
    ((σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]).toRingEquiv) with hu
  have huv : ∀ k : ℕ, PadicInt.toZModPow k (u : ℤ_[p]) = PadicInt.toZModPow k ((1 : ℤ_[p])) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · haveI : Subsingleton (ZMod (p ^ 0)) := by rw [pow_zero]; infer_instance
      exact Subsingleton.elim _ _
    obtain ⟨t, ht⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ k)
    have hfix : toAlgEquiv σ t = t := hσ t ⟨k, ht.pow_eq_one⟩
    have hspec := cyclotomicCharacter.spec (L := AlgebraicClosure ℚ_[p]) p
      ((σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]).toRingEquiv)
      t ht.pow_eq_one
    rw [← hu] at hspec
    have hfix' : (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]).toRingEquiv t
        = t := hfix
    rw [hfix'] at hspec
    have hlt : 1 < p ^ k := Nat.one_lt_pow hk.ne' (Fact.out : p.Prime).one_lt
    haveI : NeZero (p ^ k) := ⟨by omega⟩
    have hval : (PadicInt.toZModPow k (u : ℤ_[p])).val = 1 := by
      refine ht.pow_inj (ZMod.val_lt _) hlt ?_
      rw [pow_one, ← hspec]
    have hz : PadicInt.toZModPow k (u : ℤ_[p]) = 1 := by
      have h1 : ((PadicInt.toZModPow k (u : ℤ_[p])).val : ZMod (p ^ k))
          = PadicInt.toZModPow k (u : ℤ_[p]) := by
        rw [ZMod.natCast_val, ZMod.cast_id]
      rw [← h1, hval, Nat.cast_one]
    rw [hz, map_one]
  have huu : u = 1 := Units.ext (PadicInt.ext_of_toZModPow.mp huv)
  change (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom) u = 1
  rw [huu, map_one]

set_option maxHeartbeats 800000 in
-- The conjugate-counting argument elaborates past the default budget: the root-set,
-- adjoin, and finrank machinery all meet in one declaration.
/-- scaffolding: over any finite intermediate field, some automorphism fixing it carries the
cyclotomic character outside the `r`th roots of unity—the conjugates of a deep primitive
root of unity outnumber the roots of unity of bounded order that could parameterize them. -/
theorem exists_zpow_ne_one (M : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] ↥M] {r : ℤ} (hr : r ≠ 0) :
    ∃ σ ∈ M.fixingSubgroup,
      ((TateTwist.padicCyclotomicCharacter p ℚ_[p] σ : ℚ_[p]) ^ r) ≠ 1 := by
  classical
  by_contra hcon
  push Not at hcon
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  -- the roots of unity of order dividing `r` form a finite set
  set Sr : Set ℚ_[p] := {u : ℚ_[p] | u ^ r.natAbs = 1} with hSr
  have hrpos : 0 < r.natAbs := Int.natAbs_pos.mpr hr
  have hSrfin : Sr.Finite := by
    have hsub : Sr ⊆ {u : ℚ_[p] | ((Polynomial.X : Polynomial ℚ_[p]) ^ r.natAbs - 1).IsRoot u} := by
      intro u hu
      have h1 : Polynomial.eval u ((Polynomial.X : Polynomial ℚ_[p]) ^ r.natAbs - 1) = 0 := by
        simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_one]
        rw [hu]
        ring
      exact h1
    refine Set.Finite.subset (Polynomial.finite_setOf_isRoot ?_) hsub
    rw [← Polynomial.C_1]
    exact Polynomial.X_pow_sub_C_ne_zero hrpos 1
  -- a level deep enough that the conjugates outnumber the candidate values
  set N : ℕ := Sr.ncard with hN
  set B : ℕ := Module.finrank ℚ_[p] ↥M * N with hB
  set k : ℕ := B + 1 with hk
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl p) (p ^ k)
  have hζalg : IsIntegral ↥M ζ := (Algebra.IsAlgebraic.isAlgebraic (R := ↥M) ζ).isIntegral
  -- every conjugate of `ζ` over `M` is cut out by a character value in the finite set
  have hcover : ∀ β ∈ (minpoly ↥M ζ).rootSet (PadicAlgCl p),
      ∃ u ∈ Sr, ∃ v : ℤ_[p]ˣ, (v : ℚ_[p]) = u
        ∧ β = ζ ^ ((PadicInt.toZModPow k) (v : ℤ_[p])).val := by
    intro β hβ
    have hβroot : (Polynomial.aeval β) (minpoly ↥M ζ) = 0 :=
      (Polynomial.mem_rootSet.mp hβ).2
    obtain ⟨σ', hσ'⟩ := minpoly.exists_algEquiv_of_root'
      (Algebra.IsAlgebraic.isAlgebraic (R := ↥M) ζ) hβroot
    set σ : Field.absoluteGaloisGroup ℚ_[p] := AlgEquiv.restrictScalars ℚ_[p] σ' with hσdef
    have hσM : σ ∈ M.fixingSubgroup := by
      intro x
      exact σ'.commutes x
    have hspec := cyclotomicCharacter.spec (L := AlgebraicClosure ℚ_[p]) p
      ((σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]).toRingEquiv)
      ζ hζ.pow_eq_one
    refine ⟨((TateTwist.padicCyclotomicCharacter p ℚ_[p] σ : ℚ_[p]ˣ) : ℚ_[p]), ?_, ?_⟩
    · have h1 := hcon σ hσM
      have habs : ((TateTwist.padicCyclotomicCharacter p ℚ_[p] σ : ℚ_[p]))
          ^ (r.natAbs : ℤ) = 1 := by
        rcases Int.natAbs_eq r with h | h
        · rw [← h, h1]
        · rw [show ((r.natAbs : ℤ)) = -r from by omega, zpow_neg, h1, inv_one]
      rw [hSr]
      simp only [Set.mem_setOf_eq]
      rw [← zpow_natCast]
      exact habs
    · refine ⟨cyclotomicCharacter (AlgebraicClosure ℚ_[p]) p
        ((σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]).toRingEquiv), rfl, ?_⟩
      rw [← hσ']
      exact hspec
  -- the conjugates inject into the finite root set, bounding the relative degree
  classical
  set f : PadicAlgCl p → ℚ_[p] := fun β =>
    if h : β ∈ (minpoly ↥M ζ).rootSet (PadicAlgCl p) then (hcover β h).choose else 0 with hf
  have hmaps : Set.MapsTo f ((minpoly ↥M ζ).rootSet (PadicAlgCl p)) Sr := by
    intro β hβ
    rw [hf]
    simp only [dif_pos hβ]
    exact (hcover β hβ).choose_spec.1
  have hinj : Set.InjOn f ((minpoly ↥M ζ).rootSet (PadicAlgCl p)) := by
    intro β1 hβ1 β2 hβ2 hf12
    rw [hf] at hf12
    simp only [dif_pos hβ1, dif_pos hβ2] at hf12
    obtain ⟨v1, hv1, hβv1⟩ := (hcover β1 hβ1).choose_spec.2
    obtain ⟨v2, hv2, hβv2⟩ := (hcover β2 hβ2).choose_spec.2
    have hv12 : v1 = v2 :=
      Units.ext (Subtype.coe_injective (hv1.trans (hf12.trans hv2.symm)))
    rw [hβv1, hβv2, hv12]
  have hcard : ((minpoly ↥M ζ).rootSet (PadicAlgCl p)).ncard ≤ N := by
    rw [hN]
    exact Set.ncard_le_ncard_of_injOn f hmaps hinj hSrfin
  -- the relative degree is the number of conjugates
  haveI : CharZero ↥M := charZero_of_injective_algebraMap (algebraMap ℚ_[p] ↥M).injective
  have hsep : (minpoly ↥M ζ).Separable := (minpoly.irreducible hζalg).separable
  have hsplit : Polynomial.Splits ((minpoly ↥M ζ).map (algebraMap ↥M (PadicAlgCl p))) :=
    IsAlgClosed.splits _
  have hroot_card : ((minpoly ↥M ζ).rootSet (PadicAlgCl p)).ncard
      = (minpoly ↥M ζ).natDegree := by
    rw [Set.ncard_eq_toFinset_card', Set.toFinset_card]
    exact Polynomial.card_rootSet_eq_natDegree hsep hsplit
  -- lower-bound the relative degree through the tower
  have hadj : (minpoly ↥M ζ).natDegree
      = Module.finrank ↥M ↥(IntermediateField.adjoin ↥M {ζ}) :=
    (IntermediateField.adjoin.finrank hζalg).symm
  have hlow : (p ^ k).totient ≤ Module.finrank ℚ_[p] ↥M * (minpoly ↥M ζ).natDegree := by
    haveI hXfd : FiniteDimensional ↥M ↥(IntermediateField.adjoin ↥M {ζ}) :=
      IntermediateField.adjoin.finiteDimensional hζalg
    haveI hXQ : FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ↥M {ζ}) :=
      Module.Finite.trans ↥M _
    have hmem : ∀ x : ↥((IntermediateField.adjoin ℚ_[p] {ζ})),
        (x : PadicAlgCl p) ∈ IntermediateField.adjoin ↥M {ζ} := by
      intro x
      have hle : (IntermediateField.adjoin ℚ_[p] {ζ})
          ≤ (IntermediateField.adjoin ↥M {ζ}).restrictScalars ℚ_[p] := by
        refine IntermediateField.adjoin_le_iff.mpr ?_
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact IntermediateField.mem_adjoin_simple_self ↥M ζ
      exact hle x.2
    let g : ↥((IntermediateField.adjoin ℚ_[p] {ζ})) →ₗ[ℚ_[p]] ↥(IntermediateField.adjoin ↥M {ζ}) :=
      { toFun := fun x => ⟨x.1, hmem x⟩
        map_add' := fun a b => rfl
        map_smul' := fun a b => rfl }
    have hginj : Function.Injective g := fun a b hab =>
      Subtype.ext (congrArg (fun z : ↥(IntermediateField.adjoin ↥M {ζ}) => z.1) hab)
    calc (p ^ k).totient
        = Module.finrank ℚ_[p] ↥((IntermediateField.adjoin ℚ_[p] {ζ})) :=
          (CyclotomicIntegerBasis.finrank_adjoin hζ (by omega : k ≠ 0)).symm
      _ ≤ Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ↥M {ζ}) :=
          LinearMap.finrank_le_finrank_of_injective hginj
      _ = Module.finrank ℚ_[p] ↥M * Module.finrank ↥M ↥(IntermediateField.adjoin ↥M {ζ}) :=
          (Module.finrank_mul_finrank ℚ_[p] ↥M ↥(IntermediateField.adjoin ↥M {ζ})).symm
      _ = Module.finrank ℚ_[p] ↥M * (minpoly ↥M ζ).natDegree := by rw [← hadj]
  -- assemble the numeric contradiction
  have htot : B < (p ^ k).totient := by
    have h2 : B < 2 ^ B := Nat.lt_two_pow_self
    have h3 : (2 : ℕ) ^ B ≤ p ^ B := Nat.pow_le_pow_left (by omega) B
    have h4 : (p ^ k).totient = p ^ B * (p - 1) := by
      rw [hk, Nat.totient_prime_pow (Fact.out : p.Prime) (by omega)]
      norm_num
    have h5 : p ^ B ≤ p ^ B * (p - 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hup : Module.finrank ℚ_[p] ↥M * (minpoly ↥M ζ).natDegree ≤ B := by
    rw [hB]
    have := hroot_card ▸ hcard
    exact Nat.mul_le_mul_left _ this
  omega

/-- scaffolding: the fixing subgroups of the tower levels normalize each other's fixed
fields—conjugating a level automorphism by one of them stays at the level, because an
automorphism carries a root of unity to one of its powers. -/
theorem conj_mem (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    {ζ : PadicAlgCl p} {q : ℕ} (hζ : IsPrimitiveRoot ζ q) (hq : q ≠ 0)
    {σ τ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    (hσ : σ ∈ toGalSubgroup H) (hτH : τ ∈ toGalSubgroup H)
    (hτ : τ ∈ (IntermediateField.adjoin ℚ_[p] {ζ}).fixingSubgroup) :
    σ⁻¹ * τ * σ ∈ toGalSubgroup H ⊓ (IntermediateField.adjoin ℚ_[p] {ζ}).fixingSubgroup := by
  haveI : NeZero q := ⟨hq⟩
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact mul_mem (mul_mem (inv_mem hσ) hτH) hσ
  · -- `σ ζ` is again a `q`th root of unity, hence a power of `ζ`, hence fixed by `τ`
    have hσζ : (σ ζ) ^ q = 1 := by
      rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨i, _, hi⟩ := hζ.eq_pow_of_pow_eq_one hσζ
    have hτσζ : τ (σ ζ) = σ ζ := by
      have hmem : σ ζ ∈ IntermediateField.adjoin ℚ_[p] {ζ} := by
        rw [← hi]
        exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
      exact hτ ⟨σ ζ, hmem⟩
    intro x
    obtain ⟨y, hy⟩ := x
    -- it suffices to fix the generator
    induction hy using IntermediateField.adjoin_induction with
    | mem z hz =>
        rw [Set.mem_singleton_iff] at hz
        subst hz
        change (σ⁻¹ * τ * σ) z = z
        have : σ.symm (τ (σ z)) = σ.symm (σ z) := by rw [hτσζ]
        simpa using this
    | algebraMap z => simp
    | add a b ha hb h1 h2 => simp_all
    | mul a b ha hb h1 h2 => simp_all
    | inv a ha h1 => simp_all

/-- scaffolding: fixing a generator is fixing its adjoined field. -/
theorem mem_fixingSubgroup_adjoin_of_fix {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p}
    {z : PadicAlgCl p} (hz : σ z = z) :
    σ ∈ (IntermediateField.adjoin ℚ_[p] {z}).fixingSubgroup := by
  intro x
  obtain ⟨y, hy⟩ := x
  induction hy using IntermediateField.adjoin_induction with
  | mem w hw =>
      rw [Set.mem_singleton_iff] at hw
      subst hw
      exact hz
  | algebraMap w => simp
  | add a b ha hb h1 h2 => simp_all
  | mul a b ha hb h1 h2 => simp_all
  | inv a ha h1 => simp_all

/-- scaffolding: an element fixed by the intersection of `H` with every level of the
cyclotomic tower is fixed at some nonzero finite level—the levels are a decreasing family
of closed subgroups in a compact group, and the element's own fixing subgroup is an open
set around the intersection. -/
theorem exists_level (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p])))
    (ζ : ℕ → PadicAlgCl p) (hζcoh : ∀ n, (ζ (n + 1)) ^ p = ζ n) {x : PadicAlgCl p}
    (hx : ∀ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, σ ∈ toGalSubgroup H →
      (∀ n, σ ∈ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup) → σ x = x) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ σ ∈ toGalSubgroup H
      ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup, σ x = x := by
  haveI : CompactSpace (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :=
    (inferInstance : CompactSpace (AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]))
  have hxint : IsIntegral ℚ_[p] x :=
    ((PadicAlgCl.isAlgebraic p).isAlgebraic x).isIntegral
  haveI : FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {x}) :=
    IntermediateField.adjoin.finiteDimensional hxint
  have hUopen : IsOpen ((IntermediateField.adjoin ℚ_[p] {x}).fixingSubgroup
      : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) :=
    IntermediateField.fixingSubgroup_isOpen _
  have hlevel_mono : ∀ n : ℕ, IntermediateField.adjoin ℚ_[p] {ζ n}
      ≤ IntermediateField.adjoin ℚ_[p] {ζ (n + 1)} := by
    intro n
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy, ← hζcoh n]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] (ζ (n + 1))) p
  set C : ℕ → Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) := fun n =>
    (toGalSubgroup H ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup
      : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) with hC
  have hCclosed : ∀ n, IsClosed (C n) := by
    intro n
    haveI : FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ n}) :=
      IntermediateField.adjoin.finiteDimensional
        ((PadicAlgCl.isAlgebraic p).isAlgebraic (ζ n)).isIntegral
    have h1 : IsClosed ((toGalSubgroup H : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
        : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) :=
      Subgroup.isClosed_of_isOpen _ hH
    have h2 := IntermediateField.fixingSubgroup_isClosed
      (IntermediateField.adjoin ℚ_[p] {ζ n})
    exact h1.inter h2
  have hCmono : ∀ m n : ℕ, m ≤ n → C n ⊆ C m := by
    intro m n hmn
    have hFn : (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup
        ≤ (IntermediateField.adjoin ℚ_[p] {ζ m}).fixingSubgroup := by
      refine IntermediateField.fixingSubgroup_antitone ?_
      induction hmn with
      | refl => exact le_rfl
      | step h ih => exact le_trans ih (hlevel_mono _)
    intro σ hσ
    exact ⟨hσ.1, hFn hσ.2⟩
  have hsub : (⋂ n, C n)
      ⊆ ((IntermediateField.adjoin ℚ_[p] {x}).fixingSubgroup
        : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) := by
    intro σ hσ
    simp only [Set.mem_iInter] at hσ
    exact mem_fixingSubgroup_adjoin_of_fix (hx σ (hσ 0).1 fun n => (hσ n).2)
  have hexists : ∃ n, C n ⊆ ((IntermediateField.adjoin ℚ_[p] {x}).fixingSubgroup
      : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) := by
    by_contra h
    push Not at h
    have hne : ∀ n, (C n ∩ ((IntermediateField.adjoin ℚ_[p] {x}).fixingSubgroup
        : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))ᶜ).Nonempty := by
      intro n
      obtain ⟨σ, hσ1, hσ2⟩ := Set.not_subset.mp (h n)
      exact ⟨σ, hσ1, hσ2⟩
    have hdir : Directed (· ⊇ ·) fun n => C n
        ∩ ((IntermediateField.adjoin ℚ_[p] {x}).fixingSubgroup
          : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))ᶜ := by
      intro m n
      exact ⟨max m n, Set.inter_subset_inter_left _ (hCmono m _ (le_max_left m n)),
        Set.inter_subset_inter_left _ (hCmono n _ (le_max_right m n))⟩
    have hcl : ∀ n, IsClosed (C n
        ∩ ((IntermediateField.adjoin ℚ_[p] {x}).fixingSubgroup
          : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))ᶜ) :=
      fun n => (hCclosed n).inter hUopen.isClosed_compl
    obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      _ hdir hne (fun n => (hcl n).isCompact) hcl
    simp only [Set.mem_iInter, Set.mem_inter_iff] at hσ
    exact (hσ 0).2 (hsub (Set.mem_iInter.mpr fun n => (hσ n).1))
  obtain ⟨n, hn⟩ := hexists
  refine ⟨max n 1, by omega, ?_⟩
  intro σ hσ
  have hσn : σ ∈ C n := hCmono n (max n 1) (le_max_left n 1) hσ
  exact hn hσn ⟨x, IntermediateField.mem_adjoin_simple_self ℚ_[p] x⟩

/-- scaffolding: the tower of level fixed fields is increasing. -/
theorem level_mono (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (ζ : ℕ → PadicAlgCl p) (hζcoh : ∀ n, (ζ (n + 1)) ^ p = ζ n) {m n : ℕ} (hmn : m ≤ n) :
    IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ m}).fixingSubgroup)
      ≤ IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup) := by
  have hlevel_mono : ∀ k : ℕ, IntermediateField.adjoin ℚ_[p] {ζ k}
      ≤ IntermediateField.adjoin ℚ_[p] {ζ (k + 1)} := by
    intro k
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy, ← hζcoh k]
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] (ζ (k + 1))) p
  have hF : (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup
      ≤ (IntermediateField.adjoin ℚ_[p] {ζ m}).fixingSubgroup := by
    refine IntermediateField.fixingSubgroup_antitone ?_
    induction hmn with
    | refl => exact le_rfl
    | step h ih => exact le_trans ih (hlevel_mono _)
  intro x hx σ
  exact hx ⟨σ.1, σ.2.1, hF σ.2.2⟩

/-- scaffolding: an automorphism of `H` fixing one level carries every higher level's fixed
field into itself—its conjugates by level automorphisms stay level automorphisms. -/
theorem level_stable (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (ζ : ℕ → PadicAlgCl p) (hζprim : ∀ n, IsPrimitiveRoot (ζ n) (p ^ n))
    {σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p} (hσ : σ ∈ toGalSubgroup H) {m : ℕ}
    {x : PadicAlgCl p}
    (hx : x ∈ IntermediateField.fixedField (toGalSubgroup H
      ⊓ (IntermediateField.adjoin ℚ_[p] {ζ m}).fixingSubgroup)) :
    σ x ∈ IntermediateField.fixedField (toGalSubgroup H
      ⊓ (IntermediateField.adjoin ℚ_[p] {ζ m}).fixingSubgroup) := by
  intro τ
  have hconj := conj_mem H (hζprim m) (Nat.pow_pos (Fact.out : p.Prime).pos).ne' hσ τ.2.1 τ.2.2
  have hfix := hx ⟨σ⁻¹ * τ.1 * σ, hconj⟩
  change (σ⁻¹ * τ.1 * σ) x = x at hfix
  change τ.1 (σ x) = σ x
  conv_lhs => rw [show τ.1 (σ x) = σ ((σ⁻¹ * τ.1 * σ) x) by simp [AlgEquiv.mul_apply]]
  rw [hfix]

set_option maxHeartbeats 1600000 in
-- The approximation-and-kill argument is one large declaration; the instance work for the
-- normalized traces at every level does not fit the default budget.
/-- scaffolding, the master step: vanishing follows from a uniform bound on the normalized
traces of the level tower. The element descends to the completed tower by the Ax–Sen–Tate
theorem, each level's trace of it is a limit that the level's own automorphisms kill, and
the traces converge back to the element. -/
theorem vanish_of_bound (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p]))) {r : ℤ} (hr : r ≠ 0)
    {c : ℂ_[p]}
    (hc : ∀ σ ∈ H, padicComplexGaloisAction p σ c
      = ((TateTwist.padicCyclotomicCharacter p ℚ_[p] σ : ℚ_[p]) ^ r) • c)
    (ζ : ℕ → PadicAlgCl p) (hζprim : ∀ n, IsPrimitiveRoot (ζ n) (p ^ n))
    (hζcoh : ∀ n, (ζ (n + 1)) ^ p = ζ n) (n₀ : ℕ) (C : ℝ) (hC : 0 < C)
    (hbound : ∀ n m : ℕ, n₀ ≤ n → n ≤ m → ∀ x : PadicAlgCl p,
      x ∈ IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ m}).fixingSubgroup) →
      ‖(algebraMap ↥(IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) (PadicAlgCl p)
        (Algebra.normalizedTrace ↥(IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) (PadicAlgCl p) x))‖
        ≤ C * ‖x‖) :
    c = 0 := by
  classical
  -- the subgroup fixing the whole tower, and the fixed element's descent to its fixed field
  set Φ : Subgroup (Field.absoluteGaloisGroup ℚ_[p]) :=
    ⨅ n : ℕ, ((IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup
      : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) with hΦ
  have hfixed : ∀ σ ∈ H ⊓ Φ, padicComplexGaloisAction p σ c = c := by
    intro σ hσ
    have hker : TateTwist.padicCyclotomicCharacter p ℚ_[p] σ = 1 := by
      refine padicCyclotomicCharacter_eq_one ?_
      intro t ⟨k, htk⟩
      haveI : NeZero (p ^ k) := ⟨(Nat.pow_pos (Fact.out : p.Prime).pos).ne'⟩
      obtain ⟨i, _, hi⟩ := (hζprim k).eq_pow_of_pow_eq_one htk
      have hζfix : toAlgEquiv σ (ζ k) = ζ k := by
        have hmem := (Subgroup.mem_iInf.mp hσ.2) k
        exact hmem ⟨ζ k, IntermediateField.mem_adjoin_simple_self ℚ_[p] (ζ k)⟩
      rw [← hi, map_pow, hζfix]
    rw [hc σ hσ.1, hker]
    simp
  have hclosed : IsClosed ((H ⊓ Φ : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
      : Set (Field.absoluteGaloisGroup ℚ_[p])) := by
    have h1 : IsClosed (H : Set (Field.absoluteGaloisGroup ℚ_[p])) :=
      Subgroup.isClosed_of_isOpen H hH
    have h2 : IsClosed (Φ : Set (Field.absoluteGaloisGroup ℚ_[p])) := by
      have h3 : IsClosed ((⨅ n : ℕ, ((IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup
          : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) :
            Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
          : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) := by
        rw [Subgroup.coe_iInf]
        refine isClosed_iInter fun n => ?_
        haveI : FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ n}) :=
          IntermediateField.adjoin.finiteDimensional
            ((PadicAlgCl.isAlgebraic p).isAlgebraic (ζ n)).isIntegral
        exact IntermediateField.fixingSubgroup_isClosed _
      exact h3
    exact h1.inter h2
  have hmem_closure : c ∈ closure (((↑) : PadicAlgCl p → ℂ_[p]) ''
      (IntermediateField.fixedField (toGalSubgroup (H ⊓ Φ)) : Set (PadicAlgCl p))) := by
    rw [← axSenTate p (H ⊓ Φ) hclosed]
    exact hfixed
  -- every approximant lives at a finite level at least `n₀`
  have happrox : ∀ ε : ℝ, 0 < ε → ∃ (m : ℕ) (y : PadicAlgCl p), n₀ ≤ m
      ∧ y ∈ IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ m}).fixingSubgroup)
      ∧ ‖c - (y : ℂ_[p])‖ ≤ ε := by
    intro ε hε
    obtain ⟨-, ⟨y, hyF, rfl⟩, hy⟩ := Metric.mem_closure_iff.mp hmem_closure ε hε
    have hylevel : ∃ n : ℕ, n ≠ 0 ∧ ∀ σ ∈ toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup, σ y = y := by
      refine exists_level H hH ζ hζcoh ?_
      intro σ hσH hσF
      have hσΦ : σ ∈ Φ := by
        rw [hΦ]
        exact Subgroup.mem_iInf.mpr hσF
      exact hyF ⟨σ, hσH, hσΦ⟩
    obtain ⟨n, -, hn⟩ := hylevel
    refine ⟨max n n₀, y, le_max_right n n₀, ?_, ?_⟩
    · refine level_mono H ζ hζcoh (le_max_left n n₀) ?_
      intro σ
      exact hn σ.1 σ.2
    · exact le_of_lt (by simpa [dist_eq_norm] using hy)
  -- it suffices to bound the element by every positive multiple of the constant
  have hkey : ∀ ε : ℝ, 0 < ε → ‖c‖ ≤ max 1 C * ε := by
    intro ε hε
    obtain ⟨n, y, hn₀, hymem, hydist⟩ := happrox ε hε
    -- the level's fixed field is finite-dimensional, through the Krull correspondence
    have hopen : IsOpen ((toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup
        : Subgroup (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p))
        : Set (PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)) := by
      haveI : FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ n}) :=
        IntermediateField.adjoin.finiteDimensional
          ((PadicAlgCl.isAlgebraic p).isAlgebraic (ζ n)).isIntegral
      rw [Subgroup.coe_inf]
      exact IsOpen.inter hH (IntermediateField.fixingSubgroup_isOpen _)
    have hKrull : (IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)).fixingSubgroup
        = toGalSubgroup H ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup :=
      InfiniteGalois.fixingSubgroup_fixedField ⟨_, Subgroup.isClosed_of_isOpen _ hopen⟩
    haveI hMfd : FiniteDimensional ℚ_[p] ↥(IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) := by
      refine (InfiniteGalois.isOpen_iff_finite _).mp ?_
      rw [hKrull]
      exact hopen
    -- a level automorphism carrying the character out of the `r`th roots of unity
    obtain ⟨σ', hσ'fix, hσ'χ⟩ := exists_zpow_ne_one (IntermediateField.fixedField
      (toGalSubgroup H ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) hr
    have hσ'inf : σ' ∈ toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup := hKrull ▸ hσ'fix
    -- approximants at every precision, pushed above the level
    have hseq : ∀ j : ℕ, ∃ (m : ℕ) (x : PadicAlgCl p), n ≤ m
        ∧ x ∈ IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ m}).fixingSubgroup)
        ∧ ‖c - (x : ℂ_[p])‖ ≤ 1 / (j + 1) := by
      intro j
      obtain ⟨m, x, _, hxmem, hxd⟩ := happrox (1 / (j + 1)) (by positivity)
      exact ⟨max m n, x, le_max_right m n,
        level_mono H ζ hζcoh (le_max_left m n) hxmem, hxd⟩
    choose mm xx hmmn hxxmem hxxdist using hseq
    set Mn := IntermediateField.fixedField (toGalSubgroup H
      ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup) with hMn
    set R := Algebra.normalizedTrace ↥Mn (PadicAlgCl p) with hR
    set Y : ℕ → ℂ_[p] :=
      fun j => ((algebraMap ↥Mn (PadicAlgCl p) (R (xx j)) : PadicAlgCl p) : ℂ_[p]) with hY
    -- the sequence of level traces converges
    have hxxsub : ∀ i j : ℕ,
        ‖xx j - xx i‖ ≤ max (1 / ((j : ℝ) + 1)) (1 / ((i : ℝ) + 1)) := by
      intro i j
      have hcoe : ((xx j - xx i : PadicAlgCl p) : ℂ_[p])
          = (xx j : ℂ_[p]) - (xx i : ℂ_[p]) :=
        map_sub (algebraMap (PadicAlgCl p) ℂ_[p]) (xx j) (xx i)
      rw [← PadicComplex.norm_extends, hcoe]
      calc ‖((xx j : ℂ_[p])) - ((xx i : ℂ_[p]))‖
          = ‖((xx j : ℂ_[p]) - c) + (c - (xx i : ℂ_[p]))‖ := by
            congr 1
            abel
        _ ≤ max ‖(xx j : ℂ_[p]) - c‖ ‖c - (xx i : ℂ_[p])‖ :=
            IsUltrametricDist.norm_add_le_max _ _
        _ ≤ max (1 / ((j : ℝ) + 1)) (1 / ((i : ℝ) + 1)) := by
            refine max_le_max ?_ (hxxdist i)
            rw [norm_sub_rev]
            exact hxxdist j
    have hRsub : ∀ i j : ℕ,
        ‖(algebraMap ↥Mn (PadicAlgCl p) (R (xx j - xx i)))‖
          ≤ C * max (1 / ((j : ℝ) + 1)) (1 / ((i : ℝ) + 1)) := by
      intro i j
      have hmemij : xx j - xx i ∈ IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ (max (mm j) (mm i))}).fixingSubgroup) :=
        sub_mem (level_mono H ζ hζcoh (le_max_left _ _) (hxxmem j))
          (level_mono H ζ hζcoh (le_max_right _ _) (hxxmem i))
      refine le_trans (hbound n (max (mm j) (mm i)) hn₀
        (le_trans (hmmn j) (le_max_left _ _)) _ hmemij) ?_
      exact mul_le_mul_of_nonneg_left (hxxsub i j) hC.le
    have hYcau : CauchySeq Y := by
      rw [Metric.cauchySeq_iff']
      intro δ hδ
      obtain ⟨N, hN⟩ := exists_nat_gt (C / δ)
      refine ⟨N, fun j hj => ?_⟩
      have h1 : dist (Y j) (Y N) = ‖(algebraMap ↥Mn (PadicAlgCl p) (R (xx j - xx N)))‖ := by
        rw [dist_eq_norm, hY]
        rw [← PadicComplex.norm_extends]
        congr 1
        push_cast [map_sub]
        rfl
      rw [h1]
      refine lt_of_le_of_lt (hRsub N j) ?_
      have h2 : max (1 / ((j : ℝ) + 1)) (1 / ((N : ℝ) + 1)) = 1 / ((N : ℝ) + 1) :=
        max_eq_right (one_div_le_one_div_of_le (by positivity)
          (by exact_mod_cast Nat.succ_le_succ hj))
      rw [h2]
      have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      rw [mul_one_div, div_lt_iff₀ hN1]
      rw [div_lt_iff₀ hδ] at hN
      nlinarith [hN, hδ]
    obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete hYcau
    -- the twisted difference of each approximant is small, and the trace kills the twist
    set χr : ℚ_[p] := ((TateTwist.padicCyclotomicCharacter p ℚ_[p] σ' : ℚ_[p]ˣ) : ℚ_[p]) ^ r
      with hχr
    have hχrnorm : ‖χr‖ = 1 := by
      rw [hχr, norm_zpow]
      have h1 : ‖((TateTwist.padicCyclotomicCharacter p ℚ_[p] σ' : ℚ_[p]ˣ) : ℚ_[p])‖ = 1 := by
        have h2 := PadicInt.norm_units (cyclotomicCharacter (AlgebraicClosure ℚ_[p]) p
          ((σ' : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p]).toRingEquiv))
        rw [PadicInt.norm_def] at h2
        exact h2
      rw [h1, one_zpow]
    have hδpos : 0 < ‖(1 : ℚ_[p]) - χr‖ := by
      rw [norm_pos_iff]
      intro h0
      exact hσ'χ ((sub_eq_zero.mp h0).symm)
    have hkill : ∀ j : ℕ, ‖(1 : ℚ_[p]) - χr‖ * ‖Y j‖ ≤ C * (1 / (j + 1)) := by
      intro j
      set Dj : PadicAlgCl p := toAlgEquiv σ' (xx j) - χr • xx j with hDj
      have hDmem : Dj ∈ IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ (mm j)}).fixingSubgroup) := by
        refine sub_mem (level_stable H ζ hζprim hσ'inf.1 (hxxmem j)) ?_
        rw [Algebra.smul_def]
        exact mul_mem (IntermediateField.algebraMap_mem _ χr) (hxxmem j)
      have hDnorm : ‖Dj‖ ≤ 1 / (j + 1) := by
        rw [← PadicComplex.norm_extends]
        have hDcoe : ((Dj : ℂ_[p]))
            = padicComplexGaloisAction p σ' ((xx j : ℂ_[p])) - χr • ((xx j : ℂ_[p])) := by
          have e1 : ((Dj : ℂ_[p]))
              = ((toAlgEquiv σ' (xx j) : PadicAlgCl p) : ℂ_[p])
                - ((χr • xx j : PadicAlgCl p) : ℂ_[p]) := by
            rw [hDj]
            exact map_sub (algebraMap (PadicAlgCl p) ℂ_[p]) _ _
          have e2 : ((toAlgEquiv σ' (xx j) : PadicAlgCl p) : ℂ_[p])
              = padicComplexGaloisAction p σ' ((xx j : ℂ_[p])) :=
            (padicComplexGaloisAction_coe σ' (xx j)).symm
          have e3 : ((χr • xx j : PadicAlgCl p) : ℂ_[p]) = χr • ((xx j : ℂ_[p])) :=
            map_smul ((IsScalarTower.toAlgHom ℚ_[p] (PadicAlgCl p) ℂ_[p]).toLinearMap)
              χr (xx j)
          rw [e1, e2, e3]
        rw [hDcoe]
        have h1 : padicComplexGaloisAction p σ' ((xx j : ℂ_[p])) - χr • ((xx j : ℂ_[p]))
            = padicComplexGaloisAction p σ' ((xx j : ℂ_[p]) - c)
              + χr • (c - (xx j : ℂ_[p])) := by
          rw [map_sub, hc σ' hσ'inf.1, smul_sub]
          abel
        rw [h1]
        refine le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le ?_ ?_)
        · have hiso := (isometry_algEquiv σ').dist_eq ((xx j : ℂ_[p]) - c) 0
          rw [dist_eq_norm, dist_eq_norm, map_zero, sub_zero, sub_zero] at hiso
          rw [show ‖padicComplexGaloisAction p σ' ((xx j : ℂ_[p]) - c)‖
              = ‖(xx j : ℂ_[p]) - c‖ from hiso, norm_sub_rev]
          exact hxxdist j
        · rw [norm_smul, hχrnorm, one_mul]
          exact hxxdist j
      have htrace : R (toAlgEquiv σ' (xx j)) = R (xx j) := by
        have hcomp := Algebra.normalizedTrace_comp_algHom (F := ↥Mn) (K := PadicAlgCl p)
          ((IntermediateField.fixingSubgroupEquiv Mn ⟨σ', hσ'fix⟩).toAlgHom)
        have happ := LinearMap.congr_fun hcomp (xx j)
        exact happ
      have hRsmul : R (χr • xx j) = χr • R (xx j) := by
        rw [← algebraMap_smul (↥Mn) χr (xx j), map_smul, algebraMap_smul]
      have halg : ∀ v : ↥Mn, algebraMap ↥Mn (PadicAlgCl p) (χr • v)
          = χr • algebraMap ↥Mn (PadicAlgCl p) v := fun v =>
        map_smul ((IsScalarTower.toAlgHom ℚ_[p] ↥Mn (PadicAlgCl p)).toLinearMap) χr v
      have hRD : algebraMap ↥Mn (PadicAlgCl p) (R Dj)
          = ((1 : ℚ_[p]) - χr) • (algebraMap ↥Mn (PadicAlgCl p) (R (xx j))) := by
        rw [hDj, map_sub, htrace, hRsmul, map_sub, halg, sub_smul, one_smul]
      have hRDnorm : ‖algebraMap ↥Mn (PadicAlgCl p) (R Dj)‖ ≤ C * (1 / (j + 1)) :=
        le_trans (hbound n (mm j) hn₀ (hmmn j) Dj hDmem)
          (mul_le_mul_of_nonneg_left hDnorm hC.le)
      have hYnorm : ‖Y j‖ = ‖algebraMap ↥Mn (PadicAlgCl p) (R (xx j))‖ := by
        simp only [hY]
        exact PadicComplex.norm_extends (p := p) _
      rw [hYnorm, ← norm_smul, ← hRD]
      exact hRDnorm
    -- the limit of the traces is zero
    have hz0 : z = 0 := by
      have h1 : Filter.Tendsto (fun j => ‖(1 : ℚ_[p]) - χr‖ * ‖Y j‖) Filter.atTop
          (nhds (‖(1 : ℚ_[p]) - χr‖ * ‖z‖)) := Filter.Tendsto.const_mul _ hz.norm
      have h2 : Filter.Tendsto (fun j : ℕ => C * (1 / (j + 1) : ℝ)) Filter.atTop (nhds 0) := by
        rw [show (0 : ℝ) = C * 0 by ring]
        exact Filter.Tendsto.const_mul _ tendsto_one_div_add_atTop_nhds_zero_nat
      have h3 : ‖(1 : ℚ_[p]) - χr‖ * ‖z‖ ≤ 0 :=
        le_of_tendsto_of_tendsto' h1 h2 hkill
      have h4 : ‖z‖ = 0 := by nlinarith [norm_nonneg z, hδpos, norm_nonneg ((1 : ℚ_[p]) - χr)]
      exact norm_eq_zero.mp h4
    -- the traces converge back within reach of the element
    have hymem' : y ∈ Mn := hymem
    have hRy : algebraMap ↥Mn (PadicAlgCl p) (R y) = y := by
      have h1 : y = algebraMap ↥Mn (PadicAlgCl p) ⟨y, hymem'⟩ := rfl
      rw [h1, Algebra.normalizedTrace_algebraMap_apply_eq_self]
    have hyz : ‖(y : ℂ_[p]) - z‖ ≤ C * ε := by
      have hev : ∀ᶠ j : ℕ in Filter.atTop, ‖(y : ℂ_[p]) - Y j‖ ≤ C * ε := by
        obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
        refine Filter.eventually_atTop.mpr ⟨N, fun j hj => ?_⟩
        have h1 : (y : ℂ_[p]) - Y j
            = ((algebraMap ↥Mn (PadicAlgCl p) (R (y - xx j)) : PadicAlgCl p) : ℂ_[p]) := by
          have e1 : R (y - xx j) = R y - R (xx j) := map_sub _ _ _
          rw [e1, map_sub]
          have e2 : ((algebraMap ↥Mn (PadicAlgCl p) (R y)
              - algebraMap ↥Mn (PadicAlgCl p) (R (xx j)) : PadicAlgCl p) : ℂ_[p])
              = ((algebraMap ↥Mn (PadicAlgCl p) (R y) : PadicAlgCl p) : ℂ_[p])
                - ((algebraMap ↥Mn (PadicAlgCl p) (R (xx j)) : PadicAlgCl p) : ℂ_[p]) :=
            map_sub (algebraMap (PadicAlgCl p) ℂ_[p]) _ _
          simp only [hY]
          rw [e2, hRy]
        rw [h1, PadicComplex.norm_extends]
        have hmemyj : y - xx j ∈ IntermediateField.fixedField (toGalSubgroup H
            ⊓ (IntermediateField.adjoin ℚ_[p] {ζ (mm j)}).fixingSubgroup) :=
          sub_mem (level_mono H ζ hζcoh (hmmn j) hymem') (hxxmem j)
        refine le_trans (hbound n (mm j) hn₀ (hmmn j) _ hmemyj) ?_
        refine mul_le_mul_of_nonneg_left ?_ hC.le
        -- the distance from `y` to the approximant is at most `ε`, ultrametrically
        have hcoe2 : ((y - xx j : PadicAlgCl p) : ℂ_[p]) = (y : ℂ_[p]) - (xx j : ℂ_[p]) :=
          map_sub (algebraMap (PadicAlgCl p) ℂ_[p]) y (xx j)
        rw [← PadicComplex.norm_extends, hcoe2]
        calc ‖((y : ℂ_[p])) - ((xx j : ℂ_[p]))‖
            = ‖((y : ℂ_[p]) - c) + (c - (xx j : ℂ_[p]))‖ := by congr 1; abel
          _ ≤ max ‖(y : ℂ_[p]) - c‖ ‖c - (xx j : ℂ_[p])‖ :=
              IsUltrametricDist.norm_add_le_max _ _
          _ ≤ ε := by
              refine max_le ?_ ?_
              · rw [norm_sub_rev]
                exact hydist
              · refine le_trans (hxxdist j) ?_
                rw [div_le_iff₀ (by positivity)]
                rw [div_lt_iff₀ hε] at hN
                nlinarith [hN, (by exact_mod_cast hj : (N : ℝ) ≤ (j : ℝ))]
      have h2 : Filter.Tendsto (fun j => ‖(y : ℂ_[p]) - Y j‖) Filter.atTop
          (nhds ‖(y : ℂ_[p]) - z‖) := (Filter.Tendsto.const_sub _ hz).norm
      exact le_of_tendsto h2 hev
    calc ‖c‖ = ‖c - z‖ := by rw [hz0, sub_zero]
      _ = ‖(c - (y : ℂ_[p])) + ((y : ℂ_[p]) - z)‖ := by congr 1; abel
      _ ≤ max ‖c - (y : ℂ_[p])‖ ‖(y : ℂ_[p]) - z‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ max 1 C * ε := by
          refine max_le ?_ ?_
          · calc ‖c - (y : ℂ_[p])‖ ≤ ε := hydist
              _ = 1 * ε := (one_mul ε).symm
              _ ≤ max 1 C * ε := by
                  refine mul_le_mul_of_nonneg_right (le_max_left 1 C) hε.le
          · refine le_trans hyz ?_
            exact mul_le_mul_of_nonneg_right (le_max_right 1 C) hε.le
  -- arbitrary precision forces vanishing
  by_contra hc0
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  have hmaxpos : 0 < max 1 C := lt_of_lt_of_le one_pos (le_max_left 1 C)
  have hhalf := hkey (‖c‖ / (2 * max 1 C)) (by positivity)
  have hsimp : max 1 C * (‖c‖ / (2 * max 1 C)) = ‖c‖ / 2 := by
    field_simp
  rw [hsimp] at hhalf
  linarith

/-- scaffolding: iterating the coherence of the root tower, a deep root powers down to the
root at any lower level. -/
theorem rootTower_pow (ζ : ℕ → PadicAlgCl p) (hζcoh : ∀ n, (ζ (n + 1)) ^ p = ζ n)
    {n m : ℕ} (hnm : n ≤ m) : ζ m ^ p ^ (m - n) = ζ n := by
  have key : ∀ k : ℕ, ζ (n + k) ^ p ^ k = ζ n := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        rw [pow_succ', pow_mul, show n + (j + 1) = (n + j) + 1 from rfl, hζcoh (n + j)]
        exact ih
  have h := key (m - n)
  rwa [Nat.add_sub_cancel' hnm] at h

/-- scaffolding: the cyclotomic levels are increasing—the lower root is a power of the deeper
one. -/
theorem adjoin_root_le (ζ : ℕ → PadicAlgCl p) (hζcoh : ∀ n, (ζ (n + 1)) ^ p = ζ n)
    {n m : ℕ} (hnm : n ≤ m) :
    IntermediateField.adjoin ℚ_[p] {ζ n} ≤ IntermediateField.adjoin ℚ_[p] {ζ m} := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy, ← rootTower_pow ζ hζcoh hnm]
  exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] (ζ m)) _

/-- scaffolding: a subfield of a finite intermediate field is finite. -/
theorem finiteDimensional_of_le {A B : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] ↥B] (h : A ≤ B) : FiniteDimensional ℚ_[p] ↥A :=
  FiniteDimensional.of_injective (IntermediateField.inclusion h).toLinearMap
    (IntermediateField.inclusion_injective h)

/-- scaffolding: degrees are monotone along inclusions of intermediate fields. -/
theorem finrank_le_of_le {A B : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] ↥B] (h : A ≤ B) :
    Module.finrank ℚ_[p] ↥A ≤ Module.finrank ℚ_[p] ↥B :=
  LinearMap.finrank_le_finrank_of_injective
    (f := (IntermediateField.inclusion h).toLinearMap)
    (IntermediateField.inclusion_injective h)

/-- scaffolding: an inclusion of intermediate fields with at least the degree of the larger
one is an equality. -/
theorem eq_of_le_of_finrank_le {A B : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] ↥B] (h : A ≤ B)
    (hr : Module.finrank ℚ_[p] ↥B ≤ Module.finrank ℚ_[p] ↥A) : A = B := by
  refine IntermediateField.toSubalgebra_injective ?_
  haveI : FiniteDimensional ℚ_[p] ↥B.toSubalgebra := ‹FiniteDimensional ℚ_[p] ↥B›
  exact Subalgebra.eq_of_le_of_finrank_le (fun x hx => h hx) hr

/-- scaffolding: multiplicativity of degrees through a relative intermediate field of the
closure—restricting its scalars leaves the underlying module unchanged. -/
theorem finrank_mul_finrank_eq (F : IntermediateField ℚ_[p] (PadicAlgCl p))
    (T : IntermediateField ↥F (PadicAlgCl p)) :
    Module.finrank ℚ_[p] ↥F * Module.finrank ↥F ↥T
      = Module.finrank ℚ_[p] ↥(T.restrictScalars ℚ_[p]) :=
  Module.finrank_mul_finrank ℚ_[p] ↥F ↥T

/-- scaffolding: the fixed field of an open subgroup is a finite extension—the Krull
correspondence turns openness into finiteness. -/
theorem finiteDimensional_fixedField (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p]))) :
    FiniteDimensional ℚ_[p] ↥(IntermediateField.fixedField (toGalSubgroup H)) := by
  refine (InfiniteGalois.isOpen_iff_finite _).mp ?_
  have hKrull : (IntermediateField.fixedField (toGalSubgroup H)).fixingSubgroup
      = toGalSubgroup H :=
    InfiniteGalois.fixingSubgroup_fixedField
      ⟨toGalSubgroup H, Subgroup.isClosed_of_isOpen _ hH⟩
  rw [hKrull]
  exact hH

/-- scaffolding: the fixed field of the intersection with a level's fixing subgroup is the
compositum of the fixed field with the level. -/
theorem fixedField_inf (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p])))
    (E : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] ↥E] :
    IntermediateField.fixedField (toGalSubgroup H ⊓ E.fixingSubgroup)
      = IntermediateField.fixedField (toGalSubgroup H) ⊔ E := by
  have hKrull : (IntermediateField.fixedField (toGalSubgroup H)).fixingSubgroup
      = toGalSubgroup H :=
    InfiniteGalois.fixingSubgroup_fixedField
      ⟨toGalSubgroup H, Subgroup.isClosed_of_isOpen _ hH⟩
  conv_lhs => rw [← hKrull, ← IntermediateField.fixingSubgroup_sup]
  exact InfiniteGalois.fixedField_fixingSubgroup _

/-- scaffolding: the intersections of the fixed field with the cyclotomic levels
stabilize—an increasing chain of subfields of a finite extension has eventually constant
degree. -/
theorem exists_stable (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p])))
    (ζ : ℕ → PadicAlgCl p) (hζcoh : ∀ n, (ζ (n + 1)) ^ p = ζ n) :
    ∃ n₀ : ℕ, n₀ ≠ 0 ∧ ∀ k : ℕ, n₀ ≤ k →
      IntermediateField.fixedField (toGalSubgroup H) ⊓ IntermediateField.adjoin ℚ_[p] {ζ k}
        = IntermediateField.fixedField (toGalSubgroup H)
            ⊓ IntermediateField.adjoin ℚ_[p] {ζ n₀} := by
  classical
  haveI := finiteDimensional_fixedField H hH
  set L := IntermediateField.fixedField (toGalSubgroup H) with hL
  haveI : ∀ k : ℕ, FiniteDimensional ℚ_[p]
      ↥(L ⊓ IntermediateField.adjoin ℚ_[p] {ζ k}) :=
    fun _ => finiteDimensional_of_le inf_le_left
  set f : ℕ → ℕ :=
    fun k => Module.finrank ℚ_[p] ↥(L ⊓ IntermediateField.adjoin ℚ_[p] {ζ k}) with hf
  have hmono : ∀ {a b : ℕ}, a ≤ b →
      L ⊓ IntermediateField.adjoin ℚ_[p] {ζ a}
        ≤ L ⊓ IntermediateField.adjoin ℚ_[p] {ζ b} :=
    fun hab => inf_le_inf_left L (adjoin_root_le ζ hζcoh hab)
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨Module.finrank ℚ_[p] ↥L, ?_⟩
    rintro - ⟨k, rfl⟩
    exact finrank_le_of_le inf_le_left
  have hne : (Set.range f).Nonempty := ⟨f 0, 0, rfl⟩
  obtain ⟨n₁, hn₁⟩ := Nat.sSup_mem hne hbdd
  have hmax : ∀ j : ℕ, f j ≤ f n₁ := fun j => (le_csSup hbdd ⟨j, rfl⟩).trans hn₁.ge
  have hstab : ∀ j : ℕ, n₁ ≤ j →
      L ⊓ IntermediateField.adjoin ℚ_[p] {ζ j}
        = L ⊓ IntermediateField.adjoin ℚ_[p] {ζ n₁} :=
    fun j hj => (eq_of_le_of_finrank_le (hmono hj) (hmax j)).symm
  refine ⟨n₁ + 1, Nat.succ_ne_zero n₁, fun k hk => ?_⟩
  rw [hstab k (by omega), hstab (n₁ + 1) (Nat.le_succ n₁)]

/-- scaffolding: a finite extension and a cyclotomic level multiply degrees over their
intersection—the cyclotomic side is Galois over the intersection, so the two sides are
linearly disjoint there ([Brinon–Conrad 2009, §14.1, p.237][BrinonConrad2009], where the
auxiliary extension is arranged linearly disjoint from the cyclotomic tower). -/
theorem finrank_sup_mul_finrank_inf {q : ℕ} (hq : q ≠ 0) {ξ : PadicAlgCl p}
    (hξ : IsPrimitiveRoot ξ q) (A : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] ↥A] :
    Module.finrank ℚ_[p] ↥(A ⊔ IntermediateField.adjoin ℚ_[p] {ξ})
        * Module.finrank ℚ_[p] ↥(A ⊓ IntermediateField.adjoin ℚ_[p] {ξ})
      = Module.finrank ℚ_[p] ↥A
        * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ξ}) := by
  classical
  haveI : NeZero q := ⟨hq⟩
  set B := IntermediateField.adjoin ℚ_[p] {ξ} with hB
  haveI : FiniteDimensional ℚ_[p] ↥B :=
    IntermediateField.adjoin.finiteDimensional
      ((PadicAlgCl.isAlgebraic p).isAlgebraic ξ).isIntegral
  set E := A ⊓ B with hE
  haveI : FiniteDimensional ℚ_[p] ↥E := finiteDimensional_of_le inf_le_left
  set A' := IntermediateField.extendScalars (inf_le_left : E ≤ A) with hA'
  set B' := IntermediateField.adjoin ↥E {ξ} with hB'
  have hBrs : B'.restrictScalars ℚ_[p] = B := by
    rw [hB', IntermediateField.restrictScalars_adjoin_eq_sup]
    exact sup_eq_right.mpr inf_le_right
  have hB'eq : B' = IntermediateField.extendScalars (inf_le_right : E ≤ B) := by
    refine IntermediateField.restrictScalars_injective ℚ_[p] ?_
    rw [hBrs, IntermediateField.extendScalars_restrictScalars]
  haveI : FiniteDimensional ↥E ↥B' :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ξ)
  haveI : FiniteDimensional ℚ_[p] ↥A' := ‹FiniteDimensional ℚ_[p] ↥A›
  haveI : FiniteDimensional ↥E ↥A' := FiniteDimensional.right ℚ_[p] ↥E ↥A'
  haveI : IsCyclotomicExtension {q} ↥E ↥B' := by
    have h2 : (IntermediateField.adjoin ↥E {ξ}).toSubalgebra = Algebra.adjoin ↥E {ξ} :=
      IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsIntegral.isIntegral ξ).isAlgebraic
    exact IsCyclotomicExtension.equiv {q} ↥E ↥(Algebra.adjoin ↥E {ξ})
      (h := hξ.adjoin_isCyclotomicExtension ↥E) (Subalgebra.equivOfEq _ _ h2.symm)
  haveI : IsGalois ↥E ↥B' := IsCyclotomicExtension.isGalois {q} ↥E ↥B'
  have hbot : B' ⊓ A' = ⊥ := by
    refine le_antisymm ?_ bot_le
    intro x hx
    have hx' := IntermediateField.mem_inf.mp hx
    have hxB : x ∈ B := by rw [← hBrs]; exact hx'.1
    have hxA : x ∈ A := hx'.2
    rw [IntermediateField.mem_bot]
    exact ⟨⟨x, IntermediateField.mem_inf.mpr ⟨hxA, hxB⟩⟩, rfl⟩
  have hdisj : B'.LinearDisjoint A' := IntermediateField.LinearDisjoint.of_inf_eq_bot hbot
  have hfr : Module.finrank ↥E ↥(B' ⊔ A')
      = Module.finrank ↥E ↥B' * Module.finrank ↥E ↥A' := hdisj.finrank_sup
  have hrs : (B' ⊔ A').restrictScalars ℚ_[p] = A ⊔ B := by
    rw [hB'eq, hA', IntermediateField.extendScalars_sup,
      IntermediateField.extendScalars_restrictScalars, sup_comm]
  have h1 : Module.finrank ℚ_[p] ↥E * Module.finrank ↥E ↥(B' ⊔ A')
      = Module.finrank ℚ_[p] ↥(A ⊔ B) := by
    rw [finrank_mul_finrank_eq E (B' ⊔ A'), hrs]
  have h2 : Module.finrank ℚ_[p] ↥E * Module.finrank ↥E ↥B'
      = Module.finrank ℚ_[p] ↥B := by
    rw [finrank_mul_finrank_eq E B', hBrs]
  have h3 : Module.finrank ℚ_[p] ↥E * Module.finrank ↥E ↥A'
      = Module.finrank ℚ_[p] ↥A := by
    rw [finrank_mul_finrank_eq E A', hA', IntermediateField.extendScalars_restrictScalars]
  rw [← h1, ← h2, ← h3, hfr]
  ring

/-- scaffolding: a finite intermediate field of the closure is generated by one element—the
primitive element theorem, transported along the inclusion. -/
theorem exists_adjoin_simple_eq (A : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] ↥A] :
    ∃ α : PadicAlgCl p, IntermediateField.adjoin ℚ_[p] {α} = A := by
  obtain ⟨α₀, hα₀⟩ := Field.exists_primitive_element ℚ_[p] ↥A
  refine ⟨(α₀ : PadicAlgCl p), ?_⟩
  have h1 : IntermediateField.map A.val (IntermediateField.adjoin ℚ_[p] {α₀})
      = IntermediateField.adjoin ℚ_[p] {(α₀ : PadicAlgCl p)} := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  rw [← h1, hα₀]
  calc IntermediateField.map A.val ⊤
      = A.val.fieldRange := (AlgHom.fieldRange_eq_map A.val).symm
    _ = A := A.fieldRange_val

/-- scaffolding: the normalized traces from the two levels of a compositum tower agree on the
adjoined side—restriction is a bijection between the embedding sets, injective because the
big field is the compositum and surjective by the equality of the counts. -/
theorem normalizedTrace_eq_of_finrank_mul {F₁ F₂ : IntermediateField ℚ_[p] (PadicAlgCl p)}
    [FiniteDimensional ℚ_[p] ↥F₁] [FiniteDimensional ℚ_[p] ↥F₂] (hF : F₁ ≤ F₂)
    (a : PadicAlgCl p)
    (hrank : Module.finrank ℚ_[p] ↥(F₂ ⊔ IntermediateField.adjoin ℚ_[p] {a})
          * Module.finrank ℚ_[p] ↥F₁
        = Module.finrank ℚ_[p] ↥F₂
          * Module.finrank ℚ_[p] ↥(F₁ ⊔ IntermediateField.adjoin ℚ_[p] {a}))
    {c : PadicAlgCl p} (hc : c ∈ IntermediateField.adjoin ℚ_[p] {a}) :
    algebraMap ↥F₂ (PadicAlgCl p) (Algebra.normalizedTrace ↥F₂ (PadicAlgCl p) c)
      = algebraMap ↥F₁ (PadicAlgCl p) (Algebra.normalizedTrace ↥F₁ (PadicAlgCl p) c) := by
  classical
  haveI : CharZero ↥F₁ := charZero_of_injective_algebraMap (algebraMap ℚ_[p] ↥F₁).injective
  haveI : CharZero ↥F₂ := charZero_of_injective_algebraMap (algebraMap ℚ_[p] ↥F₂).injective
  set T₁ := IntermediateField.adjoin ↥F₁ {a} with hT₁
  set T₂ := IntermediateField.adjoin ↥F₂ {a} with hT₂
  haveI : FiniteDimensional ↥F₁ ↥T₁ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  haveI : FiniteDimensional ↥F₂ ↥T₂ :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  have hrs₁ : T₁.restrictScalars ℚ_[p] = F₁ ⊔ IntermediateField.adjoin ℚ_[p] {a} :=
    IntermediateField.restrictScalars_adjoin_eq_sup (K := F₁) (S := {a})
  have hrs₂ : T₂.restrictScalars ℚ_[p] = F₂ ⊔ IntermediateField.adjoin ℚ_[p] {a} :=
    IntermediateField.restrictScalars_adjoin_eq_sup (K := F₂) (S := {a})
  have hc₁ : c ∈ T₁ := by
    have h1 : c ∈ T₁.restrictScalars ℚ_[p] := by
      rw [hrs₁]
      exact (le_sup_right : IntermediateField.adjoin ℚ_[p] {a} ≤ _) hc
    exact h1
  have hc₂ : c ∈ T₂ := by
    have h1 : c ∈ T₂.restrictScalars ℚ_[p] := by
      rw [hrs₂]
      exact (le_sup_right : IntermediateField.adjoin ℚ_[p] {a} ≤ _) hc
    exact h1
  -- the relative degrees agree
  have hd₁ : Module.finrank ℚ_[p] ↥F₁ * Module.finrank ↥F₁ ↥T₁
      = Module.finrank ℚ_[p] ↥(F₁ ⊔ IntermediateField.adjoin ℚ_[p] {a}) := by
    rw [finrank_mul_finrank_eq F₁ T₁, hrs₁]
  have hd₂ : Module.finrank ℚ_[p] ↥F₂ * Module.finrank ↥F₂ ↥T₂
      = Module.finrank ℚ_[p] ↥(F₂ ⊔ IntermediateField.adjoin ℚ_[p] {a}) := by
    rw [finrank_mul_finrank_eq F₂ T₂, hrs₂]
  have hr : Module.finrank ↥F₂ ↥T₂ = Module.finrank ↥F₁ ↥T₁ := by
    have key : Module.finrank ℚ_[p] ↥F₂ * Module.finrank ℚ_[p] ↥F₁
          * Module.finrank ↥F₂ ↥T₂
        = Module.finrank ℚ_[p] ↥F₂ * Module.finrank ℚ_[p] ↥F₁
          * Module.finrank ↥F₁ ↥T₁ := by
      calc Module.finrank ℚ_[p] ↥F₂ * Module.finrank ℚ_[p] ↥F₁ * Module.finrank ↥F₂ ↥T₂
          = Module.finrank ℚ_[p] ↥F₂ * Module.finrank ↥F₂ ↥T₂
              * Module.finrank ℚ_[p] ↥F₁ := by ring
        _ = Module.finrank ℚ_[p] ↥(F₂ ⊔ IntermediateField.adjoin ℚ_[p] {a})
              * Module.finrank ℚ_[p] ↥F₁ := by rw [hd₂]
        _ = Module.finrank ℚ_[p] ↥F₂
              * Module.finrank ℚ_[p] ↥(F₁ ⊔ IntermediateField.adjoin ℚ_[p] {a}) := hrank
        _ = Module.finrank ℚ_[p] ↥F₂
              * (Module.finrank ℚ_[p] ↥F₁ * Module.finrank ↥F₁ ↥T₁) := by rw [hd₁]
        _ = Module.finrank ℚ_[p] ↥F₂ * Module.finrank ℚ_[p] ↥F₁
              * Module.finrank ↥F₁ ↥T₁ := by ring
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.mul_pos Module.finrank_pos Module.finrank_pos) key
  -- the restriction between the embedding sets
  have hsub : ∀ x : PadicAlgCl p, x ∈ T₁ → x ∈ T₂ := by
    intro x hx
    have h1 : x ∈ T₁.restrictScalars ℚ_[p] := hx
    rw [hrs₁] at h1
    have h3 : x ∈ T₂.restrictScalars ℚ_[p] := by
      rw [hrs₂]
      exact sup_le_sup_right hF _ h1
    exact h3
  have hRcomm : ∀ (σ : ↥T₂ →ₐ[↥F₂] PadicAlgCl p) (u : ↥F₁),
      σ ⟨((algebraMap ↥F₁ ↥T₁ u : ↥T₁) : PadicAlgCl p),
          hsub _ (algebraMap ↥F₁ ↥T₁ u).2⟩
        = algebraMap ↥F₁ (PadicAlgCl p) u := by
    intro σ u
    have h1 : (⟨((algebraMap ↥F₁ ↥T₁ u : ↥T₁) : PadicAlgCl p),
        hsub _ (algebraMap ↥F₁ ↥T₁ u).2⟩ : ↥T₂)
        = algebraMap ↥F₂ ↥T₂ ⟨(u : PadicAlgCl p), hF u.2⟩ := Subtype.ext rfl
    rw [h1, σ.commutes]
    rfl
  let R : (↥T₂ →ₐ[↥F₂] PadicAlgCl p) → (↥T₁ →ₐ[↥F₁] PadicAlgCl p) := fun σ =>
    { toFun := fun x => σ ⟨x.1, hsub x.1 x.2⟩
      map_one' := map_one σ
      map_mul' := fun x y => map_mul σ ⟨x.1, hsub x.1 x.2⟩ ⟨y.1, hsub y.1 y.2⟩
      map_zero' := map_zero σ
      map_add' := fun x y => map_add σ ⟨x.1, hsub x.1 x.2⟩ ⟨y.1, hsub y.1 y.2⟩
      commutes' := hRcomm σ }
  have hRinj : Function.Injective R := by
    intro σ σ' h
    refine (IntermediateField.adjoin.powerBasis
      (Algebra.IsIntegral.isIntegral (R := ↥F₂) a)).algHom_ext ?_
    exact DFunLike.congr_fun h (⟨a, IntermediateField.mem_adjoin_simple_self ↥F₁ a⟩ : ↥T₁)
  have hcard : Nat.card (↥T₂ →ₐ[↥F₂] PadicAlgCl p)
      = Nat.card (↥T₁ →ₐ[↥F₁] PadicAlgCl p) := by
    rw [AlgHom.natCard_of_splits _ _ _ fun _ => IsAlgClosed.splits _,
      AlgHom.natCard_of_splits _ _ _ fun _ => IsAlgClosed.splits _, hr]
  have hRbij : Function.Bijective R :=
    (Nat.bijective_iff_injective_and_card R).mpr ⟨hRinj, hcard⟩
  have hsum : (∑ σ : ↥T₂ →ₐ[↥F₂] PadicAlgCl p, σ ⟨c, hc₂⟩)
      = ∑ τ : ↥T₁ →ₐ[↥F₁] PadicAlgCl p, τ ⟨c, hc₁⟩ :=
    Fintype.sum_bijective R hRbij _ _ fun σ => rfl
  -- reduce both normalized traces to the embedding sums
  have htr₂ : algebraMap ↥F₂ (PadicAlgCl p) (Algebra.trace ↥F₂ ↥T₂ ⟨c, hc₂⟩)
      = ∑ σ : ↥T₂ →ₐ[↥F₂] PadicAlgCl p, σ ⟨c, hc₂⟩ :=
    trace_eq_sum_embeddings (E := PadicAlgCl p)
  have htr₁ : algebraMap ↥F₁ (PadicAlgCl p) (Algebra.trace ↥F₁ ↥T₁ ⟨c, hc₁⟩)
      = ∑ τ : ↥T₁ →ₐ[↥F₁] PadicAlgCl p, τ ⟨c, hc₁⟩ :=
    trace_eq_sum_embeddings (E := PadicAlgCl p)
  have hnt₂ : Algebra.normalizedTrace ↥F₂ (PadicAlgCl p) c
      = (Module.finrank ↥F₂ ↥T₂ : ↥F₂)⁻¹ • Algebra.trace ↥F₂ ↥T₂ ⟨c, hc₂⟩ := by
    have h1 : Algebra.normalizedTrace ↥F₂ (PadicAlgCl p) c
        = Algebra.normalizedTrace ↥F₂ ↥T₂ ⟨c, hc₂⟩ :=
      Algebra.normalizedTrace_intermediateField ↥F₂ (PadicAlgCl p) ⟨c, hc₂⟩
    rw [h1, Algebra.normalizedTrace_eq_of_finiteDimensional_apply]
  have hnt₁ : Algebra.normalizedTrace ↥F₁ (PadicAlgCl p) c
      = (Module.finrank ↥F₁ ↥T₁ : ↥F₁)⁻¹ • Algebra.trace ↥F₁ ↥T₁ ⟨c, hc₁⟩ := by
    have h1 : Algebra.normalizedTrace ↥F₁ (PadicAlgCl p) c
        = Algebra.normalizedTrace ↥F₁ ↥T₁ ⟨c, hc₁⟩ :=
      Algebra.normalizedTrace_intermediateField ↥F₁ (PadicAlgCl p) ⟨c, hc₁⟩
    rw [h1, Algebra.normalizedTrace_eq_of_finiteDimensional_apply]
  rw [hnt₂, hnt₁, hr, smul_eq_mul, smul_eq_mul, map_mul, map_mul, map_inv₀, map_inv₀,
    map_natCast, map_natCast, htr₂, htr₁, hsum]

/-- scaffolding: the trace of a relative finite extension inside the algebraic closure is
ultrametrically bounded by the element—the trace is a sum of conjugates, and conjugation
preserves the spectral norm. -/
theorem norm_trace_le (F : IntermediateField ℚ_[p] (PadicAlgCl p))
    (T : IntermediateField ↥F (PadicAlgCl p)) [FiniteDimensional ↥F ↥T] (v : ↥T) :
    ‖algebraMap ↥F (PadicAlgCl p) (Algebra.trace ↥F ↥T v)‖ ≤ ‖(v : PadicAlgCl p)‖ := by
  haveI : CharZero ↥F := charZero_of_injective_algebraMap (algebraMap ℚ_[p] ↥F).injective
  have htr : algebraMap ↥F (PadicAlgCl p) (Algebra.trace ↥F ↥T v)
      = ∑ σ : ↥T →ₐ[↥F] PadicAlgCl p, σ v :=
    trace_eq_sum_embeddings (E := PadicAlgCl p)
  rw [htr]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun σ _ => ?_
  have hvroot : (Polynomial.aeval (σ v)) (minpoly ℚ_[p] ((v : ↥T) : PadicAlgCl p)) = 0 := by
    have h1 : (T.val.restrictScalars ℚ_[p])
        ((Polynomial.aeval v) (minpoly ℚ_[p] ((v : ↥T) : PadicAlgCl p))) = 0 := by
      rw [← Polynomial.aeval_algHom_apply]
      exact minpoly.aeval ℚ_[p] _
    have h2 : (Polynomial.aeval v) (minpoly ℚ_[p] ((v : ↥T) : PadicAlgCl p)) = 0 :=
      Subtype.ext h1
    have h3 : σ v = (σ.restrictScalars ℚ_[p]) v := rfl
    rw [h3, Polynomial.aeval_algHom_apply, h2, map_zero]
  obtain ⟨τ, hτ⟩ := minpoly.exists_algEquiv_of_root'
    ((PadicAlgCl.isAlgebraic p).isAlgebraic ((v : ↥T) : PadicAlgCl p)) hvroot
  rw [← hτ]
  exact le_of_eq (ConjugateDiameterBound.norm_algEquiv τ _)

set_option maxHeartbeats 800000 in
-- The basis expansion over the compositum drives the elaborator through the scalar-tower
-- instances at every coordinate; the work does not fit the default budget.
/-- scaffolding: dual-basis coordinate extraction. A basis of the finite side over the stable
intersection stays a basis of every compositum with a level, and the coordinates of an
element are traces against the dual basis, ultrametrically bounded uniformly in the level
([Brinon–Conrad 2009, §14.1, p.237][BrinonConrad2009], the linear disjointness arranged there;
the bound is the content of [Brinon–Conrad 2009, §14.1, Lem. 14.1.4, p.238][BrinonConrad2009]). -/
theorem exists_coordinates (E A : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] ↥E] [FiniteDimensional ℚ_[p] ↥A] (hEA : E ≤ A)
    {α : PadicAlgCl p} (hα : IntermediateField.adjoin ℚ_[p] {α} = A) :
    ∃ (s : ℕ) (w : Fin s → PadicAlgCl p) (D : ℝ), (∀ i, w i ∈ A) ∧ 0 < D ∧
      ∀ B : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] ↥B → E ≤ B →
        Module.finrank ℚ_[p] ↥(A ⊔ B) * Module.finrank ℚ_[p] ↥E
          = Module.finrank ℚ_[p] ↥A * Module.finrank ℚ_[p] ↥B →
        ∀ x ∈ A ⊔ B, ∃ c : Fin s → PadicAlgCl p, (∀ i, c i ∈ B)
          ∧ x = ∑ i, c i * w i ∧ ∀ i, ‖c i‖ ≤ D * ‖x‖ := by
  classical
  haveI : CharZero ↥E := charZero_of_injective_algebraMap (algebraMap ℚ_[p] ↥E).injective
  set VA := IntermediateField.extendScalars hEA with hVA
  haveI hVAfd : FiniteDimensional ℚ_[p] ↥VA := ‹FiniteDimensional ℚ_[p] ↥A›
  haveI : FiniteDimensional ↥E ↥VA := FiniteDimensional.right ℚ_[p] ↥E ↥VA
  set s := Module.finrank ↥E ↥VA with hs
  set w0 : Module.Basis (Fin s) ↥E ↥VA := Module.finBasis ↥E ↥VA with hw0
  set w1 : Module.Basis (Fin s) ↥E ↥VA := w0.traceDual with hw1
  refine ⟨s, fun i => ((w0 i : ↥VA) : PadicAlgCl p),
    1 + ∑ j, ‖((w1 j : ↥VA) : PadicAlgCl p)‖, fun i => (w0 i).2,
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun j _ => norm_nonneg _), ?_⟩
  intro B hBfd hEB hrank x hx
  haveI := hBfd
  have hBAB : B ≤ A ⊔ B := le_sup_right
  set VM := IntermediateField.extendScalars hBAB with hVM
  haveI hVMfd : FiniteDimensional ℚ_[p] ↥VM :=
    (inferInstance : FiniteDimensional ℚ_[p] ↥(A ⊔ B))
  haveI : FiniteDimensional ↥B ↥VM := FiniteDimensional.right ℚ_[p] ↥B ↥VM
  haveI : CharZero ↥B := charZero_of_injective_algebraMap (algebraMap ℚ_[p] ↥B).injective
  -- the compositum has relative dimension `s` over the level
  have hfrVM : Module.finrank ↥B ↥VM = s := by
    have h1 := finrank_mul_finrank_eq B VM
    have h2 := finrank_mul_finrank_eq E VA
    rw [IntermediateField.extendScalars_restrictScalars] at h1
    rw [IntermediateField.extendScalars_restrictScalars] at h2
    have h3 : Module.finrank ℚ_[p] ↥B * Module.finrank ℚ_[p] ↥E * Module.finrank ↥B ↥VM
        = Module.finrank ℚ_[p] ↥B * Module.finrank ℚ_[p] ↥E * s := by
      calc Module.finrank ℚ_[p] ↥B * Module.finrank ℚ_[p] ↥E * Module.finrank ↥B ↥VM
          = Module.finrank ℚ_[p] ↥(A ⊔ B) * Module.finrank ℚ_[p] ↥E := by rw [← h1]; ring
        _ = Module.finrank ℚ_[p] ↥A * Module.finrank ℚ_[p] ↥B := hrank
        _ = Module.finrank ℚ_[p] ↥B * Module.finrank ℚ_[p] ↥E * s := by rw [← h2]; ring
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.mul_pos Module.finrank_pos Module.finrank_pos) h3
  -- the basis and its trace dual, pushed into the compositum
  have hle : ∀ i : Fin s, ((w0 i : ↥VA) : PadicAlgCl p) ∈ VM := fun i =>
    (le_sup_left : A ≤ A ⊔ B) (w0 i).2
  have hle1 : ∀ j : Fin s, ((w1 j : ↥VA) : PadicAlgCl p) ∈ VM := fun j =>
    (le_sup_left : A ≤ A ⊔ B) (w1 j).2
  set wV : Fin s → ↥VM := fun i => ⟨((w0 i : ↥VA) : PadicAlgCl p), hle i⟩ with hwV
  set w1V : Fin s → ↥VM := fun j => ⟨((w1 j : ↥VA) : PadicAlgCl p), hle1 j⟩ with hw1V
  have hs0 : s ≠ 0 := hs ▸ Module.finrank_pos.ne'
  -- a compositum trace of an element of the finite side descends to the intersection
  have htr : ∀ u : ↥VM, ((u : ↥VM) : PadicAlgCl p) ∈ A →
      algebraMap ↥B (PadicAlgCl p) (Algebra.trace ↥B ↥VM u)
        = (s : PadicAlgCl p) * algebraMap ↥E (PadicAlgCl p)
            (Algebra.normalizedTrace ↥E (PadicAlgCl p) ((u : ↥VM) : PadicAlgCl p)) := by
    intro u hu
    have h1 : Algebra.normalizedTrace ↥B (PadicAlgCl p) ((u : ↥VM) : PadicAlgCl p)
        = Algebra.normalizedTrace ↥B ↥VM u :=
      Algebra.normalizedTrace_intermediateField ↥B (PadicAlgCl p) u
    have h2 : Algebra.normalizedTrace ↥B ↥VM u
        = (Module.finrank ↥B ↥VM : ↥B)⁻¹ • Algebra.trace ↥B ↥VM u :=
      Algebra.normalizedTrace_eq_of_finiteDimensional_apply ↥B u
    have h3 : Algebra.trace ↥B ↥VM u
        = (s : ↥B) • Algebra.normalizedTrace ↥B (PadicAlgCl p) ((u : ↥VM) : PadicAlgCl p) := by
      rw [h1, h2, hfrVM, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hs0), one_smul]
    have h4 : algebraMap ↥B (PadicAlgCl p) (Algebra.trace ↥B ↥VM u)
        = (s : PadicAlgCl p) * algebraMap ↥B (PadicAlgCl p)
            (Algebra.normalizedTrace ↥B (PadicAlgCl p) ((u : ↥VM) : PadicAlgCl p)) := by
      rw [h3, smul_eq_mul, map_mul, map_natCast]
    rw [h4]
    congr 1
    refine normalizedTrace_eq_of_finrank_mul hEB α ?_ ?_
    · rw [hα, sup_comm B A, sup_eq_right.mpr hEA]
      exact hrank.trans (Nat.mul_comm _ _)
    · rw [hα]
      exact hu
  -- the diagonal: the compositum trace of basis against trace dual
  have hdiag : ∀ i j : Fin s,
      algebraMap ↥B (PadicAlgCl p) (Algebra.trace ↥B ↥VM (wV i * w1V j))
        = if i = j then 1 else 0 := by
    intro i j
    have hmem : ((wV i * w1V j : ↥VM) : PadicAlgCl p) ∈ A := by
      have h0 : ((wV i * w1V j : ↥VM) : PadicAlgCl p)
          = ((w0 i : ↥VA) : PadicAlgCl p) * ((w1 j : ↥VA) : PadicAlgCl p) := rfl
      rw [h0]
      exact mul_mem (w0 i).2 (w1 j).2
    rw [htr _ hmem]
    have h5 : ((wV i * w1V j : ↥VM) : PadicAlgCl p)
        = ((w0 i * w1 j : ↥VA) : PadicAlgCl p) := rfl
    have h6 : Algebra.normalizedTrace ↥E (PadicAlgCl p) ((w0 i * w1 j : ↥VA) : PadicAlgCl p)
        = Algebra.normalizedTrace ↥E ↥VA (w0 i * w1 j) :=
      Algebra.normalizedTrace_intermediateField ↥E (PadicAlgCl p) (w0 i * w1 j)
    have h7 : Algebra.normalizedTrace ↥E ↥VA (w0 i * w1 j)
        = (s : ↥E)⁻¹ • Algebra.trace ↥E ↥VA (w0 i * w1 j) :=
      Algebra.normalizedTrace_eq_of_finiteDimensional_apply ↥E (w0 i * w1 j)
    have h8 : Algebra.trace ↥E ↥VA (w0 i * w1 j) = if i = j then 1 else 0 :=
      Module.Basis.trace_mul_traceDual w0 i j
    rw [h5, h6, h7, h8, smul_eq_mul, map_mul, map_inv₀, map_natCast,
      apply_ite (algebraMap ↥E (PadicAlgCl p)), map_one, map_zero]
    by_cases hij : i = j
    · rw [if_pos hij, mul_one, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hs0)]
    · rw [if_neg hij, mul_zero, mul_zero]
  have hinj : Function.Injective (algebraMap ↥B (PadicAlgCl p)) :=
    (algebraMap ↥B (PadicAlgCl p)).injective
  -- the pushed basis is independent, hence a basis by the dimension count
  have hli : LinearIndependent ↥B wV := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have h1 : Algebra.trace ↥B ↥VM ((∑ i, g i • wV i) * w1V j) = 0 := by
      rw [hg, zero_mul, map_zero]
    have h2 : Algebra.trace ↥B ↥VM ((∑ i, g i • wV i) * w1V j)
        = ∑ i, g i * Algebra.trace ↥B ↥VM (wV i * w1V j) := by
      rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, map_smul, smul_eq_mul]
    have h6 : (∑ i, g i * Algebra.trace ↥B ↥VM (wV i * w1V j)) = 0 := h2.symm.trans h1
    have h3 : algebraMap ↥B (PadicAlgCl p) (∑ i, g i * Algebra.trace ↥B ↥VM (wV i * w1V j))
        = algebraMap ↥B (PadicAlgCl p) (g j) := by
      rw [map_sum]
      have h4 : ∀ i : Fin s,
          algebraMap ↥B (PadicAlgCl p) (g i * Algebra.trace ↥B ↥VM (wV i * w1V j))
            = if i = j then algebraMap ↥B (PadicAlgCl p) (g i) else 0 := by
        intro i
        rw [map_mul, hdiag i j]
        by_cases hij : i = j
        · rw [if_pos hij, if_pos hij, mul_one]
        · rw [if_neg hij, if_neg hij, mul_zero]
      rw [Finset.sum_congr rfl fun i _ => h4 i,
        Finset.sum_ite_eq' Finset.univ j (fun i => algebraMap ↥B (PadicAlgCl p) (g i)),
        if_pos (Finset.mem_univ j)]
    have h7 : algebraMap ↥B (PadicAlgCl p) (g j) = algebraMap ↥B (PadicAlgCl p) 0 := by
      rw [← h3, h6]
    exact hinj h7
  have hcard : Fintype.card (Fin s) = Module.finrank ↥B ↥VM := by
    rw [Fintype.card_fin, hfrVM]
  set bV : Module.Basis (Fin s) ↥B ↥VM := basisOfLinearIndependentOfCardEqFinrank' wV hli hcard
    with hbV
  have hbVcoe : ∀ i, bV i = wV i := fun i =>
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' wV hli hcard) i
  -- the element, its coordinates, and the coordinate formula
  have hxVM : x ∈ VM := hx
  set xV : ↥VM := ⟨x, hxVM⟩ with hxV
  refine ⟨fun i => ((bV.repr xV i : ↥B) : PadicAlgCl p), fun i => (bV.repr xV i).2, ?_, ?_⟩
  · -- the expansion
    have h1 : (∑ i, bV.repr xV i • bV i) = xV := bV.sum_repr xV
    have h2 : x = algebraMap ↥VM (PadicAlgCl p) xV := rfl
    rw [h2]
    conv_lhs => rw [← h1]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbVcoe i, Algebra.smul_def, map_mul]
    rfl
  · -- the coordinate bound
    intro i
    have h1 : Algebra.trace ↥B ↥VM (xV * w1V i)
        = ∑ j, bV.repr xV j * Algebra.trace ↥B ↥VM (wV j * w1V i) := by
      conv_lhs => rw [← bV.sum_repr xV]
      rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hbVcoe j, smul_mul_assoc, map_smul, smul_eq_mul]
    have h2 : algebraMap ↥B (PadicAlgCl p) (Algebra.trace ↥B ↥VM (xV * w1V i))
        = ((bV.repr xV i : ↥B) : PadicAlgCl p) := by
      rw [h1, map_sum]
      have h3 : ∀ j : Fin s,
          algebraMap ↥B (PadicAlgCl p) (bV.repr xV j * Algebra.trace ↥B ↥VM (wV j * w1V i))
            = if j = i then ((bV.repr xV j : ↥B) : PadicAlgCl p) else 0 := by
        intro j
        rw [map_mul, hdiag j i]
        by_cases hji : j = i
        · rw [if_pos hji, if_pos hji, mul_one]
          rfl
        · rw [if_neg hji, if_neg hji, mul_zero]
      rw [Finset.sum_congr rfl fun j _ => h3 j,
        Finset.sum_ite_eq' Finset.univ i (fun j => ((bV.repr xV j : ↥B) : PadicAlgCl p)),
        if_pos (Finset.mem_univ i)]
    change ‖((bV.repr xV i : ↥B) : PadicAlgCl p)‖
      ≤ (1 + ∑ j, ‖((w1 j : ↥VA) : PadicAlgCl p)‖) * ‖x‖
    rw [← h2]
    refine le_trans (norm_trace_le B VM (xV * w1V i)) ?_
    have h4 : ((xV * w1V i : ↥VM) : PadicAlgCl p) = x * ((w1 i : ↥VA) : PadicAlgCl p) := rfl
    rw [h4, norm_mul]
    have h5 : ‖((w1 i : ↥VA) : PadicAlgCl p)‖
        ≤ 1 + ∑ j, ‖((w1 j : ↥VA) : PadicAlgCl p)‖ :=
      le_trans (Finset.single_le_sum (fun j _ => norm_nonneg
        ((w1 j : ↥VA) : PadicAlgCl p)) (Finset.mem_univ i)) (le_add_of_nonneg_left zero_le_one)
    calc ‖x‖ * ‖((w1 i : ↥VA) : PadicAlgCl p)‖
        ≤ ‖x‖ * (1 + ∑ j, ‖((w1 j : ↥VA) : PadicAlgCl p)‖) :=
          mul_le_mul_of_nonneg_left h5 (norm_nonneg x)
      _ = (1 + ∑ j, ‖((w1 j : ↥VA) : PadicAlgCl p)‖) * ‖x‖ := mul_comm _ _

/-- scaffolding, the analytic input: the normalized traces of the level tower are uniformly
bounded. From the stabilization level on, an element fixed at a deep level has coordinates
over the fixed side controlled by the dual basis, and each coordinate's cyclotomic normalized
trace loses at most a factor `p` ([Brinon–Conrad 2009, §14.1, Lem. 14.1.4, p.238][BrinonConrad2009];
the reduction to the cyclotomic tower through linear disjointness is
[Brinon–Conrad 2009, §14.1, p.237][BrinonConrad2009]). -/
theorem levelTraceBound (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p])))
    (ζ : ℕ → PadicAlgCl p) (hζprim : ∀ n, IsPrimitiveRoot (ζ n) (p ^ n))
    (hζcoh : ∀ n, (ζ (n + 1)) ^ p = ζ n) :
    ∃ (n₀ : ℕ) (C : ℝ), 0 < C ∧ ∀ n m : ℕ, n₀ ≤ n → n ≤ m → ∀ x : PadicAlgCl p,
      x ∈ IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ m}).fixingSubgroup) →
      ‖(algebraMap ↥(IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) (PadicAlgCl p)
        (Algebra.normalizedTrace ↥(IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) (PadicAlgCl p) x))‖
        ≤ C * ‖x‖ := by
  classical
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  haveI hLfd := finiteDimensional_fixedField H hH
  obtain ⟨n₀, hn₀0, hstab⟩ := exists_stable H hH ζ hζcoh
  set L := IntermediateField.fixedField (toGalSubgroup H) with hLdef
  set E₀ := L ⊓ IntermediateField.adjoin ℚ_[p] {ζ n₀} with hE₀
  haveI : FiniteDimensional ℚ_[p] ↥E₀ := finiteDimensional_of_le inf_le_left
  obtain ⟨α, hα⟩ := exists_adjoin_simple_eq L
  obtain ⟨s, w, D, hwL, hD, hcoord⟩ := exists_coordinates E₀ L inf_le_left hα
  have hsum : (0 : ℝ) < 1 + ∑ i, ‖w i‖ :=
    add_pos_of_pos_of_nonneg one_pos (Finset.sum_nonneg fun i _ => norm_nonneg _)
  refine ⟨n₀, (p : ℝ) * D * (1 + ∑ i, ‖w i‖), mul_pos (mul_pos hp0 hD) hsum, ?_⟩
  intro n m hn₀n hnm x hx
  have hn0 : n ≠ 0 := by omega
  have hn₀m : n₀ ≤ m := le_trans hn₀n hnm
  haveI : FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ n}) :=
    IntermediateField.adjoin.finiteDimensional
      ((PadicAlgCl.isAlgebraic p).isAlgebraic (ζ n)).isIntegral
  haveI : FiniteDimensional ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ m}) :=
    IntermediateField.adjoin.finiteDimensional
      ((PadicAlgCl.isAlgebraic p).isAlgebraic (ζ m)).isIntegral
  -- the level fixed fields are composita
  have hMn : IntermediateField.fixedField (toGalSubgroup H
      ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)
      = L ⊔ IntermediateField.adjoin ℚ_[p] {ζ n} := fixedField_inf H hH _
  have hMm : IntermediateField.fixedField (toGalSubgroup H
      ⊓ (IntermediateField.adjoin ℚ_[p] {ζ m}).fixingSubgroup)
      = L ⊔ IntermediateField.adjoin ℚ_[p] {ζ m} := fixedField_inf H hH _
  -- the stabilized degree identity at every deep level
  have hstar : ∀ k : ℕ, n₀ ≤ k →
      Module.finrank ℚ_[p] ↥(L ⊔ IntermediateField.adjoin ℚ_[p] {ζ k})
          * Module.finrank ℚ_[p] ↥E₀
        = Module.finrank ℚ_[p] ↥L
          * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ k}) := by
    intro k hk
    have h1 := finrank_sup_mul_finrank_inf
      (Nat.pow_pos (Fact.out : p.Prime).pos).ne' (hζprim k) L
    rw [hstab k hk] at h1
    exact h1
  -- the coordinates of the element over the deep level
  have hxm : x ∈ L ⊔ IntermediateField.adjoin ℚ_[p] {ζ m} := hMm ▸ hx
  have hEK : E₀ ≤ IntermediateField.adjoin ℚ_[p] {ζ m} :=
    le_trans inf_le_right (adjoin_root_le ζ hζcoh hn₀m)
  obtain ⟨c, hcK, hcx, hcnorm⟩ := hcoord (IntermediateField.adjoin ℚ_[p] {ζ m})
    inferInstance hEK (hstar m hn₀m) x hxm
  -- instances and membership for the level fixed field
  haveI : FiniteDimensional ℚ_[p] ↥(IntermediateField.fixedField (toGalSubgroup H
      ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) := by
    rw [hMn]
    infer_instance
  have hwMn : ∀ i, w i ∈ IntermediateField.fixedField (toGalSubgroup H
      ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup) := fun i => by
    rw [hMn]
    exact (le_sup_left : L ≤ _) (hwL i)
  -- the trace expansion along the coordinates
  have hexp : Algebra.normalizedTrace ↥(IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) (PadicAlgCl p) x
      = ∑ i, (⟨w i, hwMn i⟩ : ↥(IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)))
        • Algebra.normalizedTrace ↥(IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) (PadicAlgCl p) (c i) := by
    conv_lhs => rw [hcx]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : c i * w i = (⟨w i, hwMn i⟩ : ↥(IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup))) • c i := by
      rw [Algebra.smul_def]
      exact mul_comm _ _
    rw [h1, map_smul]
  rw [hexp, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (mul_pos (mul_pos hp0 hD) hsum).le (norm_nonneg x)) fun i _ => ?_
  have hterm : algebraMap ↥(IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) (PadicAlgCl p)
      ((⟨w i, hwMn i⟩ : ↥(IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)))
        • Algebra.normalizedTrace ↥(IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) (PadicAlgCl p) (c i))
      = w i * algebraMap ↥(IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) (PadicAlgCl p)
        (Algebra.normalizedTrace ↥(IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) (PadicAlgCl p) (c i)) := by
    rw [smul_eq_mul, map_mul]
    rfl
  rw [hterm, norm_mul]
  -- the two-level comparison and the delegated cyclotomic bound
  have hKnMn : IntermediateField.adjoin ℚ_[p] {ζ n}
      ≤ IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup) := by
    rw [hMn]
    exact le_sup_right
  have hrank4 : Module.finrank ℚ_[p] ↥(IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)
          ⊔ IntermediateField.adjoin ℚ_[p] {ζ m})
        * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ n})
      = Module.finrank ℚ_[p] ↥(IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup))
        * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ n}
          ⊔ IntermediateField.adjoin ℚ_[p] {ζ m}) := by
    have e2 : IntermediateField.adjoin ℚ_[p] {ζ n} ⊔ IntermediateField.adjoin ℚ_[p] {ζ m}
        = IntermediateField.adjoin ℚ_[p] {ζ m} :=
      sup_eq_right.mpr (adjoin_root_le ζ hζcoh hnm)
    have e1 : IntermediateField.fixedField (toGalSubgroup H
          ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)
          ⊔ IntermediateField.adjoin ℚ_[p] {ζ m}
        = L ⊔ IntermediateField.adjoin ℚ_[p] {ζ m} := by
      rw [hMn, sup_assoc, e2]
    rw [e1, e2, hMn]
    have key : Module.finrank ℚ_[p] ↥(L ⊔ IntermediateField.adjoin ℚ_[p] {ζ m})
          * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ n})
          * Module.finrank ℚ_[p] ↥E₀
        = Module.finrank ℚ_[p] ↥(L ⊔ IntermediateField.adjoin ℚ_[p] {ζ n})
          * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ m})
          * Module.finrank ℚ_[p] ↥E₀ := by
      calc Module.finrank ℚ_[p] ↥(L ⊔ IntermediateField.adjoin ℚ_[p] {ζ m})
            * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ n})
            * Module.finrank ℚ_[p] ↥E₀
          = Module.finrank ℚ_[p] ↥(L ⊔ IntermediateField.adjoin ℚ_[p] {ζ m})
              * Module.finrank ℚ_[p] ↥E₀
              * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ n}) := by ring
        _ = Module.finrank ℚ_[p] ↥L
              * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ m})
              * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ n}) := by
            rw [hstar m hn₀m]
        _ = Module.finrank ℚ_[p] ↥L
              * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ n})
              * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ m}) := by ring
        _ = Module.finrank ℚ_[p] ↥(L ⊔ IntermediateField.adjoin ℚ_[p] {ζ n})
              * Module.finrank ℚ_[p] ↥E₀
              * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ m}) := by
            rw [hstar n hn₀n]
        _ = Module.finrank ℚ_[p] ↥(L ⊔ IntermediateField.adjoin ℚ_[p] {ζ n})
              * Module.finrank ℚ_[p] ↥(IntermediateField.adjoin ℚ_[p] {ζ m})
              * Module.finrank ℚ_[p] ↥E₀ := by ring
    exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos key
  have hcomp : algebraMap ↥(IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) (PadicAlgCl p)
      (Algebra.normalizedTrace ↥(IntermediateField.fixedField (toGalSubgroup H
        ⊓ (IntermediateField.adjoin ℚ_[p] {ζ n}).fixingSubgroup)) (PadicAlgCl p) (c i))
      = algebraMap ↥(IntermediateField.adjoin ℚ_[p] {ζ n}) (PadicAlgCl p)
        (Algebra.normalizedTrace ↥(IntermediateField.adjoin ℚ_[p] {ζ n}) (PadicAlgCl p)
          (c i)) := by
    refine normalizedTrace_eq_of_finrank_mul hKnMn (ζ m) hrank4 ?_
    exact hcK i
  rw [hcomp]
  have hcyc := cyclotomicNormalizedTraceBound p (hζprim m) hn0 hnm (hcK i)
  rw [rootTower_pow ζ hζcoh hnm] at hcyc
  calc ‖w i‖ * ‖algebraMap ↥(IntermediateField.adjoin ℚ_[p] {ζ n}) (PadicAlgCl p)
        (Algebra.normalizedTrace ↥(IntermediateField.adjoin ℚ_[p] {ζ n}) (PadicAlgCl p)
          (c i))‖
      ≤ ‖w i‖ * ((p : ℝ) * ‖c i‖) := mul_le_mul_of_nonneg_left hcyc (norm_nonneg _)
    _ ≤ ‖w i‖ * ((p : ℝ) * (D * ‖x‖)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hcnorm i) hp0.le) (norm_nonneg _)
    _ ≤ (p : ℝ) * D * (1 + ∑ j, ‖w j‖) * ‖x‖ := by
        have h5 : ‖w i‖ ≤ 1 + ∑ j, ‖w j‖ :=
          le_trans (Finset.single_le_sum (fun j _ => norm_nonneg (w j)) (Finset.mem_univ i))
            (le_add_of_nonneg_left zero_le_one)
        have h6 : (0 : ℝ) ≤ (p : ℝ) * (D * ‖x‖) :=
          mul_nonneg hp0.le (mul_nonneg hD.le (norm_nonneg x))
        calc ‖w i‖ * ((p : ℝ) * (D * ‖x‖))
            ≤ (1 + ∑ j, ‖w j‖) * ((p : ℝ) * (D * ‖x‖)) :=
              mul_le_mul_of_nonneg_right h5 h6
          _ = (p : ℝ) * D * (1 + ∑ j, ‖w j‖) * ‖x‖ := by ring

end TateTwistVanishing

/-- **Tate's vanishing theorem**: an element of `ℂ_[p]` on which an open subgroup of the
absolute Galois group acts through a nonzero power of the cyclotomic character is zero
([Brinon–Conrad 2009, Thm. 2.2.7, p.15][BrinonConrad2009], the statement `ℂ_K (r)^{G_K} = 0`
for `r ≠ 0`; [Hyeon 2025, §5, p.18][Hyeon2025], where the invariants of the twists are the
Hodge–Tate machinery's input). -/
theorem tateTwistVanishing (p : ℕ) [Fact p.Prime]
    (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p]))) {r : ℤ} (hr : r ≠ 0)
    {c : ℂ_[p]}
    (hc : ∀ σ ∈ H, padicComplexGaloisAction p σ c
      = ((TateTwist.padicCyclotomicCharacter p ℚ_[p] σ : ℚ_[p]) ^ r) • c) :
    c = 0 := by
  obtain ⟨ζ, -, hζprim, hζcoh⟩ := TateTwistVanishing.exists_rootTower p
  obtain ⟨n₀, C, hC, hbound⟩ := TateTwistVanishing.levelTraceBound H hH ζ hζprim hζcoh
  exact TateTwistVanishing.vanish_of_bound H hH hr hc ζ hζprim hζcoh n₀ C hC hbound

end Atlas.Knowledge
