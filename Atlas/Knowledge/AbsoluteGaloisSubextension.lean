import Mathlib

/-!
# absolute Galois group of a subextension

The fixing subgroup of a subextension is the absolute Galois group of the subextension: for an
intermediate field `l` of the algebraic closure of `k`, the subgroup of
`Field.absoluteGaloisGroup k` fixing `l` pointwise, in its subspace topology, is topologically
isomorphic to `Field.absoluteGaloisGroup ↥l`. Combined with the infinite Galois correspondence—in
characteristic zero every open subgroup is the fixing subgroup of a finite subextension, proved
here from Mathlib's `InfiniteGalois`—this is the identification of open subgroups of the
absolute Galois group with absolute Galois groups of finite extensions, the mechanism by which
a group-theoretic statement about open subgroups becomes a field-theoretic statement about
finite extensions, as in the level identity of `Atlas.Knowledge.MStepSolvableSubextension`.

## Main statements

* `absoluteGaloisSubextension_continuousMulEquiv` — the fixing subgroup of `l` is the absolute
  Galois group of `l`, topologically. Proved.
* `AbsoluteGaloisSubextension.exists_fixingSubgroup_of_isOpen` — in characteristic zero, an
  open subgroup is the fixing subgroup of a finite subextension. Proved.

## Implementation notes

The isomorphism claim is `Nonempty`-shaped because it conjugates a choice: `AlgebraicClosure
↥l` and `AlgebraicClosure k` are two algebraic closures of `l`, identified by an `l`-algebra
isomorphism that exists but is not canonical. The topological content is that the subspace
topology on the fixing subgroup is its own Krull topology, which holds because the two
neighborhood bases of `1` interleave: transporting the finitely many basis vectors of a
finite subextension across the identification of closures turns a basic open on either side
into a basic open on the other, and an automorphism fixing the transported generators fixes
the subextension they adjoin to. No hypothesis on `k` is needed for the isomorphism—the
algebraic closure of `k` is algebraic over `l` and algebraically closed, so it is an
algebraic closure of `l` in any characteristic; the cited proposition covers the Galois
case, and the general case and the topological half are this standard argument, which is why
the docstring marks them so rather than sourced. The open-subgroup dictionary does need the
Galois correspondence, so it asks for `CharZero`, which makes the algebraic closure Galois
over `k`—the layer applies it to mixed-characteristic local fields only. The dictionary
produces the fixing subgroup equal to the given subgroup, not merely isomorphic, so consumers
can rewrite along it.

## References

* [MilneFT] J. S. Milne, *Fields and Galois theory* (v5.10), available at www.jmilne.org/math/,
  2022.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/- An automorphism over the base fixing a generating set pointwise fixes the whole
adjunction: the fixed points absorb the base, sums, products, and inverses. -/
private theorem fixes_adjoin {k E : Type*} [Field k] [Field E] [Algebra k E]
    (σ : E ≃ₐ[k] E) {S : Set E} (hS : ∀ x ∈ S, σ x = x) :
    ∀ x ∈ IntermediateField.adjoin k S, σ x = x := by
  intro x hx
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy => exact hS y hy
  | algebraMap y => exact σ.commutes y
  | add y z hy hz hy' hz' => rw [map_add, hy', hz']
  | inv y hy hy' => rw [map_inv₀, hy']
  | mul y z hy hz hy' hz' => rw [map_mul, hy', hz']

/- A finite-dimensional intermediate field sits inside the adjunction of the coerced
vectors of any of its finite bases. -/
private theorem le_adjoin_finset {k E : Type*} [Field k] [Field E] [Algebra k E]
    (F : IntermediateField k E) [FiniteDimensional k ↥F] :
    ∃ t : Finset E, F ≤ IntermediateField.adjoin k (t : Set E) := by
  classical
  set b := Module.finBasis k ↥F
  refine ⟨Finset.univ.image fun j => ((b j : ↥F) : E), fun x hx => ?_⟩
  have hval := congrArg F.val (b.sum_repr ⟨x, hx⟩)
  rw [map_sum] at hval
  rw [show x = F.val ⟨x, hx⟩ from rfl, ← hval]
  refine sum_mem fun j _ => ?_
  rw [map_smul, Algebra.smul_def]
  exact mul_mem (IntermediateField.algebraMap_mem _ _)
    (IntermediateField.subset_adjoin _ _
      (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)))

/-- The fixing subgroup of a subextension `l`, in its subspace topology, is the absolute Galois
group of `l`: restriction of scalars along `k ⊆ l` and a choice of `l`-isomorphism of
algebraic closures exhibit `Gal (k̄ / l)` as `Field.absoluteGaloisGroup ↥l`
([Milne 2022, Chap. 7, Prop. 7.12, p.97][MilneFT] for the correspondence when the closure is
Galois over `k`; the general case and the matching of the subspace topology with the Krull
topology are standard, per the implementation notes). -/
theorem absoluteGaloisSubextension_continuousMulEquiv (k : Type*) [Field k]
    (l : IntermediateField k (AlgebraicClosure k)) :
    Nonempty (↥l.fixingSubgroup ≃ₜ* Field.absoluteGaloisGroup ↥l) := by
  haveI halg : Algebra.IsAlgebraic ↥l (AlgebraicClosure k) :=
    Algebra.IsAlgebraic.tower_top (K := k) ↥l
  haveI : IsAlgClosure ↥l (AlgebraicClosure k) := ⟨inferInstance, halg⟩
  let i : AlgebraicClosure k ≃ₐ[↥l] AlgebraicClosure ↥l :=
    IsAlgClosure.equiv ↥l (AlgebraicClosure k) (AlgebraicClosure ↥l)
  let e : ↥l.fixingSubgroup ≃* (AlgebraicClosure ↥l ≃ₐ[↥l] AlgebraicClosure ↥l) :=
    (IntermediateField.fixingSubgroupEquiv l).trans i.autCongr
  have heval : ∀ (σ : ↥l.fixingSubgroup) (x : AlgebraicClosure ↥l),
      e σ x = i ((σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (i.symm x)) :=
    fun σ x => rfl
  have hsymmval : ∀ (τ : AlgebraicClosure ↥l ≃ₐ[↥l] AlgebraicClosure ↥l)
      (x : AlgebraicClosure k),
      ((e.symm τ : ↥l.fixingSubgroup) : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) x =
        i.symm (τ (i x)) :=
    fun τ x => rfl
  -- forward continuity, checked at the identity against the Krull bases
  have hcont : Continuous e := by
    apply continuous_of_continuousAt_one
    rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro U hU
    obtain ⟨F, hFfin, hFU⟩ :=
      (krullTopology_mem_nhds_one_iff ↥l (AlgebraicClosure ↥l) U).mp hU
    haveI := hFfin
    obtain ⟨t, hFle⟩ := le_adjoin_finset F
    haveI : Finite ↥(⇑i.symm '' (t : Set (AlgebraicClosure ↥l))) :=
      Set.Finite.to_subtype (t.finite_toSet.image _)
    haveI : FiniteDimensional k
        ↥(IntermediateField.adjoin k (⇑i.symm '' (t : Set (AlgebraicClosure ↥l)))) :=
      IntermediateField.finiteDimensional_adjoin fun x _ =>
        (Algebra.IsAlgebraic.isAlgebraic (R := k) x).isIntegral
    rw [nhds_subtype_eq_comap]
    refine Filter.mem_comap.mpr
      ⟨((IntermediateField.adjoin k
            (⇑i.symm '' (t : Set (AlgebraicClosure ↥l)))).fixingSubgroup :
          Set (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k)),
        (IntermediateField.fixingSubgroup_isOpen _).mem_nhds (Subgroup.one_mem _), ?_⟩
    intro σ hσ
    refine Set.mem_preimage.mpr (hFU ?_)
    have hfix : ∀ y ∈ (t : Set (AlgebraicClosure ↥l)), e σ y = y := by
      intro y hy
      rw [heval σ y]
      have hσy : (σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) (i.symm y) = i.symm y :=
        ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hσ) _
          (IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩)
      rw [hσy, AlgEquiv.apply_symm_apply]
    exact IntermediateField.fixingSubgroup_antitone hFle
      ((IntermediateField.mem_fixingSubgroup_iff _ _).mpr (fixes_adjoin (e σ) hfix))
  -- backward continuity, the same argument through the inverse identification
  have hcont' : Continuous e.symm := by
    rw [continuous_induced_rng]
    apply continuous_of_continuousAt_one (l.fixingSubgroup.subtype.comp e.symm.toMonoidHom)
    rw [ContinuousAt, map_one, Filter.tendsto_def]
    intro U hU
    obtain ⟨E, hEfin, hEU⟩ :=
      (krullTopology_mem_nhds_one_iff k (AlgebraicClosure k) U).mp hU
    haveI := hEfin
    obtain ⟨t, hEle⟩ := le_adjoin_finset E
    haveI : Finite ↥(⇑i '' (t : Set (AlgebraicClosure k))) :=
      Set.Finite.to_subtype (t.finite_toSet.image _)
    haveI : FiniteDimensional ↥l
        ↥(IntermediateField.adjoin ↥l (⇑i '' (t : Set (AlgebraicClosure k)))) :=
      IntermediateField.finiteDimensional_adjoin fun x _ =>
        (Algebra.IsAlgebraic.isAlgebraic (R := ↥l) x).isIntegral
    refine Filter.mem_of_superset
      ((IntermediateField.fixingSubgroup_isOpen
          (IntermediateField.adjoin ↥l (⇑i '' (t : Set (AlgebraicClosure k))))).mem_nhds
        (Subgroup.one_mem _)) ?_
    intro τ hτ
    refine Set.mem_preimage.mpr (hEU ?_)
    have hfix : ∀ y ∈ (t : Set (AlgebraicClosure k)),
        ((e.symm τ : ↥l.fixingSubgroup) :
          AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) y = y := by
      intro y hy
      rw [hsymmval τ y]
      have hτy : τ (i y) = i y :=
        ((IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ) _
          (IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩)
      rw [hτy, AlgEquiv.symm_apply_apply]
    exact IntermediateField.fixingSubgroup_antitone hEle
      ((IntermediateField.mem_fixingSubgroup_iff _ _).mpr
        (fixes_adjoin ((e.symm τ : ↥l.fixingSubgroup) :
          AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) hfix))
  exact ⟨{ e with continuous_toFun := hcont, continuous_invFun := hcont' }⟩

namespace AbsoluteGaloisSubextension

/-- In characteristic zero, an open subgroup of the absolute Galois group is the fixing
subgroup of a finite subextension: its fixed field is finite-dimensional over `k` and cuts it
back out. With `absoluteGaloisSubextension_continuousMulEquiv` this identifies open subgroups
with absolute Galois groups of finite extensions
([Milne 2022, Chap. 7, Thm. 7.13, p.98][MilneFT]; [Hyeon 2025, §2, p.8][Hyeon2025]). -/
theorem exists_fixingSubgroup_of_isOpen (k : Type*) [Field k] [CharZero k]
    {H : Subgroup (Field.absoluteGaloisGroup k)}
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup k))) :
    ∃ l : IntermediateField k (AlgebraicClosure k),
      FiniteDimensional k ↥l ∧ l.fixingSubgroup = H := by
  have hc : IsClosed (H : Set (Field.absoluteGaloisGroup k)) := Subgroup.isClosed_of_isOpen H hH
  have hfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hc⟩
  refine ⟨IntermediateField.fixedField H, ?_, hfix⟩
  exact (InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField H)).mp
    (by rw [hfix]; exact hH)

end AbsoluteGaloisSubextension

end Atlas.Knowledge
