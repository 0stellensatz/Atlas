import Mathlib
import Atlas.Knowledge.IsLadicRepresentation
import Atlas.Knowledge.PadicComplexGaloisAction
import Atlas.Knowledge.SemiInvariantIndependence
import Atlas.Knowledge.TateTwist

/-!
# Hodge–Tate number

The **Hodge–Tate numbers** of a `p`-adic representation, and Hodge–Tateness: for a subgroup
`H` of the absolute Galois group of `ℚ_[p]` and a representation `ρ` of `H` on a
`ℚ_[p]`-vector space `V`, the `i`th number is the dimension, over the fixed field of `H`, of
the `H`-invariants of `ℂ_[p] ⊗ V(-i)`—the Galois action of
`Atlas.Knowledge.PadicComplexGaloisAction` on the left factor tensored against the `(-i)`th
twist of `ρ` by the cyclotomic character of `Atlas.Knowledge.TateTwist`—and `ρ` is
**Hodge–Tate** when the numbers sum to the dimension of `V`. The sum never exceeds it, which is
the recorded claim, and the fixed-field base of the dimension is computed by
`Atlas.Knowledge.axSenTate`. This is the invariant the source's Section 5 extracts from the
`m`-step solvable representations `Atlas.Knowledge.IsMStepSolvableRep`.

## Main definitions

* `hodgeTateNumber` — the dimension over the fixed field of the invariants of the twisted
  tensor representation.
* `IsHodgeTate` — the numbers sum to the dimension.
* `HodgeTateNumber.twistedTensor` — the representation of `H` on `ℂ_[p] ⊗ V(i)`.
* `HodgeTateNumber.invariants` — its invariants, as a module over the fixed field of `H`.

## Main statements

* `HodgeTateNumber.support_finite` — for an open `H` and a `p`-adic representation—the
  condition of `Atlas.Knowledge.IsLadicRepresentation` at `ℓ = p`—only finitely many numbers
  are nonzero.
* `HodgeTateNumber.finsum_le` — their sum is at most the dimension of `V`.
* `HodgeTateNumber.sum_le` — the finite-partial-sum form both claims reduce to: over any
  finite set of weights, the numbers sum to at most the dimension.

## Implementation notes

The source states the numbers for a `p_K`-adic representation of `G_K`, `K` a
mixed-characteristic local field; here `G_K` is a subgroup `H` of the absolute Galois group of
the base `ℚ_[p]`, the frame of `Atlas.Knowledge.AxSenTate`, and the twist is
`Atlas.Knowledge.tateTwist` along the inclusion of `H`—the restriction to `H` of the base's
cyclotomic character, which is the cyclotomic character of the subextension, an identification
across the two closures that the layer does not yet state and whose vocabulary is
`Atlas.Knowledge.CyclotomicCharacterInvariance`. The `K`-vector space structure enters with no
construction: the invariants are `H`-fixed, the fixed field acts on the left tensor factor
through `ℂ_[p]`, and the action of `H` commutes with that multiplication exactly because the
fixed field is fixed—the content of the `smul_mem'` field of `invariants`. The definitions are
total, and their junk values all fall to `0`: `Module.finrank` vanishes wherever the invariants
have infinite rank, which off the open case is everywhere they are nonzero at all, the fixed
field of a non-open subgroup being incomplete of infinite corank in its completion. The claims
carry `IsOpen` not because they would fail off it—they would hold vacuously, every number
junking to `0`—but because the open case is where the numbers compute the source's
`d^i_{HT,K}`: for open `H` the fixed field is a finite extension of `ℚ_[p]`, complete, and
equal to the fixed points of `ℂ_[p]` by `Atlas.Knowledge.axSenTate`, so the dimension is taken
over the field the source takes it over. `IsHodgeTate` reads the honest equality on the
claims' domain, where the support and the sum are finite; note its junk lands on the *true*
side for a `V` of infinite dimension over `ℚ_[p]`, both sides vanishing, which a consumer
should mind before applying it off the `p`-adic domain.

Both claims reduce to the finite-partial-sum bound `sum_le`, and the reduction never needs
the invariants to be finite-dimensional: the numbers are `Module.finrank`, which vanishes on
infinite rank, so each weight contributes an independent family of exactly its number—junk
weights contribute nothing—and `Atlas.Knowledge.semiInvariantIndependence` makes the union
independent over `ℂ_[p]`, whose dimension caps the count. The representation hypothesis
enters only through the finite-dimensionality of `V`; neither the topology on `V` nor the
continuity of the action plays any role in the bound.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
* [BrinonConrad2009] O. Brinon, B. Conrad, *CMI Summer School notes on p-adic Hodge theory
  (preliminary version)*, available at math.stanford.edu/~conrad/papers/notes.pdf, 2009.
-/

namespace Atlas.Knowledge

open PadicComplexGaloisAction

namespace HodgeTateNumber

variable {p : ℕ} [Fact p.Prime] {H : Subgroup (Field.absoluteGaloisGroup ℚ_[p])}
  {V : Type*} [AddCommGroup V] [Module ℚ_[p] V]

/-- The Galois action of a subgroup of the absolute Galois group of `ℚ_[p]` on `ℂ_[p]`, as a
`ℚ_[p]`-linear representation. -/
noncomputable def galois (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p])) :
    Representation ℚ_[p] ↥H ℂ_[p] :=
  (AlgEquiv.toLinearMapHom ℚ_[p] ℂ_[p]).comp ((padicComplexGaloisAction p).comp H.subtype)

/-- The representation of `H` on `ℂ_[p] ⊗ V(i)`: the Galois action on the left factor,
tensored with the `i`th Tate twist of `ρ` along the inclusion of `H`
([Brinon–Conrad 2009, §2.2, p.12][BrinonConrad2009], the operation `V ↝ ℂ_K ⊗ V` with the
action `g (c ⊗ v) = g(c) ⊗ g(v)`). -/
noncomputable def twistedTensor (ρ : Representation ℚ_[p] ↥H V) (i : ℤ) :
    Representation ℚ_[p] ↥H (TensorProduct ℚ_[p] ℂ_[p] V) :=
  (galois H).tprod (tateTwist ρ H.subtype i)

/-- The action of `H` on `ℂ_[p] ⊗ V(i)` commutes with the multiplication by the fixed field
of `H` on the left factor: the twisted tensor action is linear over the fixed field. -/
theorem twistedTensor_smul (ρ : Representation ℚ_[p] ↥H V) (i : ℤ) (σ : ↥H)
    (f : ↥(IntermediateField.fixedField (toGalSubgroup H))) (x : TensorProduct ℚ_[p] ℂ_[p] V) :
    twistedTensor ρ i σ (f • x) = f • twistedTensor ρ i σ x := by
  have hgalois : ∀ c : ℂ_[p], galois H σ (f • c) = f • galois H σ c := fun c => by
    have hfix : algebraMap ↥(IntermediateField.fixedField (toGalSubgroup H)) ℂ_[p] f
        = ((f : PadicAlgCl p) : ℂ_[p]) := rfl
    have hmap : padicComplexGaloisAction p ↑σ ((f : PadicAlgCl p) : ℂ_[p])
        = ((f : PadicAlgCl p) : ℂ_[p]) := by
      rw [padicComplexGaloisAction_coe]
      exact congrArg _
        ((IntermediateField.mem_fixedField_iff (toGalSubgroup H) _).mp f.2 (toAlgEquiv ↑σ) σ.2)
    calc galois H σ (f • c)
        = padicComplexGaloisAction p ↑σ (algebraMap _ ℂ_[p] f * c) := by
          rw [Algebra.smul_def]; rfl
      _ = algebraMap _ ℂ_[p] f * padicComplexGaloisAction p ↑σ c := by
          rw [map_mul, hfix, hmap]
      _ = f • galois H σ c := by rw [Algebra.smul_def]; rfl
  have key : ∀ (B : V →ₗ[ℚ_[p]] V) (y : TensorProduct ℚ_[p] ℂ_[p] V),
      TensorProduct.map (galois H σ) B (f • y) = f • TensorProduct.map (galois H σ) B y := by
    intro B y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c v =>
        calc TensorProduct.map (galois H σ) B (f • (c ⊗ₜ[ℚ_[p]] v))
            = TensorProduct.map (galois H σ) B ((f • c) ⊗ₜ[ℚ_[p]] v) :=
              congrArg _ (TensorProduct.smul_tmul' f c v)
          _ = galois H σ (f • c) ⊗ₜ[ℚ_[p]] B v := TensorProduct.map_tmul ..
          _ = (f • galois H σ c) ⊗ₜ[ℚ_[p]] B v := by rw [hgalois]
          _ = f • (galois H σ c ⊗ₜ[ℚ_[p]] B v) := (TensorProduct.smul_tmul' f _ _).symm
          _ = f • TensorProduct.map (galois H σ) B (c ⊗ₜ[ℚ_[p]] v) := by
              rw [TensorProduct.map_tmul]
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  exact key _ x

/-- The twisted tensor action is semilinear over the left factor: a `ℂ_[p]` scalar passes
through at the cost of the Galois action on it. -/
theorem twistedTensor_semilinear (ρ : Representation ℚ_[p] ↥H V) (i : ℤ) (σ : ↥H)
    (c : ℂ_[p]) (x : TensorProduct ℚ_[p] ℂ_[p] V) :
    twistedTensor ρ i σ (c • x)
      = padicComplexGaloisAction p ↑σ c • twistedTensor ρ i σ x := by
  have key : ∀ (B : V →ₗ[ℚ_[p]] V) (y : TensorProduct ℚ_[p] ℂ_[p] V),
      TensorProduct.map (galois H σ) B (c • y)
        = padicComplexGaloisAction p ↑σ c • TensorProduct.map (galois H σ) B y := by
    intro B y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        calc TensorProduct.map (galois H σ) B (c • (a ⊗ₜ[ℚ_[p]] v))
            = TensorProduct.map (galois H σ) B ((c * a) ⊗ₜ[ℚ_[p]] v) := by
              rw [TensorProduct.smul_tmul', smul_eq_mul]
          _ = galois H σ (c * a) ⊗ₜ[ℚ_[p]] B v := TensorProduct.map_tmul ..
          _ = (padicComplexGaloisAction p ↑σ c * galois H σ a) ⊗ₜ[ℚ_[p]] B v := by
              congr 1
              exact map_mul (padicComplexGaloisAction p ↑σ) c a
          _ = padicComplexGaloisAction p ↑σ c • (galois H σ a ⊗ₜ[ℚ_[p]] B v) := by
              rw [TensorProduct.smul_tmul', smul_eq_mul]
          _ = padicComplexGaloisAction p ↑σ c
                • TensorProduct.map (galois H σ) B (a ⊗ₜ[ℚ_[p]] v) := by
              rw [TensorProduct.map_tmul]
    | add u w hu hw => rw [smul_add, map_add, map_add, hu, hw, smul_add]
  exact key _ x

/-- The `H`-invariants of `ℂ_[p] ⊗ V(i)`, as a module over the fixed field of `H`: the fixed
field multiplies the left tensor factor, and the action commutes with that multiplication, so
the invariants are stable. -/
noncomputable def invariants (ρ : Representation ℚ_[p] ↥H V) (i : ℤ) :
    Submodule ↥(IntermediateField.fixedField (toGalSubgroup H)) (TensorProduct ℚ_[p] ℂ_[p] V) where
  carrier := {x | ∀ σ : ↥H, twistedTensor ρ i σ x = x}
  add_mem' hx hy σ := by rw [map_add, hx σ, hy σ]
  zero_mem' σ := map_zero _
  smul_mem' f x hx σ := by rw [twistedTensor_smul, hx σ]

/-- Membership in the invariants of the `(-i)`th twist is the eigenvector law for the
untwisted action: the element transforms by the `i`th power of the cyclotomic character. -/
theorem twistedTensor_eq_zpow_smul (ρ : Representation ℚ_[p] ↥H V) (i : ℤ)
    {x : TensorProduct ℚ_[p] ℂ_[p] V} (hx : x ∈ invariants ρ (-i)) (σ : ↥H) :
    twistedTensor ρ 0 σ x
      = ((TateTwist.padicCyclotomicCharacter p ℚ_[p] σ.1 : ℚ_[p]) ^ i) • x := by
  have hmem : twistedTensor ρ (-i) σ x = x := hx σ
  set c : ℚ_[p] := (TateTwist.padicCyclotomicCharacter p ℚ_[p] σ.1 : ℚ_[p]) with hcdef
  have hc0 : c ≠ 0 := Units.ne_zero _
  have hcast : ∀ j : ℤ,
      ((((TateTwist.padicCyclotomicCharacter p ℚ_[p]).comp H.subtype ^ j) σ
        : ℚ_[p]ˣ) : ℚ_[p]) = c ^ j := by
    intro j
    rw [MonoidHom.zpow_apply]
    push_cast
    rfl
  have h0 : (twistedTensor ρ 0) σ = TensorProduct.map ((galois H) σ) (ρ σ) := by
    change TensorProduct.map _ ((tateTwist ρ H.subtype 0) σ) = _
    rw [tateTwist_apply, hcast, zpow_zero, one_smul]
  have hrel : twistedTensor ρ (-i) σ x = c ^ (-i) • twistedTensor ρ 0 σ x := by
    change TensorProduct.map _ ((tateTwist ρ H.subtype (-i)) σ) x = _
    rw [tateTwist_apply, hcast, TensorProduct.map_smul_right, LinearMap.smul_apply, h0]
  rw [hrel] at hmem
  calc twistedTensor ρ 0 σ x = (c ^ i * c ^ (-i)) • twistedTensor ρ 0 σ x := by
        rw [← zpow_add₀ hc0, add_neg_cancel, zpow_zero, one_smul]
    _ = c ^ i • (c ^ (-i) • twistedTensor ρ 0 σ x) := mul_smul _ _ _
    _ = c ^ i • x := by rw [hmem]

end HodgeTateNumber

/-- The `i`th **Hodge–Tate number** of a representation of a subgroup `H` of the absolute
Galois group of `ℚ_[p]`: the dimension, over the fixed field of `H`, of the `H`-invariants of
`ℂ_[p] ⊗ V(-i)` ([Hyeon 2025, §5, p.18][Hyeon2025], the number `d^i_{HT,K}`;
[Brinon–Conrad 2009, Remark 2.3.2, p.17][BrinonConrad2009], the subspaces `W[-i]`). -/
noncomputable def hodgeTateNumber (p : ℕ) [Fact p.Prime]
    (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p])) {V : Type*} [AddCommGroup V]
    [Module ℚ_[p] V] (ρ : Representation ℚ_[p] ↥H V) (i : ℤ) : ℕ :=
  Module.finrank ↥(IntermediateField.fixedField (toGalSubgroup H))
    ↥(HodgeTateNumber.invariants ρ (-i))

/-- **Hodge–Tateness**: the Hodge–Tate numbers of the representation sum to the dimension of
its space—the equality case of `HodgeTateNumber.finsum_le` ([Hyeon 2025, §5, p.18][Hyeon2025];
[Brinon–Conrad 2009, Def. 2.3.4 and Ex. 2.3.5, p.17][BrinonConrad2009], where the intrinsic
`ξ_W`-form is shown equivalent to this sum equality). -/
def IsHodgeTate (p : ℕ) [Fact p.Prime] (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] (ρ : Representation ℚ_[p] ↥H V) : Prop :=
  ∑ᶠ i : ℤ, hodgeTateNumber p H ρ i = Module.finrank ℚ_[p] V

namespace HodgeTateNumber

/-- Over any finite set of weights, the Hodge–Tate numbers sum to at most the dimension of
the space: each weight contributes to `ℂ_[p] ⊗ V` an independent family of size its number,
distinct weights stay independent by the Serre–Tate lemma, and the `ℂ_[p]`-dimension of
`ℂ_[p] ⊗ V` is the `ℚ_[p]`-dimension of `V`
([Brinon–Conrad 2009, Lemma 2.3.1, p.16][BrinonConrad2009], the injectivity of
`ξ_W` restricted to finitely many summands). -/
theorem sum_le (p : ℕ) [Fact p.Prime] (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p]))) {V : Type*} [AddCommGroup V]
    [Module ℚ_[p] V] [FiniteDimensional ℚ_[p] V] (ρ : Representation ℚ_[p] ↥H V)
    (S : Finset ℤ) :
    ∑ i ∈ S, hodgeTateNumber p H ρ i ≤ Module.finrank ℚ_[p] V := by
  classical
  set L := IntermediateField.fixedField (toGalSubgroup H) with hLdef
  set n : ℤ → ℕ := fun i => if i ∈ S then hodgeTateNumber p H ρ i else 0 with hn
  -- one independent family per weight, of size the number
  have hex : ∀ i : ℤ, ∃ f : Fin (n i) → ↥(invariants ρ (-i)), LinearIndependent ↥L f := by
    intro i
    refine exists_linearIndependent_of_le_finrank ?_
    rw [hn]
    dsimp only
    split
    · exact le_rfl
    · exact Nat.zero_le _
  choose b hb using hex
  set y : (Σ i : ℤ, Fin (n i)) → TensorProduct ℚ_[p] ℂ_[p] V :=
    fun j => (b j.1 j.2 : TensorProduct ℚ_[p] ℂ_[p] V) with hydef
  have hymem : ∀ j : Σ i : ℤ, Fin (n i), y j ∈ invariants ρ (-(j.1)) := fun j => (b j.1 j.2).2
  -- within one weight, the family is the chosen one, transported along the fiber
  have hind : ∀ i₀ : ℤ, LinearIndependent (R := ↥L)
      (fun j : {j : Σ i : ℤ, Fin (n i) // j.1 = i₀} => y j.1) := by
    intro i₀
    have hbase : LinearIndependent (R := ↥L)
        (fun k : Fin (n i₀) => (b i₀ k : TensorProduct ℚ_[p] ℂ_[p] V)) :=
      (hb i₀).map' (Submodule.subtype _) (Submodule.ker_subtype _)
    have hfun : (fun j : {j : Σ i : ℤ, Fin (n i) // j.1 = i₀} => y j.1)
        = (fun k : Fin (n i₀) => (b i₀ k : TensorProduct ℚ_[p] ℂ_[p] V))
          ∘ (fun j => Fin.cast (congrArg n j.2) j.1.2) := by
      funext j
      obtain ⟨⟨i, k⟩, hw⟩ := j
      dsimp only at hw
      subst hw
      rfl
    rw [hfun]
    refine hbase.comp _ ?_
    rintro ⟨⟨i, k⟩, hw⟩ ⟨⟨i', k'⟩, hw'⟩ h
    dsimp only at hw hw'
    subst hw
    subst hw'
    simp only [Fin.cast] at h
    exact Subtype.ext (Sigma.ext rfl (by simpa using h))
  -- distinct weights stay independent, and the finite sub-sigma over `S` counts
  have hCp : LinearIndependent ℂ_[p] y :=
    semiInvariantIndependence p H hH (fun σ => twistedTensor ρ 0 σ)
      (fun σ c x => twistedTensor_semilinear ρ 0 σ c x) y (fun j => j.1)
      (fun j σ => twistedTensor_eq_zpow_smul ρ j.1 (hymem j) σ) hind
  set e : (Σ i : ↥S, Fin (n i.1)) → (Σ i : ℤ, Fin (n i)) := fun j => ⟨j.1.1, j.2⟩ with he
  have hinj : Function.Injective e := by
    rintro ⟨⟨i, hi⟩, k⟩ ⟨⟨i', hi'⟩, k'⟩ h
    simp only [he, Sigma.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1
    simp only [heq_eq_eq] at h2
    subst h2
    rfl
  have hfin : LinearIndependent ℂ_[p] (y ∘ e) := hCp.comp e hinj
  have hcard := hfin.fintype_card_le_finrank
  rw [Fintype.card_sigma, Module.finrank_baseChange] at hcard
  calc ∑ i ∈ S, hodgeTateNumber p H ρ i
      = ∑ i : ↥S, n i.1 := by
        rw [← Finset.sum_coe_sort S (fun i => hodgeTateNumber p H ρ i)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hn]
        exact (if_pos i.2).symm
    _ ≤ Module.finrank ℚ_[p] V := by simpa using hcard

/-- For an open subgroup and a `p`-adic representation, only finitely many Hodge–Tate numbers
are nonzero: more than `dim V` of them would overfill a finite partial sum
([Brinon–Conrad 2009, Remark 2.3.2, p.17][BrinonConrad2009], "vanish for all but finitely
many"; [Hyeon 2025, §5, p.18][Hyeon2025], where the finiteness is implicit in the sum over
`ℤ`). -/
theorem support_finite (p : ℕ) [Fact p.Prime] (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p]))) {V : Type*} [AddCommGroup V]
    [Module ℚ_[p] V] [TopologicalSpace V] (ρ : Representation ℚ_[p] ↥H V)
    (hρ : IsLadicRepresentation ρ) : {i : ℤ | hodgeTateNumber p H ρ i ≠ 0}.Finite := by
  haveI := hρ.finiteDimensional
  by_contra hinf
  rw [Set.not_finite] at hinf
  obtain ⟨S, hSsub, hScard⟩ := hinf.exists_subset_card_eq (Module.finrank ℚ_[p] V + 1)
  have hlow : (Module.finrank ℚ_[p] V + 1 : ℕ) ≤ ∑ i ∈ S, hodgeTateNumber p H ρ i := by
    calc (Module.finrank ℚ_[p] V + 1 : ℕ) = ∑ _i ∈ S, 1 := by
          rw [Finset.sum_const, smul_eq_mul, mul_one, hScard]
      _ ≤ ∑ i ∈ S, hodgeTateNumber p H ρ i :=
          Finset.sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr (hSsub hi)
  have hup := sum_le p H hH ρ S
  omega

/-- The Hodge–Tate numbers of a `p`-adic representation of an open subgroup sum to at most
the dimension of its space: the support is finite, and the partial sum over it is bounded
([Hyeon 2025, §5, p.18][Hyeon2025];
[Brinon–Conrad 2009, Remark 2.3.2, p.17][BrinonConrad2009], the injectivity of
`⊕ (ℂ_K ⊗ W[q]) → W`). -/
theorem finsum_le (p : ℕ) [Fact p.Prime] (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p]))) {V : Type*} [AddCommGroup V]
    [Module ℚ_[p] V] [TopologicalSpace V] (ρ : Representation ℚ_[p] ↥H V)
    (hρ : IsLadicRepresentation ρ) :
    ∑ᶠ i : ℤ, hodgeTateNumber p H ρ i ≤ Module.finrank ℚ_[p] V := by
  haveI := hρ.finiteDimensional
  have hsupp : (Function.support fun i : ℤ => hodgeTateNumber p H ρ i).Finite :=
    support_finite p H hH ρ hρ
  rw [finsum_eq_sum _ hsupp]
  exact sum_le p H hH ρ _

end HodgeTateNumber

end Atlas.Knowledge
