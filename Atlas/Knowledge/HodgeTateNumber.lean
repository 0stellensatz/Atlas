import Mathlib
import Atlas.Knowledge.CharacterTwist
import Atlas.Knowledge.IsLadicRepresentation
import Atlas.Knowledge.PadicComplexGaloisAction
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

Both are claims recorded ahead of their proofs.

* `HodgeTateNumber.support_finite` — for an open `H` and an `ℓ`-adic representation, only
  finitely many numbers are nonzero.
* `HodgeTateNumber.finsum_le` — their sum is at most the dimension of `V`.

## Implementation notes

The source states the numbers for a `p_K`-adic representation of `G_K`, `K` a
mixed-characteristic local field; here `G_K` is a subgroup `H` of the absolute Galois group of
the base `ℚ_[p]`, the frame of `Atlas.Knowledge.AxSenTate`, and the twist is by the cyclotomic
character of the base restricted to `H`, which is the cyclotomic character of the subextension.
The `K`-vector space structure enters with no construction: the invariants are `H`-fixed, the
fixed field acts on the left tensor factor through `ℂ_[p]`, and the action of `H` commutes
with that multiplication exactly because the fixed field is fixed—the content of the
`smul_mem'` field of `invariants`. The definitions are total: for a subgroup that is not open,
or a representation that is not `ℓ`-adic, the numbers are whatever `Module.finrank` junk-values
them to be—`0` wherever the invariants have infinite rank—and the recorded claims say nothing
there; `IsHodgeTate` reads the honest equality on the claims' domain, where the support is
finite, and compares a finite sum. The claims carry `IsOpen` rather than `IsClosed` because
the source's base is a mixed-characteristic local field: for a general closed subgroup the
cyclotomic character can die on `H` and the twists collapse, so finiteness of the support is
genuinely a statement about the open case.

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
tensored with the `i`th Tate twist of `ρ`—the twist by the `i`th power of the cyclotomic
character of the base restricted to `H`
([Brinon–Conrad 2009, §2.2, p.12][BrinonConrad2009], the operation `V ↝ ℂ_K ⊗ V` with the
action `g (c ⊗ v) = g(c) ⊗ g(v)`). -/
noncomputable def twistedTensor (ρ : Representation ℚ_[p] ↥H V) (i : ℤ) :
    Representation ℚ_[p] ↥H (TensorProduct ℚ_[p] ℂ_[p] V) :=
  (galois H).tprod
    (characterTwist ρ ((TateTwist.padicCyclotomicCharacter p ℚ_[p]).comp H.subtype ^ i))

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

/-- The `H`-invariants of `ℂ_[p] ⊗ V(i)`, as a module over the fixed field of `H`: the fixed
field multiplies the left tensor factor, and the action commutes with that multiplication, so
the invariants are stable. -/
noncomputable def invariants (ρ : Representation ℚ_[p] ↥H V) (i : ℤ) :
    Submodule ↥(IntermediateField.fixedField (toGalSubgroup H)) (TensorProduct ℚ_[p] ℂ_[p] V) where
  carrier := {x | ∀ σ : ↥H, twistedTensor ρ i σ x = x}
  add_mem' hx hy σ := by rw [map_add, hx σ, hy σ]
  zero_mem' σ := map_zero _
  smul_mem' f x hx σ := by rw [twistedTensor_smul, hx σ]

end HodgeTateNumber

/-- The `i`th **Hodge–Tate number** of a representation of a subgroup `H` of the absolute
Galois group of `ℚ_[p]`: the dimension, over the fixed field of `H`, of the `H`-invariants of
`ℂ_[p] ⊗ V(-i)` ([Hyeon 2025, §5, p.18][Hyeon2025], the number `d^i_{HT,K}`;
[Brinon–Conrad 2009, Remark 2.3.2, p.17][BrinonConrad2009], the subspaces `W[q]`). -/
noncomputable def hodgeTateNumber (p : ℕ) [Fact p.Prime]
    (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p])) {V : Type*} [AddCommGroup V]
    [Module ℚ_[p] V] (ρ : Representation ℚ_[p] ↥H V) (i : ℤ) : ℕ :=
  Module.finrank ↥(IntermediateField.fixedField (toGalSubgroup H))
    ↥(HodgeTateNumber.invariants ρ (-i))

/-- **Hodge–Tateness**: the Hodge–Tate numbers of the representation sum to the dimension of
its space—the equality case of `HodgeTateNumber.finsum_le`
([Hyeon 2025, §5, p.18][Hyeon2025]; [Brinon–Conrad 2009, Def. 2.3.4, p.17][BrinonConrad2009]). -/
def IsHodgeTate (p : ℕ) [Fact p.Prime] (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] (ρ : Representation ℚ_[p] ↥H V) : Prop :=
  ∑ᶠ i : ℤ, hodgeTateNumber p H ρ i = Module.finrank ℚ_[p] V

namespace HodgeTateNumber

/-- For an open subgroup and an `ℓ`-adic representation, only finitely many Hodge–Tate numbers
are nonzero. Claim recorded ahead of its proof ([Hyeon 2025, §5, p.18][Hyeon2025];
[Brinon–Conrad 2009, Remark 2.3.2, p.17][BrinonConrad2009]). -/
theorem support_finite (p : ℕ) [Fact p.Prime] (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p]))) {V : Type*} [AddCommGroup V]
    [Module ℚ_[p] V] [TopologicalSpace V] (ρ : Representation ℚ_[p] ↥H V)
    (hρ : IsLadicRepresentation ρ) : {i : ℤ | hodgeTateNumber p H ρ i ≠ 0}.Finite := by
  sorry

/-- The Hodge–Tate numbers of an `ℓ`-adic representation of an open subgroup sum to at most
the dimension of its space. Claim recorded ahead of its proof
([Hyeon 2025, §5, p.18][Hyeon2025]; [Brinon–Conrad 2009, Remark 2.3.2,
p.17][BrinonConrad2009], the injectivity of `⊕ (ℂ_K ⊗ W[q]) → W`). -/
theorem finsum_le (p : ℕ) [Fact p.Prime] (H : Subgroup (Field.absoluteGaloisGroup ℚ_[p]))
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup ℚ_[p]))) {V : Type*} [AddCommGroup V]
    [Module ℚ_[p] V] [TopologicalSpace V] (ρ : Representation ℚ_[p] ↥H V)
    (hρ : IsLadicRepresentation ρ) :
    ∑ᶠ i : ℤ, hodgeTateNumber p H ρ i ≤ Module.finrank ℚ_[p] V := by
  sorry

end HodgeTateNumber

end Atlas.Knowledge
