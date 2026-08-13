import Mathlib

/-!
# character twist

The **character twist** `ρ(χ)` of a representation `ρ` by a character `χ`: the same underlying
space, with the action rescaled to `σ ↦ χ(σ) • ρ(σ)`. The source introduces it for `ℓ`-adic
representations `Atlas.Knowledge.IsLadicRepresentation`, where twisting by powers of the
cyclotomic character produces the Tate twists its Hodge–Tate numbers are computed from; the
construction itself needs only a commutative coefficient ring, and is stated at that
generality.

## Main definitions

* `characterTwist` — the representation `σ ↦ χ(σ) • ρ(σ)`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

variable {k G V : Type*} [CommSemiring k] [Monoid G] [AddCommMonoid V] [Module k V]

/-- The **character twist** of a representation by a character: the action
`σ ↦ χ(σ) • ρ(σ)` on the same space ([Hyeon 2025, §5, p.18][Hyeon2025]). -/
def characterTwist (ρ : Representation k G V) (χ : G →* kˣ) : Representation k G V where
  toFun σ := (χ σ : k) • ρ σ
  map_one' := by simp
  map_mul' σ τ := by
    rw [map_mul, map_mul, Units.val_mul, smul_mul_assoc, mul_smul_comm, smul_smul]

@[simp]
theorem characterTwist_apply (ρ : Representation k G V) (χ : G →* kˣ) (σ : G) :
    characterTwist ρ χ σ = (χ σ : k) • ρ σ :=
  rfl

end Atlas.Knowledge
