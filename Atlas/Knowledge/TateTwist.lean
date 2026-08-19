import Mathlib
import Atlas.Knowledge.CharacterTwist

/-!
# Tate twist

The **Tate twist** `V(i)` of a representation presented over an absolute Galois group: the
character twist `Atlas.Knowledge.CharacterTwist` by the `i`th power of the `p`-adic cyclotomic
character, pulled back along a homomorphism into the Galois group, for `i` any integer. At the
identity this is the source's twist `V(χ_K^i)` of a representation of `G_K` itself; at the
inclusion of a subgroup it is the twist the `i`th Hodge–Tate number of
`Atlas.Knowledge.hodgeTateNumber` tensors against, at exponent `-i`. The supporting definition
realizes the cyclotomic character of Mathlib as a `ℚ_[p]ˣ`-valued character of
`Field.absoluteGaloisGroup`.

## Main definitions

* `tateTwist` — the representation `ρ(χ_K^i ∘ φ)` on the same space.
* `TateTwist.padicCyclotomicCharacter` — the `p`-adic cyclotomic character as a character of
  the absolute Galois group valued in `ℚ_[p]ˣ`.

## Implementation notes

Mathlib's `cyclotomicCharacter` is `ℤ_[p]ˣ`-valued on the ring automorphisms of a domain, and
honest exactly when the domain has enough `p`-power roots of unity; the algebraic closure of a
characteristic-`0` field always does, and for other base fields the values are junk and nothing
is claimed. The composite pushes the units of `ℤ_[p]` into the units of `ℚ_[p]` so that the
twist can rescale a `ℚ_[p]`-linear representation, and the integer power is taken in the
commutative group of `ℚ_[p]ˣ`-valued characters, so a single definition covers both the twists
and their inverses. The representation's group is any monoid presented over the Galois group by
a homomorphism `φ` rather than the Galois group itself, so that a representation of a subgroup
—the situation of `Atlas.Knowledge.hodgeTateNumber`—twists by the same definition, along the
subgroup's inclusion. The Galois elements enter through their underlying ring automorphisms, as
in `Atlas.Knowledge.CyclotomicCharacterInvariance`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

namespace TateTwist

/-- The `p`-adic cyclotomic character of the absolute Galois group, valued in `ℚ_[p]ˣ`:
Mathlib's `cyclotomicCharacter` of the algebraic closure, on the underlying ring automorphism,
with the units of `ℤ_[p]` pushed into the units of `ℚ_[p]`
([Hyeon 2025, §5, p.18][Hyeon2025], the character `χ_K`). -/
noncomputable def padicCyclotomicCharacter (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] :
    Field.absoluteGaloisGroup K →* ℚ_[p]ˣ :=
  (Units.map (PadicInt.Coe.ringHom (p := p)).toMonoidHom).comp
    ((cyclotomicCharacter (AlgebraicClosure K) p).comp
      (MonoidHom.mk'
        (fun σ => (σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K).toRingEquiv)
        fun _ _ => rfl))

end TateTwist

/-- The **Tate twist** `V(i)`: the twist of a representation, presented over the absolute
Galois group of `K` by a homomorphism `φ`, by the `i`th power of the `p`-adic cyclotomic
character pulled back along `φ`, on the same space—the source's twist of a representation of
`G_K` itself at `φ` the identity ([Hyeon 2025, §5, p.18][Hyeon2025], the twist `(ρ(χ), V(χ))`
at `χ = χ_K^i` and the Tate twist `V(-i) = V(χ_K^{-i})`). -/
noncomputable def tateTwist {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] {G : Type*}
    [Monoid G] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] (ρ : Representation ℚ_[p] G V)
    (φ : G →* Field.absoluteGaloisGroup K) (i : ℤ) : Representation ℚ_[p] G V :=
  characterTwist ρ ((TateTwist.padicCyclotomicCharacter p K).comp φ ^ i)

@[simp]
theorem tateTwist_apply {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] (ρ : Representation ℚ_[p] G V)
    (φ : G →* Field.absoluteGaloisGroup K) (i : ℤ) (σ : G) :
    tateTwist ρ φ i σ
      = ((((TateTwist.padicCyclotomicCharacter p K).comp φ ^ i) σ : ℚ_[p]ˣ) : ℚ_[p]) • ρ σ :=
  rfl

end Atlas.Knowledge
