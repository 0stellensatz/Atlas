import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# local Tate duality

The duality theorem of the Galois cohomology of a mixed-characteristic local field: for a
finite discrete module `A` over the absolute Galois group and its dual partner `B`—a finite
discrete module in perfect equivariant pairing with `A` into the units of the algebraic
closure, classically `A' = Hom (A, μ)`—the continuous cohomology in degree `i ≤ 2` of `B` is
the Pontryagin dual of that of `A` in degree `2 - i`. Alongside it, the two finiteness facts
the theorem lives with: every cohomology group of a finite discrete module is finite, and
everything above degree `2` vanishes. This is the item the cyclotomic-character recovery
`cyclotomicCharacter_comp` of `Atlas.Knowledge.CyclotomicCharacterInvariance` opens with: for
`M` of order `p^n` the duality reads `H^2 (K, M)` off the invariants of the dual partner, which
detects `M ≅ ℤ/p^n (1)`. The degree-two computation `H^2 (K, μ_n) ≅ ℤ/n` of the classical
statements is the instance of the duality at the evaluation pairing of `μ_n` against `ℤ/n`
with trivial action.

## Main statements

All are claims recorded ahead of their proofs.

* `localTateDuality` — the duality isomorphism in degrees `0 ≤ i ≤ 2`.
* `LocalTateDuality.finite_continuousCohomology` — finiteness in every degree.
* `LocalTateDuality.subsingleton_continuousCohomology` — vanishing above degree `2`.

## Implementation notes

A module enters as a `TopRep ℤ (Field.absoluteGaloisGroup K)` with finite discrete carrier,
and its cohomology is Mathlib's `continuousCohomology`, whose homogeneous cochains compute the
classical continuous-cochain cohomology over the profinite Galois group. Mathlib's
`ContRepresentation` constrains the action in the module variable only, so the open-stabilizer
hypothesis carried by every statement is exactly what "discrete Galois module" adds: without
it the statements would quantify over non-continuous actions, about which the classical
theorems say nothing. The dual partner is pinned by a perfect equivariant pairing rather than
constructed as `Hom (A, μ)`: the pairing data determines `B` up to equivariant isomorphism as
the classical `A'`, the evaluation pairing realizes it, and stating through the pairing keeps
the file free of definitions, which may not carry a `sorry`. The duality is recorded as its
isomorphism conclusion and not as perfection of the cup product, which has no vocabulary at
the pinned Mathlib; when a cup product on `continuousCohomology` lands, the pairing form is
the strengthening to state. `ℚ/ℤ` is `AddCircle (1 : ℚ)`. The `i ≤ 2` bound is load-bearing
against the truncated subtraction: at `i = 3` the unguarded statement would read `H^3 (B)`
against the dual of `H^0 (A)` and is false, `H^3` vanishing while `H^0` need not.

## References

* [Serre1994] J-P. Serre, *Cohomologie galoisienne*, Lecture Notes in Mathematics **5**,
  Springer-Verlag Berlin Heidelberg, fifth edition, 1994.
* [NeukirchEtAl2008] J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of number fields*,
  Grundlehren der mathematischen Wissenschaften **323**, Springer Berlin Heidelberg, 2008.
* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- **Local Tate duality**: for finite discrete modules `A` and `B` over the absolute Galois
group of a mixed-characteristic local field, in perfect equivariant pairing into the units of
the algebraic closure—`B` is the classical `A' = Hom (A, μ)`—the degree-`i` continuous
cohomology of `B`, `i ≤ 2`, is the Pontryagin dual of the degree-`(2 - i)` continuous
cohomology of `A`. Claim recorded ahead of its proof
([Serre 1994, Chap. II, §5.2, Thm. 2, pp.101–102][Serre1994];
[Neukirch–Schmidt–Wingberg 2008, Chap. VII, Thm. (7.2.6), p.380][NeukirchEtAl2008];
[Mochizuki 1997, §1, pp.500–501][Mochizuki1997]). -/
theorem localTateDuality (A B : TopRep ℤ (Field.absoluteGaloisGroup K))
    [Finite A] [DiscreteTopology A] [Finite B] [DiscreteTopology B]
    (hA : ∀ a : A, IsOpen {σ : Field.absoluteGaloisGroup K | A.ρ σ a = a})
    (hB : ∀ b : B, IsOpen {σ : Field.absoluteGaloisGroup K | B.ρ σ b = b})
    (P : B →+ A →+ Additive (AlgebraicClosure K)ˣ)
    (hP : ∀ (σ : Field.absoluteGaloisGroup K) (b : B) (a : A),
      P (B.ρ σ b) (A.ρ σ a) = Additive.ofMul
        (Units.map (σ.toRingEquiv : AlgebraicClosure K →* AlgebraicClosure K) (P b a).toMul))
    (hPB : ∀ b : B, P b = 0 → b = 0) (hPA : ∀ a : A, (∀ b : B, P b a = 0) → a = 0)
    (i : ℕ) (hi : i ≤ 2) :
    Nonempty ((continuousCohomology i B : TopModuleCat ℤ) ≃+
      ((continuousCohomology (2 - i) A : TopModuleCat ℤ) →+ AddCircle (1 : ℚ))) := by
  sorry

namespace LocalTateDuality

/-- The continuous cohomology of a finite discrete module over the absolute Galois group of a
mixed-characteristic local field is finite in every degree. Claim recorded ahead of its proof
([Serre 1994, Chap. II, §5.2, Prop. 14, p.101][Serre1994];
[Neukirch–Schmidt–Wingberg 2008, Chap. VII, Thm. (7.1.8) (iii), p.376][NeukirchEtAl2008]). -/
theorem finite_continuousCohomology (A : TopRep ℤ (Field.absoluteGaloisGroup K))
    [Finite A] [DiscreteTopology A]
    (hA : ∀ a : A, IsOpen {σ : Field.absoluteGaloisGroup K | A.ρ σ a = a}) (i : ℕ) :
    Finite (continuousCohomology i A : TopModuleCat ℤ) := by
  sorry

/-- The continuous cohomology of a finite discrete module over the absolute Galois group of a
mixed-characteristic local field vanishes above degree `2`: the group is of cohomological
dimension `2`. Claim recorded ahead of its proof
([Serre 1994, Chap. II, §5.2, p.101][Serre1994];
[Neukirch–Schmidt–Wingberg 2008, Chap. VII, Thm. (7.1.8) (i), p.376][NeukirchEtAl2008]). -/
theorem subsingleton_continuousCohomology (A : TopRep ℤ (Field.absoluteGaloisGroup K))
    [Finite A] [DiscreteTopology A]
    (hA : ∀ a : A, IsOpen {σ : Field.absoluteGaloisGroup K | A.ρ σ a = a}) {i : ℕ}
    (hi : 3 ≤ i) :
    Subsingleton (continuousCohomology i A : TopModuleCat ℤ) := by
  sorry

end LocalTateDuality

end Atlas.Knowledge
