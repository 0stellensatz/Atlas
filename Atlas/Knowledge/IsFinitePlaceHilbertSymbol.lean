import Mathlib
import Atlas.Knowledge.IsLocalHilbertSymbol
import Atlas.Knowledge.AdicCompletionIsMixedCharLocalField

/-!
# finite-place Hilbert symbol

The Hilbert symbol of two global units at a finite place of a number field, as a
characterization: `IsFinitePlaceHilbertSymbol K n v h` says the function
`h : Kˣ → Kˣ → Kˣ` is the restriction along the completion embedding of some `n`-th local
Hilbert symbol of `v.adicCompletion K` — the local pairing of
`Atlas.Knowledge.IsLocalHilbertSymbol` evaluated on the images of global units, its value
descended back to the base field. The local symbol is itself a characterization, so the
finite-place factor is one too; what the predicate already pins, it pins sorry-free — the
values are `n`-th roots of unity, the symbol is bimultiplicative, and two symbols for the
same place and exponent agree. Existence is recorded ahead of its proof.

## Main definitions

* `IsFinitePlaceHilbertSymbol` — `h` restricts some local Hilbert symbol at `v` along
  `Kˣ → (v.adicCompletion K)ˣ`.

## Main statements

* `exists_isFinitePlaceHilbertSymbol` — existence, recorded ahead of its proof.
* `IsFinitePlaceHilbertSymbol.pow_eq_one`, `.mul_left`, `.mul_right` — values and
  bimultiplicativity, proved by descent along the completion embedding.
* `IsFinitePlaceHilbertSymbol.unique` — the characterization pins the symbol; proved
  modulo the recorded uniqueness chain of the local layer.

## Implementation notes

The predicate quantifies over the local-field certificate of
`Atlas.Knowledge.AdicCompletionIsMixedCharLocalField` rather than assuming it: the
certificate is a proof-irrelevant proposition, so the quantification leaves the
predicate's truth unchanged while keeping every downstream statement free of instance
binders — the derived lemmas, which must instantiate it, take it as an instance
hypothesis instead, and the recorded `adicCompletion_isMixedCharLocalField` is what keeps
all of them non-vacuous. The value of `h` lives in `Kˣ` and is pinned through the
injective `Units.map` of the completion embedding, which is the descent to `μₙ(K)` the
literature performs with the bijection `μₙ(K) ≅ μₙ(K_v)`; the source instead constructs
the local value and transports it with a chosen equivalence of root subgroups
(`GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/Core.lean:158`). Milne's
Remark 5.9 — `(a,b)_v = φ_v(b)(a^{1/n})/a^{1/n}` — is Phase 3's characterization
verbatim, which is why no new normalization enters here. `unique` consumes
`Atlas.Knowledge.IsLocalHilbertSymbol.unique` and inherits its recorded backlog through
the axiom audit.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open NumberField IsDedekindDomain

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- The **finite-place Hilbert symbol** characterization of `h : Kˣ → Kˣ → Kˣ`: some
`n`-th local Hilbert symbol `H` of the completion at `v` restricts to `h` along the
completion embedding — the local pairing on global arguments, descended to `μₙ(K)`
([Milne 2020, Chap. VIII, §5, Rem. 5.9, p.247][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/Core.lean:158`]
[Yamaguchi2026]). -/
def IsFinitePlaceHilbertSymbol (n : ℕ) (v : HeightOneSpectrum (𝓞 K))
    (h : Kˣ → Kˣ → Kˣ) : Prop :=
  ∀ _cert : IsMixedCharLocalField (v.adicCompletion K),
    ∃ H : (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ → (v.adicCompletion K)ˣ,
      IsLocalHilbertSymbol (v.adicCompletion K) n H ∧
      ∀ a b : Kˣ,
        Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom (h a b) =
          H (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom a)
            (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom b)

/-- An `n`-th Hilbert symbol exists at every finite place once `K` contains the `n`-th
roots of unity. Claim recorded ahead of its proof
([Milne 2020, Chap. VIII, §5, pp.245–247][MilneCFT];
[Yamaguchi 2026, `GlobalClassFieldTheory/Reciprocity/GlobalHilbertSymbol/Core.lean:158`]
[Yamaguchi2026]). -/
theorem exists_isFinitePlaceHilbertSymbol (n : ℕ) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ h : Kˣ → Kˣ → Kˣ, IsFinitePlaceHilbertSymbol K n v h := by
  sorry

namespace IsFinitePlaceHilbertSymbol

variable {K}
variable {n : ℕ} {v : HeightOneSpectrum (𝓞 K)} {h : Kˣ → Kˣ → Kˣ}

private theorem units_map_injective :
    Function.Injective
      (Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom : Kˣ → _) :=
  Units.map_injective (algebraMap K (v.adicCompletion K)).injective

/-- The values of a finite-place Hilbert symbol are `n`-th roots of unity
([Milne 2020, Chap. VIII, §5, p.245][MilneCFT]). -/
theorem pow_eq_one [IsMixedCharLocalField (v.adicCompletion K)]
    (hh : IsFinitePlaceHilbertSymbol K n v h) (hn : n ≠ 0) (a b : Kˣ) :
    h a b ^ n = 1 := by
  obtain ⟨H, hH, hcompat⟩ := hh inferInstance
  apply units_map_injective
  rw [map_pow, map_one, hcompat]
  exact hH.pow_eq_one hn _ _

/-- The finite-place symbol is multiplicative in its first slot
([Milne 2020, Chap. VIII, §5, p.246][MilneCFT]). -/
theorem mul_left [IsMixedCharLocalField (v.adicCompletion K)]
    (hh : IsFinitePlaceHilbertSymbol K n v h) (hn : n ≠ 0) (a a' b : Kˣ) :
    h (a * a') b = h a b * h a' b := by
  obtain ⟨H, hH, hcompat⟩ := hh inferInstance
  apply units_map_injective
  rw [map_mul, hcompat, hcompat, hcompat, map_mul]
  exact hH.mul_left hn _ _ _

/-- The finite-place symbol is multiplicative in its second slot
([Milne 2020, Chap. VIII, §5, p.246][MilneCFT]). -/
theorem mul_right [IsMixedCharLocalField (v.adicCompletion K)]
    (hh : IsFinitePlaceHilbertSymbol K n v h) (hn : n ≠ 0) (a b b' : Kˣ) :
    h a (b * b') = h a b * h a b' := by
  obtain ⟨H, hH, hcompat⟩ := hh inferInstance
  apply units_map_injective
  rw [map_mul, hcompat, hcompat, hcompat, map_mul]
  exact hH.mul_right hn _ _ _

/-- The characterization pins the finite-place symbol: two symbols for the same place and
exponent agree. The proof consumes the local `Atlas.Knowledge.IsLocalHilbertSymbol.unique`
and inherits its recorded backlog through the axiom audit
([Milne 2020, Chap. VIII, §5, Rem. 5.9, p.247][MilneCFT]). -/
theorem unique [IsMixedCharLocalField (v.adicCompletion K)] (hn : n ≠ 0)
    {h₁ h₂ : Kˣ → Kˣ → Kˣ} (hh₁ : IsFinitePlaceHilbertSymbol K n v h₁)
    (hh₂ : IsFinitePlaceHilbertSymbol K n v h₂) : h₁ = h₂ := by
  obtain ⟨H₁, hH₁, hcompat₁⟩ := hh₁ inferInstance
  obtain ⟨H₂, hH₂, hcompat₂⟩ := hh₂ inferInstance
  have hH : H₁ = H₂ := IsLocalHilbertSymbol.unique hn hH₁ hH₂
  funext a b
  apply units_map_injective
  rw [hcompat₁, hcompat₂, hH]

end IsFinitePlaceHilbertSymbol

end Atlas.Knowledge
