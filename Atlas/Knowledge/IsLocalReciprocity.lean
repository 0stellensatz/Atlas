import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# local reciprocity

The local reciprocity map of a mixed-characteristic local field, as a characterization:
`IsLocalReciprocity K φ` says the homomorphism `φ : Kˣ → G_K^ab` has dense range, cuts out
the norm subgroup of every finite abelian subextension, and satisfies the arithmetic
Frobenius normalization on roots of unity. These are the properties that classically pin the
Artin map `Art_K` — existence, uniqueness, and the profinite-completion isomorphism
`K̂ˣ ≅ G_K^ab` are the recorded claims. The map itself is not constructed: its construction
is the content of local class field theory, and a definition may not carry a `sorry`; every
consumer of `Art_K` in this layer takes a `φ` with this predicate instead, and uniqueness
makes that unambiguous.

## Main definitions

* `IsLocalReciprocity` — dense range, norm kernels, Frobenius normalization.

## Main statements

* `exists_isLocalReciprocity` — the Artin map exists, recorded ahead of its proof.
* `IsLocalReciprocity.unique` — the three properties pin the map, recorded ahead of its
  proof.
* `IsLocalReciprocity.unitsCompletion_continuousMulEquiv` — the induced isomorphism
  `K̂ˣ ≅ G_K^ab` from Mathlib's profinite completion, recorded ahead of its proof.

## Implementation notes

`G_K^ab` is `Field.absoluteGaloisGroupAbelianization K`, defeq to the
`mStepSolvableQuotient … 1` of `Atlas.Knowledge.AbelianizedGaloisRecovery`; stating over the
algebraic closure is legitimate because `CharZero` makes it Galois. The `normKernel` field
renders "the kernel of `φ` followed by restriction to `L` is the norm subgroup" without
constructing the factored restriction: preimage of the image of the fixing subgroup equals
the range of the unit norm. The `frobenius` field quantifies over every lift `σ` of `φ (u)`
— all lifts agree on abelian subextensions, and the ∀-form keeps the statement free of the
descended map. The completion claim is stated against Mathlib's profinite completion, which
completes against *all* finite-index normal subgroups; its agreement with the topological
completion of the classical statement is the char-0 fact that every finite-index subgroup of
`Kˣ` is open — false in equal characteristic, which is why `IsMixedCharLocalField` is
load-bearing and the read repository, which proves the comparison only under an undischarged
openness hypothesis (`Infinite/AbstractProfiniteCompletionComparison.lean:298`), states its
own completion instead. The `∃ e` shape, rather than a `ProfiniteGrp` bundling, is forced:
the compactness instances do not synthesize through the `absoluteGaloisGroup` definition.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic
  local fields*, J. London Math. Soc. **112** (2025), e70402.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- The **local reciprocity** characterization of a homomorphism
`φ : Kˣ →* G_K^ab`: dense range, norm kernels at every finite abelian level, and the
arithmetic Frobenius normalization. These are the properties that pin the Artin map
([Serre 1979, Chap. XIII, §4, pp.195–198][Serre1979];
[Milne 2020, Chap. I, §1, Thm. 1.1, p.20][MilneCFT];
[Hyeon 2025, §3, p.10][Hyeon2025];
[Yamaguchi 2026, `LocalClassFieldTheory/Infinite/ProfiniteLocalReciprocity.lean:144`]
[Yamaguchi2026]). -/
structure IsLocalReciprocity (φ : Kˣ →* Field.absoluteGaloisGroupAbelianization K) :
    Prop where
  /-- The range is dense: at every finite abelian level the induced map surjects. -/
  denseRange : DenseRange φ
  /-- At every finite abelian subextension `L`, the preimage under `φ` of the image of the
  fixing subgroup of `L` in `G_K^ab` is exactly the norm subgroup `N_{L/K} (Lˣ)`: the induced
  map is `Kˣ / N_{L/K} (Lˣ) ≅ Gal (L/K)`. -/
  normKernel : ∀ (L : IntermediateField K (AlgebraicClosure K)) [FiniteDimensional K L]
    [IsGalois K ↥L], (∀ σ τ : ↥L ≃ₐ[K] ↥L, σ * τ = τ * σ) →
    Subgroup.comap φ
        (Subgroup.map
          (QuotientGroup.mk' (commutator (Field.absoluteGaloisGroup K)).topologicalClosure)
          (IntermediateField.fixingSubgroup L))
      = MonoidHom.range (Units.map (Algebra.norm K (S := ↥L)))
  /-- The arithmetic normalization: every lift of `φ (π)`, `π` a uniformizer, acts on the
  prime-to-`p` roots of unity by `ζ ↦ ζ ^ q`, `q = Nat.card 𝓀[K]` — uniformizer ↦ arithmetic
  Frobenius, read on the maximal unramified subextension. -/
  frobenius : ∀ (u : Kˣ) (hu : (u : K) ∈ 𝒪[K]), Irreducible (⟨(u : K), hu⟩ : 𝒪[K]) →
    ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      (QuotientGroup.mk (σ : Field.absoluteGaloisGroup K) :
        Field.absoluteGaloisGroupAbelianization K) = φ u →
    ∀ m : ℕ, Nat.Coprime m (Nat.card 𝓀[K]) →
    ∀ ζ : AlgebraicClosure K, ζ ^ m = 1 → σ ζ = ζ ^ Nat.card 𝓀[K]

/-- The local reciprocity map exists. Claim recorded ahead of its proof
([Serre 1979, Chap. XIII, §4, pp.195–197][Serre1979];
[Milne 2020, Chap. I, §1, Thm. 1.1, p.20][MilneCFT];
[Yamaguchi 2026, `LocalClassFieldTheory/Infinite/ProfiniteLocalReciprocity.lean:144`]
[Yamaguchi2026]). -/
theorem exists_isLocalReciprocity :
    ∃ φ : Kˣ →* Field.absoluteGaloisGroupAbelianization K, IsLocalReciprocity K φ := by
  sorry

namespace IsLocalReciprocity

variable {K}
variable {φ ψ : Kˣ →* Field.absoluteGaloisGroupAbelianization K}

/-- The characterization pins the map: two homomorphisms satisfying it are equal. Claim
recorded ahead of its proof ([Milne 2020, Chap. I, §1, Thm. 1.1, p.20][MilneCFT]). -/
theorem unique (hφ : IsLocalReciprocity K φ) (hψ : IsLocalReciprocity K ψ) : φ = ψ := by
  sorry

/-- The reciprocity map is an isomorphism after profinite completion:
`K̂ˣ ≅ G_K^ab`, the completion taken against all finite-index normal subgroups — which are
all open, `K` being of mixed characteristic. Claim recorded ahead of its proof
([Serre 1979, Chap. XIII, §4, pp.197–198][Serre1979];
[Hyeon 2025, §3, p.10][Hyeon2025];
[Yamaguchi 2026, `LocalClassFieldTheory/Infinite/ProfiniteLocalReciprocity.lean:257`]
[Yamaguchi2026]). -/
theorem unitsCompletion_continuousMulEquiv (hφ : IsLocalReciprocity K φ) :
    ∃ e : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Kˣ) ≃ₜ*
        Field.absoluteGaloisGroupAbelianization K,
      ∀ u : Kˣ, e (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of Kˣ) u) = φ u := by
  sorry

end IsLocalReciprocity

end Atlas.Knowledge
