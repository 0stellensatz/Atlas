import Mathlib
import Atlas.Knowledge.IsMixedCharLocalField

/-!
# completed unit group of a finite extension

The profinite completion of the multiplicative group of a mixed-characteristic local field,
under a finite extension: the induced map `K-hatˣ → L-hatˣ` is injective, and when the
extension is Galois its image is exactly the fixed points of the Galois action. These are
parts (1) and (3) of the source's Lemma A.3, the input to its proof of the center-freeness
`Atlas.Knowledge.MStepSolvableCenterFree`: by local class field theory the completed unit
group is `G^ab` of the corresponding Galois group, so injectivity and descent here translate
into statements about the tower of `Atlas.Knowledge.MStepSolvableQuotient`s. Part (2), the
injectivity of the transfer map, waits on a profinite Verlagerung and is tracked in the plan's
blocked vocabulary rather than here.

## Main statements

Both are claims recorded ahead of their proofs.

* `unitsCompletion_injective` — the completion of `Units.map (algebraMap K L)` is injective.
  The source's proof splits the completions along `Kˣ ≅ U_K × ℤ` and uses that the
  ramification index is not a zero divisor in `ℤ-hat`.
* `unitsCompletion_fixedPoints` — for a finite Galois extension, the fixed points of the
  Galois action on the completion of `Lˣ` are exactly the image. The source's proof is
  Hilbert's Theorem 90 for `U_L` plus a cokernel chase.

## Implementation notes

The completion is Mathlib's `ProfiniteGrp.ProfiniteCompletion.completion` of the abstract
group `Kˣ`—the source likewise completes the discrete group, so no topology on the field
enters. The source states part (3) for an arbitrary finite extension and reduces at once to
the Galois case, which is the case stated here: without normality the Galois action on `Lˣ`
that the statement quantifies over is not available. Both fields carry the full
mixed-characteristic hypotheses: the claims lean on the local structure of the unit group, not
only on the extension being finite.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

open CategoryTheory

universe u

variable (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsMixedCharLocalField L] [Algebra K L] [FiniteDimensional K L]

/-- The map induced on profinite completions of the multiplicative groups by a finite
extension of mixed-characteristic local fields is injective. Claim recorded ahead of its proof
([Hyeon 2025, Lem. A.3 (1), p.24][Hyeon2025]). -/
theorem unitsCompletion_injective :
    Function.Injective (ProfiniteGrp.profiniteCompletion.map
      (GrpCat.ofHom (Units.map (algebraMap K L : K →* L)))) := by
  sorry

/-- Galois descent for the completed unit group: for a finite Galois extension of
mixed-characteristic local fields, the fixed points of the Galois action on the profinite
completion of `Lˣ` are exactly the image of the profinite completion of `Kˣ`. Claim recorded
ahead of its proof ([Hyeon 2025, Lem. A.3 (3), p.24][Hyeon2025]). -/
theorem unitsCompletion_fixedPoints [IsGalois K L] :
    {x : ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of Lˣ) |
        ∀ σ : L ≃ₐ[K] L, ProfiniteGrp.profiniteCompletion.map
          (GrpCat.ofHom (Units.map ((σ : L ≃+* L) : L →* L))) x = x}
      = Set.range (ProfiniteGrp.profiniteCompletion.map
          (GrpCat.ofHom (Units.map (algebraMap K L : K →* L)))) := by
  sorry

end Atlas.Knowledge
