import Mathlib
import Atlas.Knowledge.IsLocalReciprocity
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.IsProfiniteTransfer

/-!
# profinite-transfer naturality of the Artin map

The class-field-theory square at the absolute level: for a finite extension `L/K` of
mixed-characteristic local fields, the profinite transfer out of `G_K^ab` intertwines the
reciprocity maps of the two fields with the inclusion `Kˣ → Lˣ`—`Ver ∘ Art_K = Art_L ∘ ι`, the
right side read inside the subgroup of `G_K` fixing `L` pointwise. This is the absolute ascent
of the finite-level square of `Atlas.Knowledge.AbelianizedGaloisTransfer`, and it is the
mechanism of the source's proof that the transfer of absolute Galois groups is injective—the
deliberately unstated gate of `Atlas.Knowledge.CompletedUnitGroup`—by reducing that injectivity
to the injectivity of the completed inclusion of unit groups.

## Main definitions

* `ArtinMapProfiniteTransferNaturality.fixingSubgroup` — the subgroup of `G_K` fixing `L`.
* `ArtinMapProfiniteTransferNaturality.conj` — conjugation by a choice of `L`-isomorphism of
  algebraic closures, realizing `G_L` inside that subgroup.

## Main statements

* `artinMap_profiniteTransfer_naturality` — the square, recorded ahead of its proof.

## Implementation notes

The two absolute Galois groups live over different algebraic closures, and the identification
of `Field.absoluteGaloisGroup L` with the fixing subgroup is by conjugation with an
`L`-isomorphism `ψ` of the closures—one exists because `L` is finite over `K`, so the closure
of `K` is also one of `L`, but none is canonical. The square therefore quantifies over every
`ψ`: two choices differ by an inner automorphism of the fixing subgroup, which the
abelianization does not see, so no choice is privileged and the ∀-form is the honest statement.
It likewise quantifies over every representative `τ` of `Art_L (ι x)`, the ∀-lift device of
`Atlas.Knowledge.IsArtinRestriction`; that all lifts land equally—`conj` is a homeomorphism
onto the fixing subgroup carrying the closed commutator subgroup into the closed commutator
subgroup—is the claim's business, not the statement's. The reciprocity maps of the two floors
enter through `Atlas.Knowledge.IsLocalReciprocity`, each over its own local-field structure
with `[ValuativeExtension K L]` tying the two, and the transfer enters as any `V` satisfying
`Atlas.Knowledge.IsProfiniteTransfer`, unambiguous by that file's uniqueness theorem. The source
states the square on the profinite completions; the form here is its restriction to `Kˣ`,
which is dense, so nothing is lost. The fixing subgroup is the abstract-extension counterpart
of the intermediate-field dictionary of `Atlas.Knowledge.AbsoluteGaloisSubextension`.

## References

* [MilneFT] J. S. Milne, *Fields and Galois theory* (v5.10), available at www.jmilne.org/math/,
  2022.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

open ValuativeRel

namespace Atlas.Knowledge

namespace ArtinMapProfiniteTransferNaturality

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  [Algebra L (AlgebraicClosure K)] [IsScalarTower K L (AlgebraicClosure K)]

/-- The subgroup of the absolute Galois group of `K` fixing `L` pointwise: the fixing subgroup
of the range of `L` in the algebraic closure of `K`. -/
noncomputable def fixingSubgroup : Subgroup (Field.absoluteGaloisGroup K) :=
  (IsScalarTower.toAlgHom K L (AlgebraicClosure K)).fieldRange.fixingSubgroup

/-- Conjugation by a choice `ψ` of `L`-isomorphism of algebraic closures realizes the absolute
Galois group of `L` inside the subgroup of `G_K` fixing `L`—the identification of the fixing
subgroup with the Galois group of the subextension
([Milne 2022, Chap. 7, Prop. 7.12, p.97][MilneFT] for the fixing-subgroup dictionary when the
closure is Galois over the base; the general case and the transport across the two closures
are the standard argument, per the implementation notes of
`Atlas.Knowledge.AbsoluteGaloisSubextension`). -/
noncomputable def conj (ψ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure K) :
    Field.absoluteGaloisGroup L →* ↥(fixingSubgroup K L) :=
  MonoidHom.codRestrict
    ((AlgEquiv.restrictScalarsHom K).comp (AlgEquiv.autCongr ψ).toMonoidHom)
    _ (fun τ => by
      rintro ⟨y, x, rfl⟩
      change (AlgEquiv.restrictScalars K (AlgEquiv.autCongr ψ τ))
        (IsScalarTower.toAlgHom K L (AlgebraicClosure K) x) = _
      simp [AlgEquiv.autCongr, IsScalarTower.toAlgHom_apply])

end ArtinMapProfiniteTransferNaturality

open ArtinMapProfiniteTransferNaturality in
/-- The **transfer square** of local class field theory at the absolute level: for a finite
extension `L/K` of mixed-characteristic local fields, reciprocity maps of the two fields
intertwine the profinite transfer with the inclusion `Kˣ → Lˣ`—`Ver (Art_K x)` is the class in
the abelianized fixing subgroup of any representative of `Art_L (ι x)`, conjugated in by any
`L`-isomorphism of the closures. Claim recorded ahead of its proof
([Hyeon 2025, Lem. A.3 proof, p.25][Hyeon2025], the square of the completions, restricted here
to the dense `Kˣ`). -/
theorem artinMap_profiniteTransfer_naturality (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsMixedCharLocalField K] (L : Type*) [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsMixedCharLocalField L] [Algebra K L] [FiniteDimensional K L]
    [ValuativeExtension K L] [Algebra L (AlgebraicClosure K)]
    [IsScalarTower K L (AlgebraicClosure K)]
    (artK : Kˣ →* Field.absoluteGaloisGroupAbelianization K) (hK : IsLocalReciprocity K artK)
    (artL : Lˣ →* Field.absoluteGaloisGroupAbelianization L) (hL : IsLocalReciprocity L artL)
    (V : Field.absoluteGaloisGroupAbelianization K →*
      TopologicalAbelianization ↥(fixingSubgroup K L))
    (hV : IsProfiniteTransfer (Field.absoluteGaloisGroup K) (fixingSubgroup K L) V)
    (ψ : AlgebraicClosure L ≃ₐ[L] AlgebraicClosure K) (x : Kˣ)
    (τ : Field.absoluteGaloisGroup L)
    (hτ : (QuotientGroup.mk τ : Field.absoluteGaloisGroupAbelianization L)
      = artL (Units.map (algebraMap K L : K →* L) x)) :
    V (artK x) = QuotientGroup.mk (conj K L ψ τ) := by
  sorry

end Atlas.Knowledge
