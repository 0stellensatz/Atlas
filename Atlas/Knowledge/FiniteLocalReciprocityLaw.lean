import Mathlib
import Atlas.Knowledge.ConcreteReciprocityTransport
import Atlas.Knowledge.LocalClassFieldAxiom
import Atlas.Knowledge.LocalHenselianValuation
import Atlas.Knowledge.LocalResidueDatum
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.UnitCohomologyDischarge

/-!
# finite local reciprocity law

**The Local Reciprocity Law, finite form**: for every finite Galois
extension `L/K` of a mixed-characteristic local field, reciprocity
gives the canonical isomorphism `G(L/K)ᵃᵇ ≃* Kˣ/N_{L/K}(Lˣ)`, and the
local norm-residue symbol `Kˣ →* G(L/K)ᵃᵇ` it inverts is surjective
with kernel exactly the norm subgroup. Every input is supplied by the
layer — the residue degree datum, the Henselian valuation, the
class-field axiom, and the unit-cohomology discharge — and no
hypothesis is threaded (#104).

## Main definitions

* `abelianizationEquivNormQuotient` — the reciprocity isomorphism.
* `localArtinMonoidHom` — the local norm-residue symbol.

## Main statements

* `localArtinMonoidHom_surjective` — the symbol is onto; proved.
* `localArtinMonoidHom_ker` — its kernel is the norm subgroup; proved.

## Implementation notes

The isomorphism inserts the four local inputs into the transported
reciprocity equivalence at the algebraic-closure ambient — the layer's
arc convention, where the source works over its separable closure with
the same statements — and therefore through the generalized
`OfEmbedding` form with `IsAlgClosed.lift`, since the chosen-embedding
form stays pinned to the separable closure; the class-field axiom
enters in its purpose-built algebraic-closure form. The source's
embedding-independence pair (`Main.lean:41` and `:66`) is not ported:
it routes through the skipped `ConcreteReciprocityCanonical.lean`,
whose fixed ambient makes the arc's single chosen embedding canonical
by construction. The threaded unit-cohomology hypothesis of the
transport is discharged here by
`Atlas.Knowledge.localHenselianValuation_satisfiesUnramifiedUnitCohomology`,
so no reciprocity statement in this file carries it.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]
  [FiniteDimensional K L] [IsGalois K L]

/-- **Finite local reciprocity (the Local Reciprocity Law)**: for a
finite Galois extension of a mixed-characteristic local field,
reciprocity gives the canonical isomorphism `G(L/K)ᵃᵇ ≃ Kˣ/N_{L/K}(Lˣ)`
([Serre 1979, Chap. XIII, §4, pp.195–197][Serre1979]; the source
counterpart over its separable closure is [Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Main.lean:32`]
[Yamaguchi2026]). -/
noncomputable def abelianizationEquivNormQuotient :
    Abelianization (L ≃ₐ[K] L) ≃* NormQuotient K L :=
  concreteReciprocityEquivOfEmbedding K L (AlgebraicClosure K)
    IsAlgClosed.lift
    (localResidueDatum K) (localHenselianValuation K)
    (algebraicClosureUnits_satisfiesClassFieldAxiom K)
    (localHenselianValuation_satisfiesUnramifiedUnitCohomology K)

/-- **The local norm-residue symbol**: the inverse of reciprocity,
preceded by the quotient map from `Kˣ`
([Serre 1979, Chap. XIII, §4, pp.195–197][Serre1979]; the source
counterpart is [Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Main.lean:57`]
[Yamaguchi2026]). -/
noncomputable def localArtinMonoidHom :
    Kˣ →* Abelianization (L ≃ₐ[K] L) :=
  (abelianizationEquivNormQuotient K L).symm.toMonoidHom.comp
    (normClass K L)

/-- The local norm-residue symbol is surjective
([Serre 1979, Chap. XIII, §4, pp.195–197][Serre1979]; [Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Main.lean:85`]
[Yamaguchi2026]). -/
theorem localArtinMonoidHom_surjective :
    Function.Surjective (localArtinMonoidHom K L) :=
  (abelianizationEquivNormQuotient K L).symm.surjective.comp
    (QuotientGroup.mk'_surjective (localNormSubgroup K L))

/-- **The kernel of the local norm-residue symbol is exactly the norm
subgroup** `N_{L/K}(Lˣ)`
([Serre 1979, Chap. XIII, §4, pp.195–197][Serre1979]; [Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/Main.lean:92`]
[Yamaguchi2026]). -/
theorem localArtinMonoidHom_ker :
    (localArtinMonoidHom K L).ker = localNormSubgroup K L := by
  ext x
  rw [MonoidHom.mem_ker]
  change
    (abelianizationEquivNormQuotient K L).symm
        (normClass K L x) = 1 ↔
      x ∈ localNormSubgroup K L
  constructor
  · intro hx
    have hx' := congrArg (abelianizationEquivNormQuotient K L) hx
    rw [(abelianizationEquivNormQuotient K L).apply_symm_apply,
      map_one] at hx'
    exact (normClass_eq_one_iff_mem K L x).mp hx'
  · intro hx
    have hq : normClass K L x = 1 :=
      (normClass_eq_one_iff_mem K L x).2 hx
    rw [hq, map_one]

end

end Atlas.Knowledge
