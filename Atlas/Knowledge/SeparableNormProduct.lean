import Mathlib

/-!
# separable field norms as products of embeddings

For a finite separable extension, the field norm becomes the product
over all base-field embeddings after mapping into a separably closed
ambient field — which need not be a normal extension of the base
field, so the formula serves imperfect ground fields where Mathlib's
algebraically closed product formula does not apply (#104).

## Main statements

* `algebraMap_norm_eq_prod_embeddings_of_isSepClosed` — the mapped
  norm is the product of all embeddings; proved.

## Implementation notes

The source's file-local `Fintype` instance on the embedding space is
dropped: the layer's Mathlib provides the instance ambiently, and a
local instance would bake a different `Finset.univ` into these
statements than their consumers elaborate with. The declarations are
universe-polymorphic where the source pins `Type`,
because the layer's `Atlas.Knowledge.SeparableFixedFieldNorm` consumer
is itself polymorphic. Everything else ports token-for-token; the file
is the source's `LocalReciprocity/SeparableNormProduct.lean` whole.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v w

/-- The embeddings of a finite separable tower above a power-basis
generator split into embeddings of the lower field and their
extensions ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableNormProduct.lean:28`]
[Yamaguchi2026]). -/
theorem prod_embeddings_algebraMap_powerBasisGen_eq
    (k : Type u) (Ω : Type v) [Field k] [Field Ω] [Algebra k Ω]
    [IsSepClosed Ω]
    {L E : Type w} [Field L] [Field E]
    [Algebra k L] [Algebra k E] [Algebra L E] [IsScalarTower k L E]
    [FiniteDimensional k L] [Algebra.IsSeparable k L]
    [Algebra.IsSeparable k E] [FiniteDimensional k E]
    (pb : PowerBasis k L) :
    ∏ σ : E →ₐ[k] Ω, σ (algebraMap L E pb.gen) =
      ((@Finset.univ (L →ₐ[k] Ω) (PowerBasis.AlgHom.fintype pb)).prod
        (fun σ => σ pb.gen)) ^ Module.finrank L E := by
  haveI : FiniteDimensional L E := FiniteDimensional.right k L E
  haveI : Algebra.IsSeparable L E :=
    Algebra.isSeparable_tower_top_of_isSeparable k L E
  letI : Fintype (L →ₐ[k] Ω) := PowerBasis.AlgHom.fintype pb
  rw [Fintype.prod_equiv algHomEquivSigma
    (fun σ : E →ₐ[k] Ω => σ (algebraMap L E pb.gen))
    (fun σ => σ.1 pb.gen)]
  · rw [← Finset.univ_sigma_univ, Finset.prod_sigma, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun σ _ => ?_
    letI : Algebra L Ω := σ.toRingHom.toAlgebra
    simp_rw [Finset.prod_const]
    congr
    rw [Finset.card_univ, Fintype.card_eq_nat_card]
    exact AlgHom.natCard_of_splits L E Ω (fun x =>
      IsSepClosed.splits_codomain _ (Algebra.IsSeparable.isSeparable L x))
  · intro σ
    simp only [algHomEquivSigma, Equiv.coe_fn_mk,
      AlgHom.restrictDomain, AlgHom.comp_apply,
      IsScalarTower.coe_toAlgHom']

/-- **Mapping the norm of an element of a finite separable extension
into a separably closed field gives the product of all base-field
embeddings** ([Yamaguchi 2026,
`LocalClassFieldTheory/Finite/LocalReciprocity/SeparableNormProduct.lean:60`]
[Yamaguchi2026]). -/
theorem algebraMap_norm_eq_prod_embeddings_of_isSepClosed
    (k : Type u) (Ω : Type v) (E : Type w) [Field k] [Field Ω] [Field E]
    [Algebra k Ω] [IsSepClosed Ω] [Algebra k E]
    [FiniteDimensional k E] [Algebra.IsSeparable k E]
    (x : E) :
    algebraMap k Ω (Algebra.norm k x) = ∏ σ : E →ₐ[k] Ω, σ x := by
  have hx := Algebra.IsSeparable.isIntegral k x
  letI : Algebra.IsSeparable k
      (IntermediateField.adjoin k ({x} : Set E)) :=
    Algebra.isSeparable_tower_bot_of_isSeparable k
      (IntermediateField.adjoin k ({x} : Set E)) E
  rw [Algebra.norm_eq_norm_adjoin k x, map_pow,
    ← IntermediateField.adjoin.powerBasis_gen hx,
    Algebra.norm_eq_prod_embeddings_gen Ω
      (IntermediateField.adjoin.powerBasis hx)
      (IsSepClosed.splits_codomain _
        (Algebra.IsSeparable.isSeparable k
          (IntermediateField.adjoin.powerBasis hx).gen))]
  · simpa only [IntermediateField.adjoin.powerBasis_gen,
      IntermediateField.AdjoinSimple.algebraMap_gen] using
      (prod_embeddings_algebraMap_powerBasisGen_eq
        (L := IntermediateField.adjoin k ({x} : Set E)) (E := E)
        k Ω (IntermediateField.adjoin.powerBasis hx)).symm
  · exact Algebra.IsSeparable.isSeparable k _

end

end Atlas.Knowledge
