import Mathlib
import Atlas.Knowledge.TransferComp
import Atlas.Knowledge.TransferNaturality

/-!
# abelianized transfer through an injection

Transfer into an injectively presented subgroup is independent of the group presentations.
This packages the finite-group comparison used by the Galois transfer square.

## Main definitions

* `abelianizedTransferOfInjective` — transfer into the domain of an injective homomorphism.

## Main statements

* `abelianizedTransferOfInjective_natural` — compatible group equivalences preserve transfer.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

variable {G H G' H' : Type*} [Group G] [Group H] [Group G'] [Group H']

/-- Transfer into an injectively presented subgroup, descended to abelianizations
([Yamaguchi 2026, `MainTransfer.lean:172`][Yamaguchi2026]). -/
def abelianizedTransferOfInjective [Finite G] (i : H →* G) (hi : Function.Injective i) :
    Abelianization G →* Abelianization H :=
  letI : i.range.FiniteIndex := Subgroup.finiteIndex_of_finite
  Abelianization.lift (MonoidHom.transfer
    (Abelianization.of.comp (MonoidHom.ofInjective hi).symm.toMonoidHom))

/-- The transferred inverse identification can equivalently be applied after transfer. -/
theorem abelianizedTransferOfInjective_eq [Finite G]
    (i : H →* G) (hi : Function.Injective i) :
    letI : i.range.FiniteIndex := Subgroup.finiteIndex_of_finite
    abelianizedTransferOfInjective i hi =
      (MonoidHom.ofInjective hi).symm.abelianizationCongr.toMonoidHom.comp
        (Abelianization.lift (MonoidHom.transfer
          (Abelianization.of : i.range →* Abelianization i.range))) := by
  letI : i.range.FiniteIndex := Subgroup.finiteIndex_of_finite
  apply Abelianization.hom_ext
  apply MonoidHom.ext
  intro g
  simp only [MonoidHom.comp_apply, abelianizedTransferOfInjective, Abelianization.lift_apply_of]
  have h : Abelianization.of.comp (MonoidHom.ofInjective hi).symm.toMonoidHom =
      (MonoidHom.ofInjective hi).symm.abelianizationCongr.toMonoidHom.comp
        (Abelianization.of : i.range →* Abelianization i.range) := by
    ext a
    rfl
  rw [h, transfer_comp]
  rfl

/-- Compatible equivalences of an ambient group and its injected subgroup preserve transfer
([Yamaguchi 2026, `TransferNaturality.lean:216`][Yamaguchi2026]). -/
theorem abelianizedTransferOfInjective_natural [Finite G] [Finite G']
    (i : H →* G) (hi : Function.Injective i) (j : H' →* G') (hj : Function.Injective j)
    (e : G ≃* G') (d : H ≃* H') (hcomm : ∀ h, e (i h) = j (d h))
    (a : Abelianization G) :
    abelianizedTransferOfInjective j hj (e.abelianizationCongr a) =
      d.abelianizationCongr (abelianizedTransferOfInjective i hi a) := by
  letI : i.range.FiniteIndex := Subgroup.finiteIndex_of_finite
  letI : j.range.FiniteIndex := Subgroup.finiteIndex_of_finite
  letI : (i.range.map e.toMonoidHom).FiniteIndex := Subgroup.finiteIndex_of_finite
  have hmap : i.range.map e.toMonoidHom = j.range := by
    ext b
    constructor
    · rintro ⟨g, ⟨h, rfl⟩, rfl⟩
      exact ⟨d h, (hcomm h).symm⟩
    · rintro ⟨h, rfl⟩
      exact ⟨i (d.symm h), ⟨d.symm h, rfl⟩,
        (hcomm (d.symm h)).trans (congrArg j (d.apply_symm_apply h))⟩
  have hker : e.toMonoidHom.ker ≤ i.range := by
    intro g hg
    have hg1 : g = 1 := e.injective (hg.trans e.map_one.symm)
    rw [hg1]
    exact i.range.one_mem
  let c := MulEquiv.subgroupCongr hmap
  let ei := MonoidHom.ofInjective hi
  let ej := MonoidHom.ofInjective hj
  have hbridge : ej.symm.toMonoidHom.comp
      (c.toMonoidHom.comp (e.toMonoidHom.subgroupMap i.range)) =
      d.toMonoidHom.comp ei.symm.toMonoidHom := by
    ext g
    apply hj
    have heig : i (ei.symm g) = g.1 := congrArg Subtype.val (ei.apply_symm_apply g)
    change j (ej.symm (c ((e.toMonoidHom.subgroupMap i.range) g))) = j (d (ei.symm g))
    rw [← hcomm, heig]
    exact congrArg Subtype.val (ej.apply_symm_apply _)
  have hn := DFunLike.congr_fun
    (abelianization_transfer_natural_of_surjective e.toMonoidHom e.surjective i.range hker) a
  simp only [MonoidHom.comp_apply] at hn
  change Abelianization.map (e.toMonoidHom.subgroupMap i.range) _ =
    (Abelianization.lift (MonoidHom.transfer
      (Abelianization.of : i.range.map e.toMonoidHom →* _))) (e.abelianizationCongr a) at hn
  have hc := DFunLike.congr_fun
    (abelianization_transfer_congr_subgroup (i.range.map e.toMonoidHom) j.range hmap)
      (e.abelianizationCongr a)
  rw [abelianizedTransferOfInjective_eq, abelianizedTransferOfInjective_eq]
  change ej.symm.abelianizationCongr _ = d.abelianizationCongr (ei.symm.abelianizationCongr _)
  rw [← hc]
  change ej.symm.abelianizationCongr (c.abelianizationCongr _) = _
  rw [← hn]
  have hb (b : Abelianization i.range) :
      ej.symm.abelianizationCongr (c.abelianizationCongr
        (Abelianization.map (e.toMonoidHom.subgroupMap i.range) b)) =
      d.abelianizationCongr (ei.symm.abelianizationCongr b) := by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective b
    exact congrArg Abelianization.of (DFunLike.congr_fun hbridge g)
  exact hb _

end

end Atlas.Knowledge
