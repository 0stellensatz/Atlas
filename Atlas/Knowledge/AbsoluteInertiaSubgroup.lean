import Mathlib

/-!
# absolute inertia subgroup

The inertia subgroup `I_K ⊆ Γ_K` of the absolute Galois group of a valued field: the kernel of
the map to the residue Galois group. Mathlib's `ValuationSubring.inertiaSubgroup` covers only
the relative setting—a chosen valuation subring of the top field, inertia inside its
decomposition subgroup—while the source needs the absolute object: one canonical normal
subgroup of `Γ_K`, no choices. The encoding acts on the integral closure `B` of `𝒪[K]` in the
algebraic closure: every `Γ_K`-element restricts to `B` by `galRestrict`, the restriction
descends to the quotient of `B` by its Jacobson radical, and `I_K` is the kernel of that
action. The group-theoreticity of this subgroup is the point of the source's first section and
is recorded separately in `Atlas.Knowledge.AbsoluteInertiaInvariance`.

## Main definitions

* `absoluteResidueHom` — the action of `Γ_K` on the integral closure of `𝒪[K]` in the
  algebraic closure, reduced modulo the Jacobson radical: the map to the residue Galois group.
  `galResidueHom` is the same map before the definitional passage from the Galois group of the
  algebraic closure to `Field.absoluteGaloisGroup`.
* `absoluteInertiaSubgroup` — `I_K`, its kernel, normal by construction.

## Main statements

* `mem_absoluteInertiaSubgroup_iff` — membership unwound: `g ∈ I_K` iff `g` moves every
  integral element by an element of the radical.

## Implementation notes

Quotienting by the Jacobson radical is what makes the target canonical without any theorem:
the radical needs no choice of prime and is preserved by every ring automorphism. For `K` a
nonarchimedean local field, `𝒪[K]` is henselian, so `B` is local with the radical as its
maximal ideal and `B ⧸ rad` an algebraic closure of `𝓀[K]`—under that identification
`absoluteResidueHom` is the classical surjection `Γ_K → Gal (𝓀̄/𝓀)` and the kernel is the
classical inertia. Those identifications are facts about the encoding, for the layer to record
when the henselian development enters it; the kernel itself does not wait for them.

## References

* [Mochizuki1997] S. Mochizuki, *A version of the Grothendieck conjecture for p-adic local
  fields*, Int. J. Math. **8** (1997), 499–506.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K]

set_option maxHeartbeats 800000 in
-- The two structure proofs push `simp` through the quotient of the integral closure, whose
-- ring structure sits under a tower of subalgebra instances; the default budget elaborates
-- `map_one'` and runs out inside `map_mul'`.
/-- The residue action before the passage to `Field.absoluteGaloisGroup`: an automorphism of
the algebraic closure over `K` restricts to the integral closure of `𝒪[K]` by `galRestrict`
and descends to the quotient by the Jacobson radical, which every ring automorphism preserves
([Mochizuki 1997, Cor. 1.3, p.501][Mochizuki1997]). -/
noncomputable def galResidueHom :
    (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K) →*
      RingAut (integralClosure 𝒪[K] (AlgebraicClosure K) ⧸
        Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] (AlgebraicClosure K)))) where
  toFun g :=
    Ideal.quotientEquiv _ _
      (galRestrict 𝒪[K] K (AlgebraicClosure K)
        (integralClosure 𝒪[K] (AlgebraicClosure K)) g).toRingEquiv
      (by
        have hbij : Function.Bijective
            ⇑((galRestrict 𝒪[K] K (AlgebraicClosure K)
                (integralClosure 𝒪[K] (AlgebraicClosure K)) g).toRingEquiv :
              integralClosure 𝒪[K] (AlgebraicClosure K) →+*
                integralClosure 𝒪[K] (AlgebraicClosure K)) :=
          (galRestrict 𝒪[K] K (AlgebraicClosure K)
            (integralClosure 𝒪[K] (AlgebraicClosure K)) g).bijective
        rw [Ideal.map_jacobson_of_bijective hbij, Ideal.map_bot])
  map_one' := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [Ideal.quotientEquiv]
  map_mul' g h := by
    ext x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [Ideal.quotientEquiv]

/-- The map from `Γ_K` to the residue Galois group: the action on the integral closure of
`𝒪[K]` in the algebraic closure, reduced modulo the Jacobson radical. The first factor is the
definitional identity of `Field.absoluteGaloisGroup K` with the Galois group of the algebraic
closure ([Mochizuki 1997, Cor. 1.3, p.501][Mochizuki1997]). -/
noncomputable def absoluteResidueHom :
    Field.absoluteGaloisGroup K →*
      RingAut (integralClosure 𝒪[K] (AlgebraicClosure K) ⧸
        Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] (AlgebraicClosure K)))) :=
  (galResidueHom K).comp ⟨⟨fun g => g, rfl⟩, fun _ _ => rfl⟩

@[simp]
theorem absoluteResidueHom_apply_mk (g : Field.absoluteGaloisGroup K)
    (x : integralClosure 𝒪[K] (AlgebraicClosure K)) :
    absoluteResidueHom K g (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _
        (galRestrict 𝒪[K] K (AlgebraicClosure K)
          (integralClosure 𝒪[K] (AlgebraicClosure K)) g x) := by
  simp [absoluteResidueHom, galResidueHom, Ideal.quotientEquiv]

/-- The **absolute inertia subgroup** `I_K ⊆ Γ_K` of a valued field: the kernel of the map to
the residue Galois group, normal by construction
([Mochizuki 1997, Cor. 1.3, p.501][Mochizuki1997]). -/
noncomputable def absoluteInertiaSubgroup : Subgroup (Field.absoluteGaloisGroup K) :=
  (absoluteResidueHom K).ker

instance : (absoluteInertiaSubgroup K).Normal :=
  inferInstanceAs ((absoluteResidueHom K).ker.Normal)

/-- Membership in the absolute inertia subgroup, unwound to the integral elements: `g ∈ I_K`
iff `g` moves every element of the integral closure by an element of the Jacobson radical
([Mochizuki 1997, Cor. 1.3, p.501][Mochizuki1997]). -/
theorem mem_absoluteInertiaSubgroup_iff {g : Field.absoluteGaloisGroup K} :
    g ∈ absoluteInertiaSubgroup K ↔
      ∀ x : integralClosure 𝒪[K] (AlgebraicClosure K),
        galRestrict 𝒪[K] K (AlgebraicClosure K)
              (integralClosure 𝒪[K] (AlgebraicClosure K)) g x - x ∈
          Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] (AlgebraicClosure K))) := by
  constructor
  · intro h x
    have hg : absoluteResidueHom K g = 1 := h
    have h1 : absoluteResidueHom K g (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := by
      rw [hg]
      rfl
    rw [absoluteResidueHom_apply_mk] at h1
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp h1
  · intro h
    have hg : absoluteResidueHom K g = 1 := by
      ext x
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [absoluteResidueHom_apply_mk]
      exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (h y)
    exact hg

end Atlas.Knowledge
