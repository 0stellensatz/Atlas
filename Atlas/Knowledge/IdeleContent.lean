import Mathlib
import Atlas.Knowledge.IdeleClassGroup

/-!
# idele content

The content of an idele: the product of the normalized absolute values of all its
coordinates — archimedean blocks with their multiplicities, finite coordinates as a
`finprod` that the restriction condition keeps finitely supported. This is Milne's
`c (a) = ∏ |a_v|_v`, and the normalization is chosen so that Mathlib's product formula
`NumberField.prod_abs_eq_one` *is* the statement that principal ideles have content one —
proved here, no inversion anywhere. The content then descends to the idele class group, and
its kernel there is the norm-one idele class group, the subgroup Fujisaki's theorem is
about.

## Main definitions

* `ideleContent` — `𝕀_K →* ℝ≥0ˣ`.
* `ideleClassContent` — the descent to `C_K`, through the proved product formula.
* `normOneIdeleClassGroup` — `C_K¹`, the kernel of the descended content.

## Main statements

* `ideleContent_principalIdele` — the product formula: principal ideles have content one;
  proved via `NumberField.prod_abs_eq_one`.

## Implementation notes

The finite part multiplies `‖·‖₊` of the coordinates over a `finprod`: coordinates are
integral units at cofinitely many places, and integral units have norm one, so the support
is finite — that one lemma is the whole restricted-product bookkeeping. The archimedean part
is a finite product of coordinate norms raised to the place multiplicities, matching the
`w x ^ w.mult` factors of the product formula. The source repository's `absoluteNorm`
(`AlgebraicNumberTheory/Idele/NormCore.lean:94`) uses ideal-norm factors — a uniformizer at
`v` contributes `absNorm v.asIdeal > 1` — and is the **inverse** of the content map defined
here; its route also passes through a repo-local fractional-ideal apparatus that the
`finprod` route makes unnecessary. Atlas states the literature's map; a port of the source's
norm statements into this vocabulary composes with inversion, factor by factor.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField RestrictedProduct NNReal
open NumberField IsDedekindDomain

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- The norm of a unit of a normed field, as a unit of `ℝ≥0`. -/
private def nnnormUnits {F : Type*} [NormedField F] : Fˣ →* ℝ≥0ˣ :=
  Units.map (nnnormHom : F →*₀ ℝ≥0).toMonoidHom

@[simp]
private theorem nnnormUnits_val {F : Type*} [NormedField F] (u : Fˣ) :
    ((nnnormUnits u : ℝ≥0ˣ) : ℝ≥0) = ‖(u : F)‖₊ := rfl

variable {K} in
/-- Local units at a finite place have norm one. -/
private theorem nnnormUnits_eq_one {v : HeightOneSpectrum (𝓞 K)}
    {u : (v.adicCompletion K)ˣ}
    (hu : u ∈ (v.adicCompletionIntegers K).units) :
    nnnormUnits u = 1 := by
  have h1 : Valued.v (u : v.adicCompletion K) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu
  have hnorm := FinitePlace.norm_def (K := K) (v := v) (u : v.adicCompletion K)
  rw [h1, map_one] at hnorm
  apply Units.ext
  apply NNReal.coe_injective
  simpa using hnorm

variable {K} in
private theorem mulSupport_nnnormUnits_finite
    (a : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (v.adicCompletionIntegers K).units]) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 K) =>
      nnnormUnits (a v)).Finite := by
  refine Set.Finite.subset (Filter.eventually_cofinite.mp a.2) ?_
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  exact fun hmem => hv (nnnormUnits_eq_one hmem)

/-- The finite part of the content. -/
private noncomputable def finiteContent :
    (Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (v.adicCompletionIntegers K).units]) →* ℝ≥0ˣ where
  toFun a := ∏ᶠ v, nnnormUnits (a v)
  map_one' := finprod_eq_one_of_forall_eq_one fun v => by simp [nnnormUnits]
  map_mul' a b := by
    rw [← finprod_mul_distrib (mulSupport_nnnormUnits_finite a)
      (mulSupport_nnnormUnits_finite b)]
    exact finprod_congr fun v => by simp [nnnormUnits]

variable {K} in
private theorem finiteContent_apply
    (a : Πʳ v : HeightOneSpectrum (𝓞 K),
      [(v.adicCompletion K)ˣ, (v.adicCompletionIntegers K).units]) :
    finiteContent K a = ∏ᶠ v, nnnormUnits (a v) := rfl

/-- Evaluation of an infinite adele at an archimedean place, as a ring hom. -/
private noncomputable def infiniteEval (w : InfinitePlace K) :
    InfiniteAdeleRing K →+* w.Completion :=
  Pi.evalRingHom (fun v : InfinitePlace K => v.Completion) w

/-- The archimedean part of the content: complex places count twice. -/
private noncomputable def infiniteContent : (InfiniteAdeleRing K)ˣ →* ℝ≥0ˣ :=
  ∏ w : InfinitePlace K,
    (powMonoidHom w.mult).comp
      (nnnormUnits.comp (Units.map (infiniteEval K w).toMonoidHom))

variable {K} in
private theorem infiniteContent_apply (a : (InfiniteAdeleRing K)ˣ) :
    infiniteContent K a =
      ∏ w : InfinitePlace K,
        nnnormUnits (Units.map (infiniteEval K w).toMonoidHom a) ^ w.mult := by
  simp [infiniteContent]

/-- The **content** of an idele: the product of the normalized absolute values of all its
coordinates, `c (a) = ∏ |a_v|_v`
([Milne 2020, Chap. V, §4, 4.4, p.171][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/NormCore.lean:94`, inverse and ideal-norm
factors][Yamaguchi2026]). -/
noncomputable def ideleContent : IdeleGroup K →* ℝ≥0ˣ :=
  ((infiniteContent K).comp (MonoidHom.fst _ _)) *
    ((finiteContent K).comp (MonoidHom.snd _ _))

/-- The forgetful map `ℝ≥0ˣ →* ℝ`. -/
private def unitsVal : ℝ≥0ˣ →* ℝ :=
  NNReal.toRealHom.toMonoidHom.comp (Units.coeHom ℝ≥0)

private theorem unitsVal_injective : Function.Injective unitsVal := fun _ _ h =>
  Units.ext (NNReal.coe_injective h)

/-- **The product formula**: principal ideles have content one. Proved through Mathlib's
`NumberField.prod_abs_eq_one` — the normalization of `ideleContent` is chosen to make this
literal ([Milne 2020, Chap. V, §4, 4.4, p.171][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/PrincipalNorm.lean:228`][Yamaguchi2026]). -/
theorem ideleContent_principalIdele (x : Kˣ) :
    ideleContent K (principalIdele K x) = 1 := by
  have hx : (x : K) ≠ 0 := Units.ne_zero x
  apply unitsVal_injective
  rw [map_one]
  rw [show ideleContent K (principalIdele K x) =
      infiniteContent K (principalIdele K x).1 *
        finiteContent K (principalIdele K x).2 from rfl]
  rw [map_mul]
  have hinf : unitsVal (infiniteContent K (principalIdele K x).1) =
      ∏ w : InfinitePlace K, w (x : K) ^ w.mult := by
    rw [infiniteContent_apply, map_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_pow]
    congr 1
    change ‖((x : K) : w.Completion)‖ = w (x : K)
    simpa using InfinitePlace.Completion.norm_coe w (WithAbs.toAbs w.1 (x : K))
  have hfin : unitsVal (finiteContent K (principalIdele K x).2) =
      ∏ᶠ w : FinitePlace K, w (x : K) := by
    rw [finiteContent_apply,
      MonoidHom.map_finprod_of_injective unitsVal unitsVal_injective]
    rw [show (fun v : HeightOneSpectrum (𝓞 K) =>
        unitsVal (nnnormUnits ((principalIdele K x).2 v))) =
        fun v : HeightOneSpectrum (𝓞 K) =>
          ‖FinitePlace.embedding v (x : K)‖ from rfl]
    simp only [← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm,
      FinitePlace.equivHeightOneSpectrum_symm_apply]
  rw [hinf, hfin]
  exact NumberField.prod_abs_eq_one hx

/-- The content descended to the idele class group: well defined exactly by the product
formula ([Milne 2020, Chap. V, §4, 4.4, p.171][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/PrincipalNorm.lean:260`][Yamaguchi2026]). -/
noncomputable def ideleClassContent : IdeleClassGroup K →* ℝ≥0ˣ :=
  QuotientGroup.lift (principalIdeleSubgroup K) (ideleContent K) (by
    rintro a ⟨x, rfl⟩
    exact MonoidHom.mem_ker.mpr (ideleContent_principalIdele K x))

/-- The **norm-one idele class group** `C_K¹`: the kernel of the descended content — the
subgroup whose compactness is Fujisaki's theorem
([Milne 2020, Chap. V, §4, 4.4, p.171][MilneCFT];
[Yamaguchi 2026, `AlgebraicNumberTheory/Idele/PrincipalNorm.lean:274`][Yamaguchi2026]). -/
noncomputable def normOneIdeleClassGroup : Subgroup (IdeleClassGroup K) :=
  MonoidHom.ker (ideleClassContent K)

end Atlas.Knowledge
