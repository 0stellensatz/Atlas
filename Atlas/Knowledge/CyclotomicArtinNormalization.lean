import Mathlib
import Atlas.Knowledge.FinitePlaceIdele
import Atlas.Knowledge.IdeleClassGroup
import Atlas.Knowledge.IsGlobalArtinMap
import Atlas.Knowledge.MaximalAbelianExtension

/-!
# cyclotomic Artin normalization

The global Artin map computed on a cyclotomic field: on a floor of `ℚ`'s maximal abelian
extension that is a cyclotomic extension of level `m`, any global Artin map sends the
class of a one-place uniformizer idele at a prime `q` not dividing `m` to an
automorphism whose restriction to the floor is `ζ ↦ ζ ^ q` — Milne's
`(p, ℚ[ζₘ]/ℚ) = [p]`, stated through Mathlib's
`IsCyclotomicExtension.Rat.galEquivZMod` as one equation in `(ZMod m)ˣ`. This is the
normalization that gives Kronecker–Weber its class-field meaning: which automorphism each
unramified prime induces on the cyclotomic field containing a given abelian extension.
The claim quantifies over `Atlas.Knowledge.IsGlobalArtinMap`'s characterization and is
proved from that characterization alone — no reciprocity map is constructed here.

## Main statements

* `cyclotomicArtinNormalization` — the uniformizer class at `q ∤ m` restricts on the floor
  to `ζ ↦ ζ ^ q`; proved.

## Implementation notes

The statement is nonvacuous — `ℚ(ζₘ)` is abelian over `ℚ`, so level-`m` floors exist —
and true of every such floor: `q ∤ m` keeps every prime over `q` unramified, the Artin
characterization then makes the restricted automorphism an arithmetic Frobenius at each
of them, and reduction is injective on `m`-th roots of unity at primes away from `m`,
which pins the `galEquivZMod` class to `[q]`. The proof follows exactly that route, on
one chosen prime over `q`, with the unramifiedness supplied by the cyclotomic
ramification theory of the pinned Mathlib and carried from `ℤ` to `𝓞 ℚ` by restriction
of scalars. The source's transported definition — the Frobenius as a `Gal` element built
from its own reciprocity map (`KroneckerWeber/RationalRayClassFieldCyclotomic.lean:492`) —
is subsumed rather than ported: the source *constructs* the reciprocity value where Atlas
*characterizes* it, as `Atlas.Knowledge.IsFinitePlaceHilbertSymbol` does for the local
symbol, so the characterization-only Artin layer already names the transported
automorphism as a restriction. The statement's shape moves once against the source: the
source computes on the concrete `CyclotomicField m ℚ`, where this claim quantifies over
the level-`m` floors of `ℚ^ab` — the form the restriction vocabulary forces — and neither
statement implies the other without identifying `CyclotomicField m ℚ` with such a floor.
Two `letI` bindings sit in statement position because pinned Mathlib fails to *synthesize*
`Normal` and `NumberField` for a `FiniteGaloisIntermediateField` floor at `K := ℚ`, though
the instance values themselves typecheck and `FiniteDimensional` synthesizes fine; the
`NumberField` binding is `Atlas.Knowledge.IsGlobalArtinMap`'s own idiom, which at generic
`K` needs no other. Milne's Introduction statement restricts `m` to be odd or divisible by
`4`; `galEquivZMod` needs no such restriction, so neither does this statement.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open scoped NumberField WithZero
open NumberField IsDedekindDomain

namespace Atlas.Knowledge

/-- The **cyclotomic Artin normalization**: on a level-`m` cyclotomic floor of `ℚ`'s
maximal abelian extension, a global Artin map sends the class of a one-place uniformizer
idele at a prime `q ∤ m` to an automorphism restricting on the floor to `ζ ↦ ζ ^ q` —
the primes over `q` are unramified, so the characterization makes the restriction an
arithmetic Frobenius at one of them, whose congruence pins the image of the chosen root
of unity exactly, `m` being invertible at that prime
([Milne 2020, Introduction, p.7, and Chap. V, §3, Ex. 3.2, p.157][MilneCFT];
[Yamaguchi 2026, `KroneckerWeber/RationalRayClassFieldCyclotomic.lean:510`, transported
definition at `:492`][Yamaguchi2026]). -/
theorem cyclotomicArtinNormalization
    {φ : IdeleClassGroup ℚ →ₜ*
      (maximalAbelianExtension ℚ ≃ₐ[ℚ] maximalAbelianExtension ℚ)}
    (hφ : IsGlobalArtinMap ℚ φ) (m : ℕ) [NeZero m]
    (L : FiniteGaloisIntermediateField ℚ (maximalAbelianExtension ℚ))
    [IsCyclotomicExtension {m} ℚ L]
    (q : ℕ) (hq : q.Prime) (hqm : ¬ q ∣ m)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : v.asIdeal = Ideal.span {(q : 𝓞 ℚ)})
    (π : (v.adicCompletion ℚ)ˣ)
    (hπ : (Valued.v : Valuation (v.adicCompletion ℚ) ℤᵐ⁰).IsUniformizer
      (π : v.adicCompletion ℚ)) :
    letI : Normal ℚ L := L.isGalois.to_normal
    letI : NumberField L := NumberField.of_module_finite ℚ L
    IsCyclotomicExtension.Rat.galEquivZMod m L
        (AlgEquiv.restrictNormalHom L (φ (finitePlaceIdeleClass v π))) =
      ZMod.unitOfCoprime q (hq.coprime_iff_not_dvd.mpr hqm) := by
  letI : Normal ℚ L := L.isGalois.to_normal
  letI : NumberField L := NumberField.of_module_finite ℚ L
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  -- the base algebra map is an isomorphism, `𝓞 ℚ` being `ℤ` in other clothes
  have halg : Function.Bijective (algebraMap ℤ (𝓞 ℚ)) := by
    have heq : algebraMap ℤ (𝓞 ℚ) =
        (Rat.ringOfIntegersEquiv.symm : ℤ ≃+* 𝓞 ℚ).toRingHom := RingHom.ext_int _ _
    rw [heq]
    exact Rat.ringOfIntegersEquiv.symm.bijective
  -- `v` lies over `q ℤ`
  have hunder : v.asIdeal.under ℤ = Ideal.span {(q : ℤ)} := by
    rw [hv, Ideal.under_def]
    have hmap : Ideal.span {(q : 𝓞 ℚ)} =
        Ideal.map (algebraMap ℤ (𝓞 ℚ)) (Ideal.span {(q : ℤ)}) := by
      rw [Ideal.map_span, Set.image_singleton, map_natCast]
    rw [hmap, Ideal.comap_map_of_bijective _ halg]
  haveI hvq : v.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) := ⟨hunder.symm⟩
  -- every prime of `𝓞 L` over `v` is unramified over the base
  have hunram : ∀ w : IsDedekindDomain.HeightOneSpectrum (𝓞 L),
      w.asIdeal.LiesOver v.asIdeal → Algebra.IsUnramifiedAt (𝓞 ℚ) w.asIdeal := by
    intro w hw
    haveI := hw
    haveI : w.asIdeal.LiesOver (Ideal.span {(q : ℤ)}) :=
      Ideal.LiesOver.trans w.asIdeal v.asIdeal (Ideal.span {(q : ℤ)})
    haveI : w.asIdeal.IsMaximal := w.isPrime.isMaximal w.ne_bot
    have h1 : Ideal.ramificationIdx w.asIdeal ℤ = 1 :=
      IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd q L w.asIdeal hqm
    haveI h2 : Algebra.IsUnramifiedAt ℤ w.asIdeal := Ideal.ramificationIdx_eq_one_iff.mp h1
    exact Algebra.IsUnramifiedAt.of_restrictScalars ℤ w.asIdeal
  -- a prime over `v`, as a height-one point
  obtain ⟨⟨P, hPprime, hPover⟩⟩ := v.asIdeal.nonempty_primesOver (S := 𝓞 L)
  haveI := hPprime
  haveI := hPover
  have hPbot : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P
  set w : IsDedekindDomain.HeightOneSpectrum (𝓞 L) := ⟨P, hPprime, hPbot⟩
  -- the Artin value is an arithmetic Frobenius at `w`
  have harith := hφ L v π hπ hunram w hPover
  -- the residue cardinality at the base is `q`
  have hcard : Nat.card (𝓞 ℚ ⧸ w.asIdeal.under (𝓞 ℚ)) = q := by
    have h1 : w.asIdeal.under (𝓞 ℚ) = v.asIdeal := hPover.over.symm
    have e : (𝓞 ℚ ⧸ Ideal.span {(q : 𝓞 ℚ)}) ≃+* (ℤ ⧸ Ideal.span {(q : ℤ)}) :=
      Ideal.quotientEquiv _ _ Rat.ringOfIntegersEquiv
        (by rw [Ideal.map_span, Set.image_singleton, map_natCast])
    rw [h1, hv, Nat.card_congr e.toEquiv, Int.card_ideal_quot]
  -- `m` stays invertible at `w`
  have hζ := IsCyclotomicExtension.zeta_spec m ℚ L
  have hζint := hζ.toInteger_isPrimitiveRoot
  have hmQ : ((m : ℕ) : 𝓞 L) ∉ w.asIdeal := by
    intro hmem
    have hbase : ((m : ℕ) : 𝓞 ℚ) ∈ v.asIdeal := by
      rw [hPover.over, Ideal.under_def, Ideal.mem_comap, map_natCast]
      exact hmem
    rw [hv, Ideal.mem_span_singleton] at hbase
    have hdvd : (q : ℤ) ∣ (m : ℤ) := by
      simpa using map_dvd Rat.ringOfIntegersEquiv hbase
    exact hqm (Int.natCast_dvd_natCast.mp hdvd)
  -- the Frobenius congruence pins the action on the chosen root of unity exactly
  have happly := harith.apply_of_pow_eq_one hζint.pow_eq_one hmQ
  have hfrobζ : AlgEquiv.restrictNormalHom L (φ (finitePlaceIdeleClass v π)) •
      hζ.toInteger = hζ.toInteger ^ q := hcard ▸ happly
  rw [IsCyclotomicExtension.Rat.galEquivZMod_smul_of_pow_eq m L _ hζint.pow_eq_one]
    at hfrobζ
  -- exponents agree modulo `m`, which is the equation in `(ZMod m)ˣ`
  rw [(hζint.isOfFinOrder (NeZero.ne _)).pow_inj_mod, ← hζint.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff', ZMod.natCast_val, ZMod.cast_id] at hfrobζ
  exact Units.ext (by rw [ZMod.coe_unitOfCoprime]; exact hfrobζ)

end Atlas.Knowledge
