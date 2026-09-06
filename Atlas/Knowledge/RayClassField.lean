import Mathlib
import Atlas.Knowledge.IsConductor
import Atlas.Knowledge.IdeleClassNormRange

/-!
# ray class field

The ray class field of a modulus, as a characterization: a finite extension is *the* ray
class field of `𝔪` when its norm subgroup is exactly the congruence subgroup of `𝔪` — the
Artin map then identifies its Galois group with the ray class group. On that predicate the
three conductor theorems are recorded: the conductor criterion — an abelian extension
embeds into the ray class field exactly when its conductor divides the modulus — conductor
exactness — the global conductor exponent at a finite place is the least level at which
the local higher unit group is normic — and ramification support — the finite conductor is
supported exactly on the ramified places.

## Main definitions

* `IsRayClassField` — norm subgroup equal to the congruence subgroup.

## Main statements

* `nonempty_algHom_isRayClassField_iff` — the conductor criterion, recorded ahead of its
  proof.
* `isConductor_finitePart_eq_local` — conductor exactness against the tensor-model local
  norms, recorded ahead of its proof.
* `isConductor_finitePart_support_iff` — the conductor's support is the ramification
  locus, recorded ahead of its proof.

## Implementation notes

Every statement takes the ray class field and the conductor through their predicates —
`Atlas.Knowledge.IsConductor` slots rather than constructed data. The local norm subgroup
of the exactness statement is the tensor form `Units.map (Algebra.norm (K_v))` on
`(K_v ⊗[K] L)ˣ` — the shape the source proves equal to its chosen-completion model
(`AlgebraicNumberTheory/Idele/Relative/FinitePlaceTensorNorm.lean:162`). Ramification
support is stated as the equivalence Milne asserts ("divisible exactly by the primes
ramifying"); the source restates only the forward implication
(`GlobalClassFieldTheory/GlobalClassFields/AbelianConductorRamification.lean:68`), on its
chosen completions, though the equivalence it derives it from is an iff one rewrite away.
The exactness statement's `sInf` is over a set that is nonempty because the local norm
group of an abelian extension is open, so the `ℕ`-junk value at the empty set never
enters.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [NumberField K]

/-- The **ray class field** characterization: the norm subgroup of `M` is exactly the
congruence subgroup of `𝔪`, so the Artin map identifies `Gal (M/K)` with the ray class
group of `𝔪` ([Milne 2020, Chap. V, §3, p.158][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/RayClassFieldRealization.lean:81`). -/
def IsRayClassField (m : Modulus K) (M : Type*) [Field M] [NumberField M] [Algebra K M]
    [FiniteDimensional K M] : Prop :=
  ideleClassNormRange K M = congruenceSubgroup K m

/-- **The conductor criterion**: an abelian extension embeds into the ray class field of
`𝔪` exactly when its conductor divides `𝔪`. Claim recorded ahead of its proof
([Milne 2020, Chap. V, §3, Rem. 3.8 and footnote 3, p.158][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/FullConductorRayClassField.lean:26`). -/
theorem nonempty_algHom_isRayClassField_iff (m : Modulus K)
    (M : Type*) [Field M] [NumberField M] [Algebra K M] [FiniteDimensional K M]
    (hM : IsRayClassField K m M)
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] (f : Modulus K)
    (hf : IsConductor K (ideleClassNormRange K L) f) :
    Nonempty (L →ₐ[K] M) ↔ f ≤ m := by
  sorry

/-- **Conductor exactness**: the finite conductor exponent at `v` is the least level at
which the local higher unit group is contained in the tensor-model local norms. Claim
recorded ahead of its proof ([Milne 2020, Chap. I, 1.9, p.23][MilneCFT];
Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/AbelianConductorExactness.lean:111`). -/
theorem isConductor_finitePart_eq_local
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] (f : Modulus K)
    (hf : IsConductor K (ideleClassNormRange K L) f) (v : HeightOneSpectrum (𝓞 K)) :
    f.finitePart v = sInf {n : ℕ | localHigherUnitGroup K v n ≤
      MonoidHom.range (Units.map (Algebra.norm (v.adicCompletion K) :
        (v.adicCompletion K ⊗[K] L) →* v.adicCompletion K))} := by
  sorry

/-- **Ramification support**: the finite conductor is supported exactly on the finite
places ramified in `L`. Claim recorded ahead of its proof
([Milne 2020, Chap. V, §3, Rem. 3.8, p.158][MilneCFT]; Yamaguchi 2026,
`GlobalClassFieldTheory/GlobalClassFields/AbelianConductorRamification.lean:68`, the
forward implication on chosen completions). -/
theorem isConductor_finitePart_support_iff
    (L : Type*) [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    [IsAbelianGalois K L] (f : Modulus K)
    (hf : IsConductor K (ideleClassNormRange K L) f) (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ f.finitePart.support ↔
      ∃ w : HeightOneSpectrum (𝓞 L), w.asIdeal.LiesOver v.asIdeal ∧
        ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal := by
  sorry

end Atlas.Knowledge

end
