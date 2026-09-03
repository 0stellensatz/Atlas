import Mathlib
import Atlas.Knowledge.CycloField
import Atlas.Knowledge.IntegralClosureDVR
import Atlas.Knowledge.IsArithmeticFrobeniusApplyOfPowEqOne
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LowerRamificationGroup

/-!
# unramified cyclotomic floor

The prime-to-`q` cyclotomic floor of a mixed-characteristic local
field is unramified: for `m` coprime to `q = Nat.card 𝓀[K]` the
zeroth lower-numbering ramification group of
`Atlas.Knowledge.cycloField K m` is trivial. An inertia element moves
every integral element within the maximal ideal of the integral
closure, so it sends each `m`-th root of unity to a congruent one;
reduction is injective on those roots for `m` prime to `q`, so the
element fixes every generator of the floor and is the identity. This
is the level supply of the Frobenius normalization: with trivial
inertia, the finite Artin maps of the floors deliver arithmetic
Frobenii (#104).

## Main statements

* `cycloField_lowerRamificationGroup_eq_bot` — the prime-to-`q`
  cyclotomic floor has trivial inertia; proved.
* `eq_of_pow_eq_one_of_sub_mem` — reduction is injective on the
  `m`-th roots of unity at an ideal avoiding `m`; proved.

## Implementation notes

The membership is unwound by
`Atlas.Knowledge.mem_lowerRamificationGroup_iff` at index zero, the
radical converted by
`Atlas.Knowledge.integralClosure_jacobson_bot_eq_maximalIdeal`, and the
closing extensionality on the adjoined generators is
`IntermediateField.algHom_ext_of_eq_adjoin` with the root-set reading
`Atlas.Knowledge.cycloField_pow_eq_one_of_mem_rootSet` — the pattern of
the uniqueness proof the floor was first built for, and the coprimality
forces `m ≠ 0` since `q > 1`, so no nonvanishing hypothesis is carried.
The injectivity lemma is stated over any domain and any ideal avoiding
`m` — the separability of `X ^ m - 1` in geometric-sum form: the two
roots divide to `η` congruent to `1`, `geom_sum_mul` splits
`0 = η ^ m - 1` into `η - 1` and the geometric sum, the sum is
congruent to `m` and hence nonzero, and the domain cancels. Mathlib
runs the same trick inside `AlgHom.IsArithFrobAt.apply_of_pow_eq_one`
but does not state it standalone. The two generic auxiliaries —
integrality and the coprime cast avoiding the maximal ideal — are
consumed from beside the wrapper
`Atlas.Knowledge.IsArithmeticFrobenius.apply_of_pow_eq_one`, an import
of those lemmas rather than of any Frobenius action. One elaboration
wrinkle: `Atlas.Knowledge.natCast_notMem_maximalIdeal_of_coprime` is
applied with its extension argument written out — `↥(cycloField K m)` —
since a placeholder there postpones a metavariable on which unification
then deadlocks. Layer-original with two disclosed neighbors: the read
repository proves a cyclotomic unramifiedness of its own —
`padicCyclotomicUnramified_finiteUnramifiedExtension`
(`LocalFieldTheory/Padic/Cyclotomic/Unramified/ArithmeticFrobenius.lean:590`),
in its Henselian exponential-valuation bundle, at a monogenic
presentation `Algebra.adjoin K {ζ} = ⊤` of one chosen primitive root —
and bounds inertia at `ℚ_p` cyclotomically
(`RamificationTheory/HilbertRamification/PadicCyclotomicInertiaBound.lean:120`,
which at the prime-to-`p` level says unramifiedness as a cardinality
bound) — but nothing at the layer's `lowerRamificationGroup` rendering,
and its local-class-field chain consumes that corner only for a
norm-subgroup identification
(`LocalClassFieldTheory/Finite/CyclotomicNorm/Unramified.lean`), never
to normalize a reciprocity map; the statement here, on the
intermediate-field floor with all `m`-th roots at once and no Hensel or
monogenicity input, is the layer's own.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open ValuativeRel

namespace Atlas.Knowledge

/-- Reduction is injective on the `m`-th roots of unity at an ideal
avoiding `m`: in a domain, two `m`-th roots of unity congruent modulo
an ideal not containing `m` are equal — the separability of
`X ^ m - 1`, in geometric-sum form. -/
theorem eq_of_pow_eq_one_of_sub_mem {S : Type*} [CommRing S] [IsDomain S] {Q : Ideal S}
    {m : ℕ} (hmQ : (m : S) ∉ Q) {a b : S} (ha : a ^ m = 1) (hb : b ^ m = 1)
    (hab : a - b ∈ Q) : a = b := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hmQ (by rw [Nat.cast_zero]; exact Q.zero_mem)
  have hm1 : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hm0)
  set η := a * b ^ (m - 1) with hηdef
  have hη : η ^ m = 1 := by
    rw [hηdef, mul_pow, ha, one_mul, ← pow_mul, Nat.mul_comm, pow_mul, hb, one_pow]
  have hη1 : η - 1 ∈ Q := by
    have hbm : b ^ (m - 1) * b = 1 := by rw [← pow_succ, hm1, hb]
    have h : η - 1 = b ^ (m - 1) * (a - b) := by
      calc η - 1 = a * b ^ (m - 1) - b ^ (m - 1) * b := by rw [hηdef, hbm]
        _ = b ^ (m - 1) * (a - b) := by ring
    rw [h]
    exact Ideal.mul_mem_left Q _ hab
  have hgeom : (∑ i ∈ Finset.range m, η ^ i) * (η - 1) = 0 := by
    rw [geom_sum_mul, hη, sub_self]
  rcases mul_eq_zero.mp hgeom with hsum | hsub
  · -- the geometric sum reduces to `m` modulo `Q`, so `m ∈ Q` — absurd
    exfalso
    apply hmQ
    have hπη : Ideal.Quotient.mk Q η = 1 := by
      rw [show (1 : S ⧸ Q) = Ideal.Quotient.mk Q 1 from rfl, Ideal.Quotient.eq]
      exact hη1
    have hπ := congrArg (Ideal.Quotient.mk Q) hsum
    rw [map_sum, map_zero] at hπ
    simp only [map_pow, hπη, one_pow] at hπ
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hπ
    rwa [← map_natCast (Ideal.Quotient.mk Q), Ideal.Quotient.eq_zero_iff_mem] at hπ
  · -- `η = 1`, and the unit power of `b` cancels
    have hη' : η = 1 := sub_eq_zero.mp hsub
    have hb1 : b * b ^ (m - 1) = 1 := by
      rw [mul_comm b (b ^ (m - 1)), ← pow_succ, hm1, hb]
    have hbne : b ^ (m - 1) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hb1
      exact zero_ne_one hb1
    apply mul_right_cancel₀ hbne
    rw [← hηdef, hη', hb1]

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/-- **The prime-to-`q` cyclotomic floor is unramified**: for `m`
coprime to `q = Nat.card 𝓀[K]`, the zeroth lower-numbering
ramification group of `Atlas.Knowledge.cycloField K m` is trivial —
an inertia element fixes every `m`-th root of unity because reduction
is injective on them, and the roots generate the floor
([Yamaguchi 2026,
`LocalFieldTheory/Padic/Cyclotomic/Unramified/ArithmeticFrobenius.lean:590`]
[Yamaguchi2026], its Henselian monogenic form; nothing in the source
speaks the layer's `lowerRamificationGroup` rendering). -/
theorem cycloField_lowerRamificationGroup_eq_bot {m : ℕ}
    (hm : Nat.Coprime m (Nat.card 𝓀[K])) :
    lowerRamificationGroup K ↥(cycloField K m) 0 = ⊥ := by
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hm
    omega
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  rw [mem_lowerRamificationGroup_iff] at hσ
  apply AlgEquiv.coe_toAlgHom_injective
  refine IntermediateField.algHom_ext_of_eq_adjoin (S := cycloField K m) K rfl ?_
  intro x hx
  have hxm : x ^ m = 1 := cycloField_pow_eq_one_of_mem_rootSet K hx
  simp only [AlgEquiv.coe_toAlgHom, AlgEquiv.one_apply]
  set ζ : ↥(cycloField K m) := ⟨x, IntermediateField.subset_adjoin _ _ hx⟩
  have hζm : ζ ^ m = 1 := by
    ext
    push_cast
    exact hxm
  set z : integralClosure 𝒪[K] ↥(cycloField K m) :=
    ⟨ζ, IsArithmeticFrobenius.isIntegral_of_pow_eq_one hm0 hζm⟩
  have hz : z ^ m = 1 := by
    ext
    push_cast
    exact congrArg Subtype.val hζm
  -- the inertia congruence puts `σ ζ` and `ζ` in the same residue class
  have hσz := hσ z
  rw [show ((0 : ℤ) + 1).toNat = 1 by norm_num, pow_one,
    integralClosure_jacobson_bot_eq_maximalIdeal K ↥(cycloField K m)] at hσz
  have hz' : galRestrict 𝒪[K] K ↥(cycloField K m)
      (integralClosure 𝒪[K] ↥(cycloField K m)) σ z ^ m = 1 := by
    rw [← map_pow, hz, map_one]
  have heq := eq_of_pow_eq_one_of_sub_mem
    (natCast_notMem_maximalIdeal_of_coprime K ↥(cycloField K m) hm) hz' hz hσz
  have hcoe := congrArg (algebraMap (integralClosure 𝒪[K] ↥(cycloField K m))
    ↥(cycloField K m)) heq
  rw [algebraMap_galRestrict_apply] at hcoe
  exact hcoe

end Atlas.Knowledge
