import Mathlib
import Atlas.Knowledge.CycloField
import Atlas.Knowledge.CycloFieldLowerRamificationGroupEqBot
import Atlas.Knowledge.FiniteExtensionIsMixedCharLocalField
import Atlas.Knowledge.IsArithmeticFrobenius
import Atlas.Knowledge.IsArithmeticFrobeniusApplyOfPowEqOne
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.LowerRamificationGroup
import Atlas.Knowledge.NormQuotient
import Atlas.Knowledge.NormalizedValuation
import Atlas.Knowledge.UnramifiedNormRange
import Atlas.Knowledge.UpperRamificationGroup

/-!
# cyclotomic floor of prescribed degree

The unramified extension of degree `d` of a mixed-characteristic local field `K`, realized as
the cyclotomic floor `K (μ_{q ^ d - 1})` of `Atlas.Knowledge.CycloField`, `q` the residue
cardinality: it has degree exactly `d`, its norm subgroup is the set of elements whose
normalized valuation is divisible by `d`, and its upper ramification groups vanish from index
`0` on. This is the unramified factor the ramification-compatibility descent needs as a
concrete subfield of the algebraic closure with a computable norm subgroup and a computable
filtration.

## Main statements

* `cycloField_lowerRamificationGroup_eq_bot_of_pos` — the floor is unramified.
* `cycloField_finrank` — `[K (μ_{q ^ d - 1}) : K] = d`.
* `cycloField_normRange` / `cycloField_localNormSubgroup` — the norm subgroup is the preimage
  of `d ℤ` under the normalized valuation, in the unit-norm-range and the norm-subgroup
  spellings.
* `cycloField_upperRamificationGroup_eq_bot` — `G^t = ⊥` for `t ≥ 0`.

## Implementation notes

The degree is the order of the arithmetic Frobenius, which generates the Galois group of an
unramified extension (`Atlas.Knowledge.orderOf_of_isArithmeticFrobenius`): its `d`th power
fixes every generator because `ζ ↦ ζ ^ q` iterated `d` times is `ζ ↦ ζ ^ (q ^ d) = ζ` on the
`(q ^ d - 1)`th roots of unity, and no smaller power fixes a primitive root, since
`ζ ^ (q ^ o) = ζ` forces `q ^ d - 1 ∣ q ^ o - 1`. The layer's inertia triviality for
prime-to-`q` cyclotomic floors, `Atlas.Knowledge.cycloField_lowerRamificationGroup_eq_bot`,
is what makes the Frobenius theory apply; `q ^ d - 1` is prime to `q` because it is one less
than a power of `q`. The norm subgroup is then `Atlas.Knowledge.unramifiedNormRange` at that
degree, the floor equipped with the local-field structure of
`Atlas.Knowledge.exists_extension_isMixedCharLocalField` inside the proof. The upper groups
vanish by antitonicity from `G^0 = G_0 = ⊥`; the statement is at `t ≥ 0` because the
compositum argument reads it at every positive index. The norm subgroup is exported in both
spellings the layer uses, as `Atlas.Knowledge.UnramifiedNormRange` does, since the order
reversal and the compositum law speak `Atlas.Knowledge.localNormSubgroup`. The same extension
is constructed abstractly, as a fixed field of the degree datum, in
`Atlas.Knowledge.UnramifiedExtensionOfDegree`; this item is its concrete cyclotomic
realization, not a second construction of the abstract one.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

/- The level `q ^ d - 1` is prime to `q`: it is one less than a power of `q`. -/
private theorem coprime_pow_sub_one {d : ℕ} (hd : 0 < d) :
    Nat.Coprime (Nat.card 𝓀[K] ^ d - 1) (Nat.card 𝓀[K]) := by
  have hq1 : 1 < Nat.card 𝓀[K] := Finite.one_lt_card
  have hqd1 : 1 ≤ Nat.card 𝓀[K] ^ d := Nat.one_le_pow _ _ (by omega)
  have h1 : Nat.Coprime (Nat.card 𝓀[K] ^ d - 1) (Nat.card 𝓀[K] ^ d - 1 + 1) :=
    Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _)
  rw [Nat.sub_add_cancel hqd1] at h1
  exact Nat.Coprime.coprime_dvd_right (dvd_pow_self _ hd.ne') h1

/-- The cyclotomic floor at level `q ^ d - 1` has trivial inertia: the level is prime to `q`
([Serre 1979, Chap. IV, §4, Prop. 16, p.77][Serre1979]). -/
theorem cycloField_lowerRamificationGroup_eq_bot_of_pos {d : ℕ} (hd : 0 < d) :
    lowerRamificationGroup K (cycloField K (Nat.card 𝓀[K] ^ d - 1)) 0 = ⊥ :=
  cycloField_lowerRamificationGroup_eq_bot K (coprime_pow_sub_one K hd)

/-- **The cyclotomic floor at level `q ^ d - 1` has degree `d`**: the arithmetic Frobenius
`ζ ↦ ζ ^ q` generates its Galois group, and its order on the `(q ^ d - 1)`th roots of unity
is exactly `d` ([Serre 1979, Chap. IV, §4, Prop. 16 and Cor. 1, p.77][Serre1979]). -/
theorem cycloField_finrank {d : ℕ} (hd : 0 < d) :
    Module.finrank K (cycloField K (Nat.card 𝓀[K] ^ d - 1)) = d := by
  set q := Nat.card 𝓀[K] with hq
  have hq1 : 1 < q := Finite.one_lt_card
  set m := q ^ d - 1 with hm
  have hqd1 : 1 ≤ q ^ d := Nat.one_le_pow _ _ (by omega)
  have hmsucc : m + 1 = q ^ d := by omega
  have hm0 : m ≠ 0 := by
    have := Nat.one_lt_pow hd.ne' hq1
    omega
  have hcop : Nat.Coprime m q := coprime_pow_sub_one K hd
  have h0 := cycloField_lowerRamificationGroup_eq_bot K hcop
  obtain ⟨σ, hσ⟩ := exists_isArithmeticFrobenius K (cycloField K m) h0
  rw [← orderOf_of_isArithmeticFrobenius K (cycloField K m) h0 hσ]
  -- the Frobenius acts on the generating roots of unity by `ζ ↦ ζ ^ q`
  have hact : ∀ (x : AlgebraicClosure K) (hx : x ∈ cycloField K m), x ^ m = 1 →
      σ ⟨x, hx⟩ = ⟨x ^ q, pow_mem hx _⟩ := by
    intro x hx hxm
    have h := hσ.apply_of_pow_eq_one hcop (ζ := (⟨x, hx⟩ : cycloField K m))
      (Subtype.ext (by simpa using hxm))
    rw [h]
    exact Subtype.ext (SubmonoidClass.coe_pow _ _)
  have hiter : ∀ (j : ℕ) (x : AlgebraicClosure K) (hx : x ∈ cycloField K m), x ^ m = 1 →
      (σ ^ j) ⟨x, hx⟩ = ⟨x ^ q ^ j, pow_mem hx _⟩ := by
    intro j
    induction j with
    | zero => intro x hx hxm; exact Subtype.ext (by simp)
    | succ n ih =>
      intro x hx hxm
      have hxroot : (x ^ q) ^ m = 1 := by
        rw [← pow_mul, Nat.mul_comm, pow_mul, hxm, one_pow]
      rw [pow_succ, AlgEquiv.mul_apply, hact x hx hxm, ih (x ^ q) (pow_mem hx _) hxroot]
      exact Subtype.ext (show (x ^ q) ^ q ^ n = x ^ q ^ (n + 1) by rw [← pow_mul, ← pow_succ'])
  -- the `d`th power is the identity on the generators
  have hpowd : σ ^ d = 1 := by
    apply AlgEquiv.coe_toAlgHom_injective
    refine IntermediateField.algHom_ext_of_eq_adjoin (S := cycloField K m) K rfl ?_
    intro x hx
    have hxm : x ^ m = 1 := cycloField_pow_eq_one_of_mem_rootSet K hx
    simp only [AlgEquiv.coe_toAlgHom]
    rw [hiter d x _ hxm]
    refine Subtype.ext ?_
    rw [AlgEquiv.one_apply]
    change x ^ q ^ d = x
    rw [← hmsucc, pow_succ, hxm, one_mul]
  -- and no smaller power fixes a primitive root
  haveI : NeZero m := ⟨hm0⟩
  haveI : NeZero (m : K) := ⟨Nat.cast_ne_zero.mpr hm0⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) m
  have hζmem : ζ₀ ∈ cycloField K m := mem_cycloField K hm0 hζ₀.pow_eq_one
  have hdvd : orderOf σ ∣ d := orderOf_dvd_of_pow_eq_one hpowd
  have hfin : IsOfFinOrder σ := isOfFinOrder_iff_pow_eq_one.mpr ⟨d, hd, hpowd⟩
  refine Nat.le_antisymm (Nat.le_of_dvd hd hdvd) ?_
  set o := orderOf σ with hodef
  have ho0 : 0 < o := hfin.orderOf_pos
  have h1 : (σ ^ o) ⟨ζ₀, hζmem⟩ = ⟨ζ₀, hζmem⟩ := by
    rw [hodef, pow_orderOf_eq_one]
    rfl
  rw [hiter o ζ₀ hζmem hζ₀.pow_eq_one] at h1
  have h2 : ζ₀ ^ q ^ o = ζ₀ := congrArg Subtype.val h1
  have hqo1 : 1 ≤ q ^ o := Nat.one_le_pow _ _ (by omega)
  have h3 : ζ₀ ^ (q ^ o - 1) = 1 := by
    have hζne : ζ₀ ≠ 0 := hζ₀.ne_zero hm0
    have hsp : q ^ o = q ^ o - 1 + 1 := by omega
    have h4 : ζ₀ ^ (q ^ o - 1) * ζ₀ = 1 * ζ₀ := by
      rw [one_mul, ← pow_succ, ← hsp]
      exact h2
    exact mul_right_cancel₀ hζne h4
  have h5 : m ∣ q ^ o - 1 := hζ₀.dvd_of_pow_eq_one _ h3
  have hqogt : 1 < q ^ o := Nat.one_lt_pow ho0.ne' hq1
  have h6 : m ≤ q ^ o - 1 := Nat.le_of_dvd (by omega) h5
  have h7 : q ^ d ≤ q ^ o := by
    rw [← hmsucc]
    exact (Nat.le_sub_iff_add_le hqo1).mp h6
  exact (Nat.pow_le_pow_iff_right hq1).mp h7

/-- **The norm subgroup of the cyclotomic floor at level `q ^ d - 1`** is the set of elements
of normalized valuation divisible by `d` — the unramified norm range at degree `d`
([Serre 1979, Chap. V, §2, Prop. 3 and Cor., p.82][Serre1979]). -/
theorem cycloField_normRange {d : ℕ} (hd : 0 < d) :
    (Units.map (Algebra.norm K : cycloField K (Nat.card 𝓀[K] ^ d - 1) →* K)).range =
      Subgroup.comap (normalizedValuationHom K)
        (Subgroup.zpowers (Multiplicative.ofAdd (d : ℤ))) := by
  obtain ⟨vL, tL, hVE, _, hMCL⟩ :=
    exists_extension_isMixedCharLocalField K (cycloField K (Nat.card 𝓀[K] ^ d - 1))
  letI := vL
  letI := tL
  haveI := hVE
  haveI := hMCL
  rw [unramifiedNormRange K _ (cycloField_lowerRamificationGroup_eq_bot_of_pos K hd),
    cycloField_finrank K hd]

/-- The norm subgroup of the cyclotomic floor at level `q ^ d - 1`, in the norm-subgroup
spelling ([Serre 1979, Chap. V, §2, Prop. 3 and Cor., p.82][Serre1979]). -/
theorem cycloField_localNormSubgroup {d : ℕ} (hd : 0 < d) :
    localNormSubgroup K (cycloField K (Nat.card 𝓀[K] ^ d - 1)) =
      Subgroup.comap (normalizedValuationHom K)
        (Subgroup.zpowers (Multiplicative.ofAdd (d : ℤ))) := by
  rw [← cycloField_normRange K hd]
  rfl

/-- The upper ramification groups of the cyclotomic floor at level `q ^ d - 1` vanish from
index `0` on: `G^t ≤ G^0 = G_0 = ⊥` for `t ≥ 0`
([Serre 1979, Chap. IV, §4, Prop. 16, p.77][Serre1979]). -/
theorem cycloField_upperRamificationGroup_eq_bot {d : ℕ} (hd : 0 < d) {t : ℝ} (ht : 0 ≤ t) :
    upperRamificationGroup K (cycloField K (Nat.card 𝓀[K] ^ d - 1)) t = ⊥ := by
  apply le_bot_iff.mp
  calc upperRamificationGroup K (cycloField K (Nat.card 𝓀[K] ^ d - 1)) t
      ≤ upperRamificationGroup K (cycloField K (Nat.card 𝓀[K] ^ d - 1)) 0 :=
        upperRamificationGroup_antitone K _ ht
    _ = lowerRamificationGroup K (cycloField K (Nat.card 𝓀[K] ^ d - 1)) 0 :=
        upperRamificationGroup_zero K _
    _ = ⊥ := cycloField_lowerRamificationGroup_eq_bot_of_pos K hd

end Atlas.Knowledge
