import Mathlib
import Atlas.Knowledge.AbelianizedKummerRootQuotient
import Atlas.Knowledge.IsLocalHilbertSymbol
import Atlas.Knowledge.IsLocalReciprocity
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.KummerField
import Atlas.Knowledge.KummerPowSubNorm

/-!
# skew-symmetry of the local Hilbert symbol

The symbol identities that need the reciprocity map's norm kernels rather than the
characterization alone: `(a, c ^ n - a) = 1` whenever `c ^ n - a ≠ 0`, hence `(a, -a) = 1`
and `(a, 1 - a) = 1`, and from these the skew-symmetry `(a, b) (b, a) = 1`. The first is the
`normKernel` field of `Atlas.Knowledge.IsLocalReciprocity` at the Kummer extension
`K (a ^ (1 / n))`, where `c ^ n - a` is a norm by `Atlas.Knowledge.KummerPowSubNorm`, so
every lift of `φ (c ^ n - a)` fixes the radical; the last is Serre's expansion of
`(ab, -ab)`. All four are proved, and the skew-symmetry is what turns the left kernel of
`Atlas.Knowledge.LocalHilbertSymbolNondegeneracy` into its right kernel.

## Main statements

* `IsLocalHilbertSymbol.pow_sub_right_eq_one` — `(a, c ^ n - a) = 1`; proved.
* `IsLocalHilbertSymbol.neg_self`, `IsLocalHilbertSymbol.one_sub` — `(a, -a) = 1` and
  `(a, 1 - a) = 1`, the cases `c = 0` and `c = 1`; proved.
* `IsLocalHilbertSymbol.skew` — `(a, b) (b, a) = 1`; proved.

## Implementation notes

The Kummer extension is `Atlas.Knowledge.kummerField K n a`, whose Galois-ness, finiteness,
extensionality on one root and commutativity are that item's; the extensionality is both the
generation hypothesis `Atlas.Knowledge.kummerPowSubNorm` asks for and, as
`Atlas.Knowledge.kummerField_aut_comm`, the commutativity the `normKernel` field asks for.
From the norm, `normKernel` puts `φ (c ^ n - a)` in the image of the fixing subgroup; a lift
of it differs from a fixing automorphism by an element of the closure of the commutator
subgroup, which fixes the root by
`Atlas.Knowledge.kummerRoot_apply_eq_self_of_mem_commutator_topologicalClosure`, so the root
is fixed and the symbol is `1`. The second slot is a unit `b` with `(b : K) = c ^ n - a`
rather than a `Units.mk0`, so that the specializations to `-a` and `1 - a` carry no
nonvanishing proof in their statements. The source proves the Steinberg relation from its own
norm witness in the transposed slot
(`LocalClassFieldTheory/Kummer/LocalHilbertPairing.lean:213`), derives `(a, -a) = 1` from it
through `-a = (1 - a) / (1 - a⁻¹)` (`:228`), and expands `(ab, -ab)` for skew-symmetry
(`:301`); here `(a, -a) = 1` is the case `c = 0` of the general norm and needs no detour. The
declarations sit in the `IsLocalHilbertSymbol` namespace, as `.pow_sub_right_eq_one`,
`.neg_self`, `.one_sub` and `.skew` beside the characterization's own lemmas, rather than
under the file's stem: they are properties of the predicate and read as such at their use
sites, and the file is named for the identity that heads them.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsMixedCharLocalField K]

namespace IsLocalHilbertSymbol

variable {n : ℕ} {h : Kˣ → Kˣ → Kˣ}

/-- `(a, c ^ n - a) = 1` whenever `c ^ n - a ≠ 0`: the second slot is a norm from
`K (a ^ (1 / n))` by `Atlas.Knowledge.kummerPowSubNorm`, so its reciprocity class lies in the
image of the fixing subgroup of that extension and every lift of it fixes the radical
([Serre 1979, Chap. XIV, §2, Prop. 4 iv, p.206 and Prop. 7 iii–iv, p.208][Serre1979]). -/
theorem pow_sub_right_eq_one (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) (a b : Kˣ) (c : K) (hb : (b : K) = c ^ n - a) :
    h a b = 1 := by
  obtain ⟨φ, hφ, hspec⟩ := hh
  obtain ⟨ζ, hζ⟩ := hmu
  have hζ : IsPrimitiveRoot ζ n := (mem_primitiveRoots (Nat.pos_of_ne_zero hn)).mp hζ
  haveI : NeZero n := ⟨hn⟩
  obtain ⟨β, hβL, hβ⟩ := exists_mem_kummerField_pow_eq K hn (a : K)
  have ha0 : algebraMap K (AlgebraicClosure K) (a : K) ≠ 0 :=
    (map_ne_zero (algebraMap K (AlgebraicClosure K))).mpr a.ne_zero
  have hβ0 : β ≠ 0 := fun h0 => by
    rw [h0, zero_pow hn] at hβ
    exact ha0 hβ.symm
  set L : IntermediateField K (AlgebraicClosure K) := kummerField K n (a : K) with hLdef
  set β' : L := ⟨β, hβL⟩ with hβ'def
  have hβ' : β' ^ n = algebraMap K L (a : K) := Subtype.ext (by simp [hβ'def, hβ])
  have hgen : ∀ σ τ : L ≃ₐ[K] L, σ β' = τ β' → σ = τ := fun σ τ hστ =>
    kummerField_algEquiv_ext hζ hn a hβ hστ
  have hcomm : ∀ σ τ : L ≃ₐ[K] L, σ * τ = τ * σ := kummerField_aut_comm hζ hn a
  -- `b` is a norm from `L`
  obtain ⟨y, hy⟩ := kummerPowSubNorm hζ hn a hβ' hgen c
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [Algebra.norm_zero] at hy
    exact b.ne_zero (hb.trans hy.symm)
  have hbmem : b ∈ MonoidHom.range (Units.map (Algebra.norm K (S := L))) :=
    ⟨Units.mk0 y hy0, Units.ext (by simp [hy, hb])⟩
  rw [← hφ.normKernel L hcomm, Subgroup.mem_comap, Subgroup.mem_map] at hbmem
  obtain ⟨τ, hτ, hτb⟩ := hbmem
  -- every lift of `φ b` fixes `β`
  have hfix : ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      (QuotientGroup.mk (σ : Field.absoluteGaloisGroup K) :
        Field.absoluteGaloisGroupAbelianization K) = φ b → σ β = β := by
    intro σ hσ
    let τ' : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := τ
    let σ' : Field.absoluteGaloisGroup K := σ
    have hmem : τ⁻¹ * σ' ∈ (commutator (Field.absoluteGaloisGroup K)).topologicalClosure :=
      QuotientGroup.eq.mp (hτb.trans hσ.symm)
    have h1 := kummerRoot_apply_eq_self_of_mem_commutator_topologicalClosure hζ hn a hβ
      (τ⁻¹ * σ') hmem
    change τ'.symm (σ β) = β at h1
    rw [AlgEquiv.symm_apply_eq] at h1
    rw [h1]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).mp hτ β hβL
  obtain ⟨σ, hσ⟩ : ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
      (QuotientGroup.mk (σ : Field.absoluteGaloisGroup K) :
        Field.absoluteGaloisGroupAbelianization K) = φ b :=
    QuotientGroup.mk_surjective (φ b)
  have h1 := hspec a b σ hσ β hβ
  rw [hfix σ hσ] at h1
  have h2 : algebraMap K (AlgebraicClosure K) ((h a b : Kˣ) : K) = 1 :=
    (mul_left_eq_self₀.mp h1.symm).resolve_right hβ0
  exact Units.ext ((algebraMap K (AlgebraicClosure K)).injective
    (by rw [Units.val_one, map_one]; exact h2))

/-- `(a, -a) = 1`, the case `c = 0`
([Serre 1979, Chap. XIV, §2, Prop. 7 iv, p.208][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Kummer/LocalHilbertPairing.lean:228`). -/
theorem neg_self (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) (a : Kˣ) : h a (-a) = 1 :=
  pow_sub_right_eq_one hh hn hmu a (-a) 0 (by rw [Units.val_neg, zero_pow hn, zero_sub])

/-- `(a, 1 - a) = 1` when `1 - a ≠ 0`, the case `c = 1` — the Steinberg relation
([Serre 1979, Chap. XIV, §2, Prop. 7 iv, p.208][Serre1979]; Yamaguchi 2026,
`LocalClassFieldTheory/Kummer/LocalHilbertPairing.lean:213`). -/
theorem one_sub (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) (a b : Kˣ) (hb : (b : K) = 1 - a) : h a b = 1 :=
  pow_sub_right_eq_one hh hn hmu a b 1 (by rw [hb, one_pow])

/-- **Skew-symmetry of the local Hilbert symbol**: `(a, b) (b, a) = 1`, by expanding
`1 = (ab, -ab)` bimultiplicatively into `(a, -a) (a, b) (b, a) (b, -b)`
([Serre 1979, Chap. XIV, §2, Prop. 4 v, p.206, proof p.207, and Prop. 7 v, p.208][Serre1979];
Yamaguchi 2026, `LocalClassFieldTheory/Kummer/LocalHilbertPairing.lean:301`). -/
theorem skew (hh : IsLocalHilbertSymbol K n h) (hn : n ≠ 0)
    (hmu : (primitiveRoots n K).Nonempty) (a b : Kˣ) : h a b * h b a = 1 := by
  have e1 : h (a * b) (-(a * b)) = h a (-(a * b)) * h b (-(a * b)) := mul_left hh hn a b _
  have e2 : h a (-(a * b)) = h a (-a) * h a b := by
    rw [show -(a * b) = -a * b by rw [neg_mul]]
    exact mul_right hh hn a (-a) b
  have e3 : h b (-(a * b)) = h b a * h b (-b) := by
    rw [show -(a * b) = a * -b by rw [mul_neg]]
    exact mul_right hh hn b a (-b)
  rw [neg_self hh hn hmu (a * b), e2, e3, neg_self hh hn hmu a, neg_self hh hn hmu b, one_mul,
    mul_one] at e1
  exact e1.symm

end IsLocalHilbertSymbol

end Atlas.Knowledge
