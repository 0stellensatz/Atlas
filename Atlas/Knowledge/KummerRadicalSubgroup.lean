import Mathlib

/-!
# Kummer radical subgroup

The subgroup `Δ = Kˣ ∩ (Lˣ)ⁿ` of the base units of a field extension that acquire an `n`-th
root upstairs: the group whose classes modulo `n`-th powers index the Kummer characters of
`L / K`. This is the finite-level carrier of the Kummer correspondence — the literature's
`B ⊆ K^× / K^{×n}` is `Δ` modulo powers, and `Atlas.Knowledge.KummerCharacterEquiv` turns
its classes into characters of the Galois group. The item is the subgroup itself, over
arbitrary fields: nothing about roots of unity, Galois closure, or local fields enters its
definition.

## Main definitions

* `kummerRadicalSubgroup` — `{a : Kˣ | ∃ β : Lˣ, β ^ n = a}` as a subgroup of `Kˣ`.

## Main statements

* `mem_kummerRadicalSubgroup_iff` — membership is the defining root, definitionally.

## Implementation notes

The root is asked for in `Lˣ` against the units-level algebra map, so the subgroup laws are
the arithmetic of roots — products and inverses of roots are roots — with no zero-divisor
bookkeeping. Membership carries the existence of a root as data for `Classical.choose`
downstream; the choice is per element, and deliberately so: no multiplicative system of
roots exists in general, and the consumers prove their choices irrelevant instead of
assuming a section.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- The **Kummer radical subgroup** `Δ = Kˣ ∩ (Lˣ)ⁿ`: base units with an `n`-th root in the
extension ([Milne 2020, Chap. VII, App. A, Thm. A.3, p.226][MilneCFT];
[Serre 1979, Chap. X, §3, p.155][Serre1979];
[Yamaguchi 2026, `KummerTheory/Concrete/FiniteCharacterEquiv.lean:32`][Yamaguchi2026]). -/
def kummerRadicalSubgroup (n : ℕ) : Subgroup Kˣ where
  carrier := {a | ∃ β : Lˣ, β ^ n = Units.map (algebraMap K L).toMonoidHom a}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro a b ⟨β, hβ⟩ ⟨γ, hγ⟩
    exact ⟨β * γ, by rw [mul_pow, hβ, hγ, ← map_mul]⟩
  inv_mem' := by
    rintro a ⟨β, hβ⟩
    exact ⟨β⁻¹, by rw [inv_pow, hβ, ← map_inv]⟩

/-- Membership in the Kummer radical subgroup is the defining root, definitionally
([Milne 2020, Chap. VII, App. A, Thm. A.3, p.226][MilneCFT]). -/
theorem mem_kummerRadicalSubgroup_iff (n : ℕ) {a : Kˣ} :
    a ∈ kummerRadicalSubgroup K L n ↔
      ∃ β : Lˣ, β ^ n = Units.map (algebraMap K L).toMonoidHom a :=
  Iff.rfl

end Atlas.Knowledge
