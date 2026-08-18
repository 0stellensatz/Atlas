import Mathlib

/-!
# absolute Galois group of a subextension

The fixing subgroup of a subextension is the absolute Galois group of the subextension: for an
intermediate field `l` of the algebraic closure of `k`, the subgroup of
`Field.absoluteGaloisGroup k` fixing `l` pointwise, in its subspace topology, is topologically
isomorphic to `Field.absoluteGaloisGroup ↥l`. Combined with the infinite Galois
correspondence—in characteristic zero every open subgroup is the fixing subgroup of a finite
subextension, proved here from Mathlib's `InfiniteGalois`—this is the identification of open
subgroups of the absolute Galois group with absolute Galois groups of finite extensions, the
mechanism by which a group-theoretic statement about open subgroups becomes a field-theoretic
statement about finite extensions, as in the level identity of
`Atlas.Knowledge.MStepSolvableSubextension`.

## Main statements

* `absoluteGaloisSubextension_continuousMulEquiv` — the fixing subgroup of `l` is the absolute
  Galois group of `l`, topologically. Claim recorded ahead of its proof.
* `AbsoluteGaloisSubextension.exists_fixingSubgroup_of_isOpen` — in characteristic zero, an
  open subgroup is the fixing subgroup of a finite subextension. Proved.

## Implementation notes

The isomorphism claim is `Nonempty`-shaped because it conjugates a choice: `AlgebraicClosure
↥l` and `AlgebraicClosure k` are two algebraic closures of `l`, identified by an `l`-algebra
isomorphism that exists but is not canonical. The topological content is that the subspace
topology on the fixing subgroup is its own Krull topology. No hypothesis on `k` is needed for
the isomorphism; the open-subgroup dictionary does need the Galois correspondence, so it asks
for `CharZero`, which makes the algebraic closure Galois over `k`—the layer applies it to
mixed-characteristic local fields only. The dictionary produces the fixing subgroup equal to
the given subgroup, not merely isomorphic, so consumers can rewrite along it.

## References

* [MilneFT] J. S. Milne, *Fields and Galois theory* (v5.10), available at www.jmilne.org/math/,
  2022.
* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The fixing subgroup of a subextension `l`, in its subspace topology, is the absolute Galois
group of `l`: restriction of scalars along `k ⊆ l` and a choice of `l`-isomorphism of
algebraic closures exhibit `Gal (k̄ / l)` as `Field.absoluteGaloisGroup ↥l`. Claim recorded
ahead of its proof ([Milne 2022, Chap. 7, Prop. 7.12, p.97][MilneFT]). -/
theorem absoluteGaloisSubextension_continuousMulEquiv (k : Type*) [Field k]
    (l : IntermediateField k (AlgebraicClosure k)) :
    Nonempty (↥l.fixingSubgroup ≃ₜ* Field.absoluteGaloisGroup ↥l) := by
  sorry

namespace AbsoluteGaloisSubextension

/-- In characteristic zero, an open subgroup of the absolute Galois group is the fixing
subgroup of a finite subextension: its fixed field is finite-dimensional over `k` and cuts it
back out. With `absoluteGaloisSubextension_continuousMulEquiv` this identifies open subgroups
with absolute Galois groups of finite extensions
([Milne 2022, Chap. 7, Thm. 7.13, p.98][MilneFT]; [Hyeon 2025, §2, p.8][Hyeon2025]). -/
theorem exists_fixingSubgroup_of_isOpen (k : Type*) [Field k] [CharZero k]
    {H : Subgroup (Field.absoluteGaloisGroup k)}
    (hH : IsOpen (H : Set (Field.absoluteGaloisGroup k))) :
    ∃ l : IntermediateField k (AlgebraicClosure k),
      FiniteDimensional k ↥l ∧ l.fixingSubgroup = H := by
  have hc : IsClosed (H : Set (Field.absoluteGaloisGroup k)) := Subgroup.isClosed_of_isOpen H hH
  have hfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hc⟩
  refine ⟨IntermediateField.fixedField H, ?_, hfix⟩
  exact (InfiniteGalois.isOpen_iff_finite (IntermediateField.fixedField H)).mp
    (by rw [hfix]; exact hH)

end AbsoluteGaloisSubextension

end Atlas.Knowledge
