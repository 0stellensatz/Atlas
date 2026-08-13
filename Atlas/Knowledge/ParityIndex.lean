import Mathlib

/-!
# parity index

The **parity index** of a natural number: `1` if it is odd and `2` if it is even. Applied to the
residue characteristic `Atlas.Knowledge.ResidueCharacteristic` of a mixed-characteristic local
field it is the invariant `ε_K`, the correction separating `p = 2` from the odd-`p` case in the
group-theoretic recovery of the other invariants.

## Main definitions

* `parityIndex` — `if Even n then 2 else 1`.

## References

* [Hyeon2025] S.-H. Hyeon, *The m-step solvable anabelian geometry of mixed-characteristic local
  fields*, J. London Math. Soc. **112** (2025), e70402.
-/

namespace Atlas.Knowledge

/-- The **parity index** of a natural number: `1` if odd, `2` if even. Applied to the residue
characteristic of a mixed-characteristic local field it is the invariant `ε_K`
([Hyeon 2025, §3, p.9][Hyeon2025]). -/
def parityIndex (n : ℕ) : ℕ :=
  if Even n then 2 else 1

theorem parityIndex_of_even {n : ℕ} (h : Even n) : parityIndex n = 2 :=
  if_pos h

theorem parityIndex_of_odd {n : ℕ} (h : Odd n) : parityIndex n = 1 :=
  if_neg (Nat.not_even_iff_odd.mpr h)

end Atlas.Knowledge
