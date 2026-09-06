import Mathlib
import Atlas.Knowledge.FiniteLocalReciprocityLaw
import Atlas.Knowledge.IsMixedCharLocalField
import Atlas.Knowledge.NormQuotient

/-!
# norm index of an abelian extension

The norm index of a finite abelian extension of mixed-characteristic local fields is
its degree: `#(Kˣ ⧸ N Lˣ) = [L : K]`. This is the cardinality summit of finite local
reciprocity — `Kˣ/N Lˣ ≅ Gal(L/K)ᵃᵇ`, the layer's
`Atlas.Knowledge.abelianizationEquivNormQuotient` — read off once the Galois group is
abelian: the abelianization is the group, and the group has the degree's order. The
abelian ascent of `Atlas.Knowledge.normIndexCyclic`, whose cyclic case the elementary
tower argument reaches; the abelian case needs the reciprocity map, and now has it.

## Main statements

* `normIndexAbelian` — `#(Kˣ ⧸ N Lˣ) = [L : K]` for finite abelian `L/K`; proved.

## Implementation notes

The statement mirrors `Atlas.Knowledge.normIndexCyclic` in its conclusion, with the
generator hypothesis replaced by Mathlib's `IsAbelianGalois` and the field variables
kept explicit, nothing being left to infer them from. Two things changed when the
proof arrived. The two fields share one universe — the layer's convention for its
local-field items, `Atlas.Knowledge.NormQuotient` binding them so — where the
recorded form had two; and the local-field structure the recorded form hypothesized
on `L`, its valuative relation, topology, extension compatibility, and local-field
class, is shed, since reciprocity needs none of it, which strengthens the claim. The
Lubin–Tate norm-subgroup description consumes it through the index squeeze at the
level field, which lives in one universe with the base, so the narrowed form
instantiates there as before. The proof is a definitional identity and three
cardinality transports: the quotient by the norm range is
`Atlas.Knowledge.NormQuotient` definitionally, the reciprocity law identifies it with
the abelianized Galois group, `Abelianization.equivOfComm` collapses that to the
group, and `IsGalois.card_aut_eq_finrank` counts it.

## References

* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

open scoped IsMulCommutative

universe u

variable (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsMixedCharLocalField K]
variable (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]

/-- **The norm index of a finite abelian extension is its degree** — the cardinality
form of finite local reciprocity, the abelian ascent of
`Atlas.Knowledge.normIndexCyclic`
([Milne 2020, Chap. I, §1, Thm. 1.1, p.20][MilneCFT]; Yamaguchi 2026,
`LocalClassFieldTheory/Finite/UnramifiedConductor.lean:94`,
`card_normQuotient_eq_finrank_of_isAbelianGalois`). -/
theorem normIndexAbelian :
    Nat.card (Kˣ ⧸ (Units.map (Algebra.norm K : L →* K)).range) =
      Module.finrank K L := by
  calc
    Nat.card (Kˣ ⧸ (Units.map (Algebra.norm K : L →* K)).range)
        = Nat.card (NormQuotient K L) := rfl
    _ = Nat.card (Abelianization (L ≃ₐ[K] L)) :=
        Nat.card_congr (abelianizationEquivNormQuotient K L).toEquiv.symm
    _ = Nat.card (L ≃ₐ[K] L) :=
        Nat.card_congr
          (Abelianization.equivOfComm : (L ≃ₐ[K] L) ≃* Abelianization (L ≃ₐ[K] L)).toEquiv.symm
    _ = Module.finrank K L := IsGalois.card_aut_eq_finrank K L

end Atlas.Knowledge
