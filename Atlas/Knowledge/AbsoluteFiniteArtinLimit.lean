import Mathlib
import Atlas.Knowledge.AbsoluteAbelianizationEquiv

/-!
# absolute finite Artin limit

The abelianized absolute Galois group of a characteristic-zero field is
profinite, so it is recovered as the inverse limit of its quotients by
open normal subgroups: the limit object, bundled in `ProfiniteGrp`, and
the canonical topological identification of the abelianization with it
— the target vocabulary in which the absolute Artin map is assembled
coordinate by coordinate (#104).

## Main definitions

* `absoluteFiniteArtinLimit` — the inverse limit of the finite
  quotients, as a profinite group.
* `absoluteGaloisAbelianizationLimitEquiv` — the canonical
  identification of the abelianization with the limit.

## Implementation notes

The continuity fork of the arc, first: the layer strips continuity of
the reciprocity homomorphisms but keeps topological objects and
identifications, and this file is wholly on the kept side — the limit
object and the limit identification port with their topology intact, as
the dictionary's `≃ₜ*` did on
`Atlas.Knowledge.AbsoluteFiniteQuotientEquiv`; the stripping resumes on
`Atlas.Knowledge.AbsoluteFiniteArtinLimitMap`. The source builds the
limit over its bundle `localAbsoluteAbelianProfinite` (its
`LocalClassFieldTheory/Infinite/AbsoluteFiniteQuotients.lean:26`),
which the layer's dictionary dropped; the layer re-bundles inline as
`ProfiniteGrp.of` of Mathlib's topological group
`Field.absoluteGaloisGroupAbelianization K`, elaborating through the
compactness and total-disconnectedness instances recorded on
`Atlas.Knowledge.AbsoluteAbelianizationEquiv`. The variable block is
the dictionary's `[CharZero K]` split rather than the consuming Artin
homomorphism's local-field block: nothing here reads the finite
reciprocity law, and the limit machinery forces nothing beyond the
bundling instances — the ambient conversion of the arc as recorded on
the dictionary. Current Mathlib names the source's composite diagram
`toFiniteQuotientFunctor ⋙ forget₂ FiniteGrp ProfiniteGrp` as
`ProfiniteGrp.diagram`; the layer keeps the source's spelling, to which
the named form is definitionally equal, so the identification's stated
target `absoluteFiniteArtinLimit K` unifies with the codomain
`ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor` states
through `ProfiniteGrp.diagram` by unfolding. Everything else ports
token-for-token; the file is the source's
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:109`–`:120`.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

open CategoryTheory

variable (K : Type*) [Field K] [CharZero K]

/-- The inverse limit of the quotients of the abelianized absolute
Galois group by its open normal subgroups, as a profinite group — the
target in which the finite Artin coordinates assemble ([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:109`]
[Yamaguchi2026]). -/
noncomputable def absoluteFiniteArtinLimit : ProfiniteGrp :=
  ProfiniteGrp.limit
    ((ProfiniteGrp.of (Field.absoluteGaloisGroupAbelianization K)).toFiniteQuotientFunctor ⋙
      forget₂ FiniteGrp ProfiniteGrp)

/-- **The topological abelianization of the absolute Galois group is
canonically the inverse limit of all of its finite quotients**
([Yamaguchi 2026,
`LocalClassFieldTheory/Infinite/AbsoluteArtin.lean:116`]
[Yamaguchi2026]). -/
noncomputable def absoluteGaloisAbelianizationLimitEquiv :
    Field.absoluteGaloisGroupAbelianization K ≃ₜ* absoluteFiniteArtinLimit K :=
  ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor
    (ProfiniteGrp.of (Field.absoluteGaloisGroupAbelianization K))

end

end Atlas.Knowledge
