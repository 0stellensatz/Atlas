import Mathlib

/-!
# transfer and postcomposition

Postcomposition of a homomorphism from a finite-index subgroup to a commutative group commutes
with group transfer. This identifies the two placements of a Galois-group equivalence in
`Atlas.Knowledge.AbelianizedGaloisTransfer`: inside the transferred map or after transfer.

## Main statements

* `transfer_comp` — transfer commutes with postcomposition.

## Implementation notes

The proof is the product formula defining Mathlib's `MonoidHom.transfer`, with
`MonoidHom.map_prod` distributing the homomorphism over the transversal product.
-/

namespace Atlas.Knowledge

/-- Postcomposition commutes with Mathlib's `MonoidHom.transfer`. -/
theorem transfer_comp
    {G A B : Type*} [Group G] [CommGroup A] [CommGroup B]
    {H : Subgroup G} [H.FiniteIndex] (f : H →* A) (g : A →* B) :
    MonoidHom.transfer (g.comp f) = g.comp (MonoidHom.transfer f) := by
  ext x
  simp only [MonoidHom.transfer, MonoidHom.coe_mk, OneHom.coe_mk,
    MonoidHom.comp_apply, Subgroup.leftTransversals.diff, map_prod]

end Atlas.Knowledge
