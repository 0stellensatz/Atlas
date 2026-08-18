import Mathlib

/-!
# profinite transfer

The transfer (Verlagerung) of a profinite group into an open subgroup, as a characterization:
`IsProfiniteTransfer G H V` says the homomorphism `V : G^ab → H^ab` between the topological
abelianizations—the quotients by the first terms of `Atlas.Knowledge.ClosedDerivedSeries`—is
continuous and agrees with Mathlib's `MonoidHom.transfer` on every finite quotient of `G` by an
open normal subgroup contained in `H`. Existence and uniqueness are the recorded claims. The map
itself is not constructed: the coset-representative formula descends to the topological
abelianization only because it is continuous, which is a theorem, and a definition may not carry
a `sorry`—so every consumer takes a `V` with this predicate instead, the device of
`Atlas.Knowledge.IsLocalReciprocity`, and uniqueness makes that unambiguous. This is the
profinite counterpart of the finite-level arrow `Atlas.Knowledge.AbelianizedGaloisTransfer`; on
the absolute Galois group of a mixed-characteristic local field it is the vertical of the
class-field-theory square `Atlas.Knowledge.ArtinMapProfiniteTransferNaturality`, and its
injectivity for a finite extension is the deliberately unstated gate of
`Atlas.Knowledge.CompletedUnitGroup`.

## Main definitions

* `IsProfiniteTransfer` — continuity, and agreement with the finite-level transfer along every
  finite quotient.

## Main statements

Both are claims recorded ahead of their proofs.

* `exists_isProfiniteTransfer` — the transfer of a profinite group into an open subgroup exists.
* `IsProfiniteTransfer.unique` — the characterization pins the map.

## Implementation notes

The finite-level field is in the ∀-lift form of `Atlas.Knowledge.IsArtinRestriction`: it
quantifies over every representative `t` of the value `V (g)` and compares images in the
abelianization of the finite level, so the statement constructs no descended homomorphism; that
all lifts land equally—the kernel of the level projection is closed and contains the
commutators—is the claims' business, not the statement's. At a level `N`, the transfer is
Mathlib's `MonoidHom.transfer` of the abelianization projection of the image of `H`, its finite
index coming from the finiteness of `G ⧸ N`; that finiteness enters as an instance binder
inside the quantifier rather than through `[CompactSpace G]` on the structure, because the
structure must elaborate over `Field.absoluteGaloisGroup`, through which compactness does not
synthesize—the note of `Atlas.Knowledge.IsLocalReciprocity`—and for a profinite `G` every open
normal subgroup has finite quotient, so nothing is asserted away. The two claims spell
profiniteness `[CompactSpace G] [TotallyDisconnectedSpace G]`, Hausdorffness following for a
topological group; openness of `H` gives it finite index and makes the levels `N ≤ H` cofinal
among the open normal subgroups of `H`, which is why the finite levels separate `H^ab` and the
characterization pins the map—the coset-representative formula passes to each finite quotient
because representatives map to representatives, which is the compatibility the field records.

## References

* [NeukirchEtAl2008] J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of number fields*,
  Grundlehren der mathematischen Wissenschaften **323**, Springer Berlin Heidelberg, 2008.
* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

namespace Atlas.Knowledge

/-- The **profinite transfer** characterization: `V : G^ab → H^ab` between the topological
abelianizations is continuous, and along every finite quotient of `G` by an open normal
subgroup `N ≤ H` it agrees with Mathlib's `MonoidHom.transfer`—every representative of a value
of `V` maps at level `N` to the transfer of the argument
([Neukirch–Schmidt–Wingberg 2008, Chap. I, §5, p.52][NeukirchEtAl2008] for the continuous
homomorphism between the quotients by the closed commutator subgroups;
[Serre 1979, Chap. VII, §8, Prop. 7, p.121][Serre1979] for the transfer of the finite
levels). -/
structure IsProfiniteTransfer (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (V : TopologicalAbelianization G →* TopologicalAbelianization ↥H) :
    Prop where
  /-- The transfer is continuous for the quotient topologies of the abelianizations. -/
  continuous : Continuous V
  /-- Along the finite quotient by an open normal `N ≤ H`, the map is the transfer: for `g` in
  `G` and every representative `t ∈ H` of `V (g)`, the image of `t` in the abelianization of
  the level of `H` is the `MonoidHom.transfer` of the level of `g`. -/
  finiteLevel : ∀ (N : OpenNormalSubgroup G) [Finite (G ⧸ (N : Subgroup G))],
    (N : Subgroup G) ≤ H → ∀ (g : G) (t : ↥H),
      (QuotientGroup.mk t : TopologicalAbelianization ↥H) = V (QuotientGroup.mk g) →
      letI : (Subgroup.map (QuotientGroup.mk' (N : Subgroup G)) H).FiniteIndex :=
        Subgroup.finiteIndex_of_finite
      Abelianization.of
          ⟨QuotientGroup.mk' (N : Subgroup G) (t : G), Subgroup.mem_map_of_mem _ t.2⟩
        = MonoidHom.transfer
            (Abelianization.of (G := ↥(Subgroup.map (QuotientGroup.mk' (N : Subgroup G)) H)))
            (QuotientGroup.mk g)

/-- The transfer of a profinite group into an open subgroup exists: some continuous
`V : G^ab → H^ab` agrees with the finite-level transfers. Claim recorded ahead of its proof
([Neukirch–Schmidt–Wingberg 2008, Chap. I, §5, p.52][NeukirchEtAl2008]; the finite-level
agreement is the passage of the coset-representative formula to the quotients, per the
implementation notes). -/
theorem exists_isProfiniteTransfer (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    ∃ V : TopologicalAbelianization G →* TopologicalAbelianization ↥H,
      IsProfiniteTransfer G H V := by
  sorry

/-- The characterization pins the map: two homomorphisms satisfying it are equal, the finite
levels separating `H^ab`. Claim recorded ahead of its proof (the separation is the standard
cofinality argument of the profinite category, per the implementation notes; the map pinned is
that of [Neukirch–Schmidt–Wingberg 2008, Chap. I, §5, p.52][NeukirchEtAl2008]). -/
theorem IsProfiniteTransfer.unique {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {H : Subgroup G} (hH : IsOpen (H : Set G))
    {V W : TopologicalAbelianization G →* TopologicalAbelianization ↥H}
    (hV : IsProfiniteTransfer G H V) (hW : IsProfiniteTransfer G H W) : V = W := by
  sorry

end Atlas.Knowledge
