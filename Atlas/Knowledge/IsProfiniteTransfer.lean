import Mathlib

/-!
# profinite transfer

The transfer (Verlagerung) of a profinite group into an open subgroup, as a characterization:
`IsProfiniteTransfer G H V` says the homomorphism `V : G^ab → H^ab` between the topological
abelianizations—the quotients by the first terms of `Atlas.Knowledge.ClosedDerivedSeries`—is
continuous and descends Mathlib's `MonoidHom.transfer`. Out of `G` itself the transfer needs no
construction: `MonoidHom.transfer` asks only for finite index, which openness in a compact group
supplies, so the coset-representative map of the source is Mathlib's map applied as it stands.
What is not free is the descent: the map factors through the quotient by the closed commutator
subgroup exactly because it is continuous, and that continuity is a theorem, so the descended
map is not defined—a definition may not carry a `sorry`—and every consumer takes a `V` with this
predicate instead, the device of `Atlas.Knowledge.IsLocalReciprocity`. Existence is the recorded
claim; uniqueness is proved. The agreement with the finite quotients, the classical reading of
the Verlagerung, is the derived recorded claim `IsProfiniteTransfer.finiteLevel`. This is the
profinite counterpart of the finite-level arrow `Atlas.Knowledge.AbelianizedGaloisTransfer`; on
the absolute Galois group of a mixed-characteristic local field it is the vertical of the
class-field-theory square `Atlas.Knowledge.ArtinMapProfiniteTransferNaturality`, and its
injectivity for a finite extension is the deliberately unstated gate of
`Atlas.Knowledge.CompletedUnitGroup`.

## Main definitions

* `IsProfiniteTransfer` — continuity, and the descent of `MonoidHom.transfer` through the
  topological abelianization of `G`.

## Main statements

* `exists_isProfiniteTransfer` — the transfer of a profinite group into an open subgroup
  descends. Claim recorded ahead of its proof.
* `IsProfiniteTransfer.unique` — the characterization pins the map. Proved.
* `IsProfiniteTransfer.finiteLevel` — along every finite quotient, the map agrees with the
  transfer of the finite levels. Claim recorded ahead of its proof.

## Implementation notes

The `transfer` field compares `V` with `MonoidHom.transfer` of the projection of `↥H` onto its
topological abelianization; the finite-index instance the transfer wants enters as a binder
inside the quantifier rather than through `[CompactSpace G]` on the structure, because the
structure must elaborate over `Field.absoluteGaloisGroup`, through which compactness does not
synthesize—the note of `Atlas.Knowledge.IsLocalReciprocity`—and openness of `H` in a compact
`G` supplies the instance, so nothing is asserted away. The same device puts `[Finite (G ⧸ N)]`
inside the quantifier of `finiteLevel`, which is in the ∀-lift form of
`Atlas.Knowledge.IsArtinRestriction`: it ranges over every representative `t` of the value of
`V` at the class of `g` and compares images in the abelianization of the finite level, so the
statement constructs no descended homomorphism; that all lifts land equally—the kernel of the
level projection is open, hence closed, and contains the commutators—is the claim's business,
not the statement's, and the agreement itself is the passage of a transversal of `H` in `G` to
a transversal of the level, which the containment of the level in `H` makes bijective.
Existence carries the real content of the source's definition: the transfer kills the closed
commutator subgroup of `G` and the descended map is continuous, which is what lets the source
write the Verlagerung on `G^ab` at all. It spells profiniteness
`[CompactSpace G] [TotallyDisconnectedSpace G]`, Hausdorffness following for a topological
group. Uniqueness needs only compactness: openness gives `H` finite index, the transfer field
then fixes the value at every class, and the projection is surjective—which is the proof.

## References

* [NeukirchEtAl2008] J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of number fields*,
  Grundlehren der mathematischen Wissenschaften **323**, Springer Berlin Heidelberg, 2008.
* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

namespace Atlas.Knowledge

/-- The **profinite transfer** characterization: `V : G^ab → H^ab` between the topological
abelianizations is continuous and descends the transfer—the value of `V` at the class of `g`
is Mathlib's `MonoidHom.transfer` at `g`
([Neukirch–Schmidt–Wingberg 2008, Chap. I, §5, p.52][NeukirchEtAl2008] for the continuous
homomorphism between the quotients by the closed commutator subgroups;
[Serre 1979, Chap. VII, §8, Prop. 7, p.121][Serre1979] for the transfer of a subgroup of
finite index). -/
structure IsProfiniteTransfer (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H : Subgroup G) (V : TopologicalAbelianization G →* TopologicalAbelianization ↥H) :
    Prop where
  /-- The transfer is continuous for the quotient topologies of the abelianizations. -/
  continuous : Continuous V
  /-- The map descends Mathlib's transfer: the value of `V` at the class of `g` is
  `MonoidHom.transfer` of the projection of `↥H` onto its topological abelianization, at `g`. -/
  transfer : ∀ [H.FiniteIndex] (g : G),
    V (QuotientGroup.mk g)
      = MonoidHom.transfer (QuotientGroup.mk' (commutator ↥H).topologicalClosure) g

/-- The transfer of a profinite group into an open subgroup descends: some continuous
`V : G^ab → H^ab` takes each class to the transfer of a representative. Claim recorded ahead
of its proof ([Neukirch–Schmidt–Wingberg 2008, Chap. I, §5, p.52][NeukirchEtAl2008]). -/
theorem exists_isProfiniteTransfer (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (H : Subgroup G) (hH : IsOpen (H : Set G)) :
    ∃ V : TopologicalAbelianization G →* TopologicalAbelianization ↥H,
      IsProfiniteTransfer G H V := by
  sorry

/-- The characterization pins the map: two homomorphisms satisfying it are equal—openness in
the compact `G` gives `H` finite index, the transfer field fixes the value at every class, and
the projection is surjective. -/
theorem IsProfiniteTransfer.unique {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] {H : Subgroup G} (hH : IsOpen (H : Set G))
    {V W : TopologicalAbelianization G →* TopologicalAbelianization ↥H}
    (hV : IsProfiniteTransfer G H V) (hW : IsProfiniteTransfer G H W) : V = W := by
  haveI : Finite (G ⧸ H) := Subgroup.quotient_finite_of_isOpen H hH
  haveI : H.FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  ext x
  exact (hV.transfer x).trans (hW.transfer x).symm

/-- Along the finite quotient by an open normal `N ≤ H`, the profinite transfer agrees with
the transfer of the finite levels: for `g` in `G` and every representative `t ∈ H` of the
value of `V` at the class of `g`, the image of `t` in the abelianization of the level of `H`
is the `MonoidHom.transfer` of the level of `g`. Claim recorded ahead of its proof
([Serre 1979, Chap. VII, §8, Prop. 7, p.121][Serre1979] for the transfer of the finite levels;
[Neukirch–Schmidt–Wingberg 2008, Chap. I, §5, p.52][NeukirchEtAl2008]; the agreement is the
passage of a transversal to the quotients, per the implementation notes). -/
theorem IsProfiniteTransfer.finiteLevel {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {H : Subgroup G}
    {V : TopologicalAbelianization G →* TopologicalAbelianization ↥H}
    (hV : IsProfiniteTransfer G H V) :
    ∀ (N : OpenNormalSubgroup G) [Finite (G ⧸ (N : Subgroup G))],
      (N : Subgroup G) ≤ H → ∀ (g : G) (t : ↥H),
        (QuotientGroup.mk t : TopologicalAbelianization ↥H) = V (QuotientGroup.mk g) →
        letI : (Subgroup.map (QuotientGroup.mk' (N : Subgroup G)) H).FiniteIndex :=
          Subgroup.finiteIndex_of_finite
        Abelianization.of
            ⟨QuotientGroup.mk' (N : Subgroup G) (t : G), Subgroup.mem_map_of_mem _ t.2⟩
          = MonoidHom.transfer
              (Abelianization.of (G := ↥(Subgroup.map (QuotientGroup.mk' (N : Subgroup G)) H)))
              (QuotientGroup.mk g) := by
  sorry

end Atlas.Knowledge
