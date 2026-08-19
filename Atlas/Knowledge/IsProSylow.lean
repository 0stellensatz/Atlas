import Mathlib

/-!
# pro-p Sylow subgroup

The **pro-`p` Sylow subgroups** of a profinite group, as a characterization: `IsProSylow p G S`
says the subgroup is closed and lands on a `p`-Sylow subgroup of every finite level `G ⧸ N`.
This is the source's definition—closed, pro-`p`, index prime to `p`—without the supernatural
arithmetic: a closed subgroup is the limit of its level images, so it is pro-`p` exactly when
those images are `p`-groups, and its index is prime to `p` exactly when every level index is,
which Sylow-ness at every level packages; the source's own existence proof runs level-wise, and
the image of a Sylow subgroup under a surjection onto a further level is again one. Existence
and conjugacy are the recorded claims. Uniqueness in the abelian case is proved from conjugacy,
and is the form the layer consumes: the torsion-level Sylow readings of
`Atlas.Knowledge.GroupRootOfUnityExponent` and `Atlas.Knowledge.GroupAbsoluteInertiaDegree`,
and, one gate ahead, the group-theoretic wild inertia of an MLF-type group
`Atlas.Knowledge.IsMLFType`—the source's *unique* pro-`p` Sylow subgroup of the inertia part,
whose field-side counterpart is `Atlas.Knowledge.WildInertiaSubgroup`.

## Main definitions

* `IsProSylow` — closed, and a `p`-Sylow subgroup on every finite level.

## Main statements

* `exists_isProSylow` — every profinite group has a pro-`p` Sylow subgroup. Claim recorded
  ahead of its proof.
* `IsProSylow.conj` — any two are conjugate. Claim recorded ahead of its proof.
* `IsProSylow.unique` — in an abelian profinite group the pro-`p` Sylow subgroup is unique.
  Proved, from the conjugacy claim.

## Implementation notes

Sylow-ness of a level image is spelled as equality with a Mathlib `Sylow p` term of the finite
quotient, and the finiteness of each level enters as an instance binder inside the quantifier
rather than as compactness on the structure—the device of `Atlas.Knowledge.IsProfiniteTransfer`,
so the predicate elaborates over any topological group and profiniteness is asked for only by
the claims, where it is load-bearing. The predicate itself asks no primality of `p`: Mathlib's
`Sylow` does not, and the claims restore `[Fact p.Prime]` where the sources say "prime".
Conjugation is spelled `Subgroup.map` along `MulAut.conj`, and `unique` is a complete proof
relative to the conjugacy claim—in an abelian group conjugation is the identity—so it inherits
that claim's `sorry` through the call, which is how a derived statement stands on recorded
backlog. The full decomposition of a profinite abelian group as the product of its pro-`p`
Sylow subgroups is deliberately not recorded: no source at hand states it, and the layer
consumes only uniqueness and the finite-torsion readings.

## References

* [NeukirchEtAl2008] J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of number fields*,
  Grundlehren der mathematischen Wissenschaften **323**, Springer Berlin Heidelberg, 2008.
* [Serre1994] J-P. Serre, *Cohomologie galoisienne*, Lecture Notes in Mathematics **5**,
  Springer-Verlag Berlin Heidelberg, fifth edition, 1994.
-/

namespace Atlas.Knowledge

/-- The **pro-`p` Sylow subgroup** characterization: the subgroup is closed, and its image in
the quotient by every open normal subgroup with finite quotient is a `p`-Sylow subgroup of
that quotient ([Neukirch–Schmidt–Wingberg 2008, Chap. I, §6, Def. (1.6.8),
p.69][NeukirchEtAl2008]; [Serre 1994, Chap. I, §1.4, p.5][Serre1994]; the level-wise reading
is the source's own construction, per the implementation notes). -/
structure IsProSylow (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] (S : Subgroup G) :
    Prop where
  isClosed : IsClosed (S : Set G)
  isSylow_map : ∀ N : OpenNormalSubgroup G, ∀ [Finite (G ⧸ (N : Subgroup G))],
    ∃ P : Sylow p (G ⧸ (N : Subgroup G)),
      Subgroup.map (QuotientGroup.mk' (N : Subgroup G)) S = ↑P

/-- Every profinite group has a pro-`p` Sylow subgroup. Claim recorded ahead of its proof
([Neukirch–Schmidt–Wingberg 2008, Chap. I, §6, Thm. (1.6.9) (i), p.69][NeukirchEtAl2008];
[Serre 1994, Chap. I, §1.4, Prop. 3, p.5][Serre1994]). -/
theorem exists_isProSylow (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] :
    ∃ S : Subgroup G, IsProSylow p G S := by
  sorry

/-- Any two pro-`p` Sylow subgroups of a profinite group are conjugate. Claim recorded ahead
of its proof ([Neukirch–Schmidt–Wingberg 2008, Chap. I, §6, Thm. (1.6.9) (iii),
p.69][NeukirchEtAl2008]; [Serre 1994, Chap. I, §1.4, Prop. 3, p.5][Serre1994]). -/
theorem IsProSylow.conj {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {S T : Subgroup G}
    (hS : IsProSylow p G S) (hT : IsProSylow p G T) :
    ∃ g : G, Subgroup.map (MulAut.conj g).toMonoidHom S = T := by
  sorry

/-- In an abelian profinite group the pro-`p` Sylow subgroup is unique: conjugation is the
identity, so the conjugacy `IsProSylow.conj` collapses to equality. Proved from the recorded
conjugacy claim, whose `sorry` it inherits through that use. -/
theorem IsProSylow.unique {p : ℕ} [Fact p.Prime] {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {S T : Subgroup G} (hS : IsProSylow p G S) (hT : IsProSylow p G T) : S = T := by
  obtain ⟨g, hg⟩ := hS.conj hT
  have h : Subgroup.map (MulAut.conj g).toMonoidHom S = S := by ext x; simp
  exact h.symm.trans hg

end Atlas.Knowledge
