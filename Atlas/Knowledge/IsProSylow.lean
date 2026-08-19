import Mathlib

/-!
# pro-p Sylow subgroup

The **pro-`p` Sylow subgroups** of a profinite group, as a characterization: `IsProSylow p G S`
says the subgroup is closed and lands on a `p`-Sylow subgroup of every finite level `G ⧸ N`.
This is the source's definition—closed, pro-`p`, index prime to `p`—without the supernatural
arithmetic: a closed subgroup is the limit of its level images, so it is pro-`p` exactly when
those images are `p`-groups, and its index is prime to `p` exactly when every level index is,
which Sylow-ness at every level packages; the source's own existence proof runs level-wise, and
the image of a Sylow subgroup under a surjection onto a further level is again one
([Serre 1994, Chap. I, §1.4, Prop. 4, p.6][Serre1994]; Mathlib's `Sylow.mapSurjective`).
Existence, conjugacy, and the containment of every pro-`p` subgroup in a Sylow one are the
recorded claims. Uniqueness in the abelian case is proved outright,
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
* `exists_isProSylow_le` — every closed level-wise pro-`p` subgroup is contained in one.
  Claim recorded ahead of its proof.
* `IsProSylow.conj` — any two are conjugate. Claim recorded ahead of its proof.
* `IsProSylow.unique` — in an abelian profinite group the pro-`p` Sylow subgroup is unique.
  Proved.

## Implementation notes

Sylow-ness of a level image is spelled as equality with a Mathlib `Sylow p` term of the finite
quotient, and the finiteness of each level enters as an instance binder inside the quantifier
rather than as compactness on the structure—the device of `Atlas.Knowledge.IsProfiniteTransfer`,
so the predicate elaborates over any topological group and profiniteness is asked for only by
the claims, where it is load-bearing. The predicate itself asks no primality of `p`: Mathlib's
`Sylow` does not, and the claims restore `[Fact p.Prime]` where the sources say "prime".
Conjugation is spelled `Subgroup.map` along `MulAut.conj`, the pro-`p` hypothesis of the
containment claim is spelled level-wise with `IsPGroup`, in the same reading as the
characterization, and `unique` is proved with no recourse to the conjugacy claim: the level
images of two pro-`p` Sylow subgroups are Sylow subgroups of a finite abelian group, hence
equal, and a closed subgroup of a profinite group is the intersection of the open subgroups
containing it. The full decomposition of a profinite abelian group as the product of its
pro-`p` Sylow subgroups is deliberately not recorded: no source at hand states it for
profinite groups—the cited page's `A = ⊕ A(p)` is the decomposition of a discrete abelian
torsion group—and the layer consumes only uniqueness and the finite-torsion readings.

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
  /-- The subgroup is closed. -/
  isClosed : IsClosed (S : Set G)
  /-- On every finite level, the image of the subgroup is a `p`-Sylow subgroup. -/
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

/-- Every closed level-wise pro-`p` subgroup of a profinite group is contained in a pro-`p`
Sylow subgroup. Claim recorded ahead of its proof
([Neukirch–Schmidt–Wingberg 2008, Chap. I, §6, Thm. (1.6.9) (ii), p.69][NeukirchEtAl2008];
[Serre 1994, Chap. I, §1.4, Prop. 4, p.6][Serre1994]). -/
theorem exists_isProSylow_le (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (H : Subgroup G)
    (hH : IsClosed (H : Set G))
    (hp : ∀ N : OpenNormalSubgroup G, ∀ [Finite (G ⧸ (N : Subgroup G))],
      IsPGroup p (Subgroup.map (QuotientGroup.mk' (N : Subgroup G)) H)) :
    ∃ S : Subgroup G, IsProSylow p G S ∧ H ≤ S := by
  sorry

/-- Any two pro-`p` Sylow subgroups of a profinite group are conjugate. Claim recorded ahead
of its proof ([Neukirch–Schmidt–Wingberg 2008, Chap. I, §6, Thm. (1.6.9) (iii),
p.69][NeukirchEtAl2008]; [Serre 1994, Chap. I, §1.4, Prop. 3, p.5][Serre1994]). -/
theorem IsProSylow.conj {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] {S T : Subgroup G}
    (hS : IsProSylow p G S) (hT : IsProSylow p G T) :
    ∃ g : G, Subgroup.map (MulAut.conj g).toMonoidHom S = T := by
  sorry

/-- In an abelian profinite group the pro-`p` Sylow subgroup is unique: on every finite level
the two images are Sylow subgroups of a finite abelian group, hence equal, and a closed
subgroup of a profinite group is the intersection of the open subgroups containing it—which is
the proof, independent of the recorded conjugacy claim. -/
theorem IsProSylow.unique {p : ℕ} [Fact p.Prime] {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {S T : Subgroup G} (hS : IsProSylow p G S) (hT : IsProSylow p G T) : S = T := by
  have main : ∀ S T : Subgroup G, IsProSylow p G S → IsProSylow p G T → T ≤ S := by
    intro S T hS hT
    have hsInf := ProfiniteGrp.closedSubgroup_eq_sInf_open (⟨S, hS.isClosed⟩ : ClosedSubgroup G)
    rw [show ((⟨S, hS.isClosed⟩ : ClosedSubgroup G) : Subgroup G) = S from rfl] at hsInf
    rw [hsInf]
    refine le_sInf fun U hU => ?_
    obtain ⟨hUopen, hSU⟩ := hU
    obtain ⟨M, hMU⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
      ⟨Subgroup.isClosed_of_isOpen U hUopen, hUopen⟩ (one_mem U)
    haveI : Finite (G ⧸ (M : Subgroup G)) :=
      Subgroup.quotient_finite_of_isOpen (M : Subgroup G) M.isOpen
    obtain ⟨PS, hPS⟩ := hS.isSylow_map M
    obtain ⟨PT, hPT⟩ := hT.isSylow_map M
    haveI : Finite (Sylow p (G ⧸ (M : Subgroup G))) :=
      Finite.of_injective_finite_range fun ⦃_ _⦄ h => h
    haveI : Unique (Sylow p (G ⧸ (M : Subgroup G))) :=
      Sylow.unique_of_normal PS (by exact Subgroup.normal_of_isMulCommutative _)
    have hmap : Subgroup.map (QuotientGroup.mk' (M : Subgroup G)) T
        = Subgroup.map (QuotientGroup.mk' (M : Subgroup G)) S := by
      rw [hPT, hPS, Subsingleton.elim PT PS]
    have hle : T ≤ Subgroup.comap (QuotientGroup.mk' (M : Subgroup G))
        (Subgroup.map (QuotientGroup.mk' (M : Subgroup G)) S) := by
      rw [← hmap]
      exact fun x hx => Subgroup.mem_comap.mpr (Subgroup.mem_map_of_mem _ hx)
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at hle
    exact hle.trans (sup_le hSU (SetLike.coe_subset_coe.mp hMU))
  exact le_antisymm (main T S hT hS) (main S T hS hT)

end Atlas.Knowledge
