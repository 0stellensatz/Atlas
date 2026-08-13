import Mathlib
import Atlas.Knowledge.FreeFiltered
import Atlas.Knowledge.IsJumpPair

/-!
# jump-set vector

The two translations between jump-set combinatorics and vectors of the free models. A jump pair
`(I, β)`—carried as its graph, as everywhere in the jump-set layer—determines the vector
`v_{(I, β)}` of a free model whose coordinate at the first copy of each level `i ∈ I` is
`π^{β (i)}` and whose other coordinates vanish; these are the normal forms among which every
filtered-automorphism orbit lands exactly once, which is the content of
`Atlas.Knowledge.FiltOrd`. In the other direction, a vector determines the graph of the
valuations of its coordinates, level by level; its `≤_ρ`-minimal points are what the source's
coordinate recipe for `filt-ord` reads off.

## Main definitions

* `jumpSetVector` — the vector `v_{(I, β)}` of a jump pair.
* `jumpSetVector.beta` — the multiplicity `β (i)` read off the graph, `0` off the index set.
* `coordGraph` — the graph of coordinate valuations of a vector.

## Main statements

* `jumpSetVector.beta_eq` — on a jump pair the read-off multiplicity is the recorded one.

## Implementation notes

`coordGraph` records one point per nonzero coordinate, so a level carrying several nonzero
coordinates contributes several points with one first component; the `≤_ρ`-minimal points of
such a graph are exactly those of the level-wise minimal valuations, so nothing downstream
needs the deduplication. The valuation is truncated into `ℕ+` by `Nat.toPNat'`, which junks the
unit coordinates a vector of `π M` never has.

## References

* [Pagano2022] C. Pagano, *Jump sets in local fields*, J. Algebra **593** (2022), 398–476.
-/

namespace Atlas.Knowledge

open IsDiscreteValuationRing

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The multiplicity `β (i)` read off the graph of a jump pair: the largest second component
sitting over `i`, and `0` when none does ([Pagano 2022, Def. 3.32, p.431][Pagano2022]). -/
def jumpSetVector.beta (P : Finset (ℕ+ × ℕ+)) (i : ℕ+) : ℕ :=
  (P.filter fun p => p.1 = i).sup fun p => (p.2 : ℕ)

/-- On a jump pair the read-off multiplicity at a first component is the recorded second
component: first components determine points. -/
theorem jumpSetVector.beta_eq {ρ : Shift} {S : Set ℕ+} {P : Finset (ℕ+ × ℕ+)}
    (hP : IsJumpPair ρ S P) {p : ℕ+ × ℕ+} (hp : p ∈ P) : jumpSetVector.beta P p.1 = (p.2 : ℕ) := by
  unfold jumpSetVector.beta
  refine le_antisymm (Finset.sup_le fun r hr => ?_) ?_
  · rw [Finset.mem_filter] at hr
    rw [hP.eq_of_fst_eq hr.1 hp hr.2]
  · refine Finset.le_sup (f := fun q : ℕ+ × ℕ+ => ((q.2 : ℕ+) : ℕ)) ?_
    rw [Finset.mem_filter]
    exact ⟨hp, rfl⟩

/-- The vector `v_{(I, β)}` of a jump pair in the free model over the index `D`: `π^{β (i)}` on
the first copy of each level `i ∈ I`, `0` elsewhere
([Pagano 2022, Def. 3.32, p.431][Pagano2022]). -/
def jumpSetVector (π : R) (D : Finset (ℕ+ × ℕ)) (P : Finset (ℕ+ × ℕ+)) : ↥D → R :=
  fun j =>
    if j.1.2 = 0 ∧ j.1.1 ∈ P.image Prod.fst then π ^ jumpSetVector.beta P j.1.1 else 0

open Classical in
/-- The graph of coordinate valuations of a vector of a free model: one point `(level, ord)`
per nonzero coordinate. Its `≤_ρ`-minimal points are what the source's coordinate recipe for
`filt-ord` consumes ([Pagano 2022, §1.2, p.405][Pagano2022]). -/
noncomputable def coordGraph {D : Finset (ℕ+ × ℕ)} (v : ↥D → R) : Finset (ℕ+ × ℕ+) :=
  (Finset.univ.filter fun j : ↥D => v j ≠ 0).image fun j =>
    (j.1.1, ((addVal R (v j)).toNat.toPNat' : ℕ+))

theorem mem_coordGraph {D : Finset (ℕ+ × ℕ)} {v : ↥D → R} {p : ℕ+ × ℕ+} :
    p ∈ coordGraph v ↔
      ∃ j : ↥D, v j ≠ 0 ∧ j.1.1 = p.1 ∧ ((addVal R (v j)).toNat.toPNat' : ℕ+) = p.2 := by
  classical
  simp only [coordGraph, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, rfl, rfl⟩
  · rintro ⟨j, hj, h1, h2⟩
    exact ⟨j, hj, Prod.ext h1 h2⟩

/-- The first components of the coordinate graph over the free index lie in `T ρ`: the levels
do ([Pagano 2022, §3.3.5, p.430][Pagano2022]). -/
theorem coordGraph_fst_mem_T {ρ : Shift} (hρ : (Shift.T ρ).Finite) {f : ℕ}
    {v : ↥(Shift.freeIndex hρ f) → R} {p : ℕ+ × ℕ+} (hp : p ∈ coordGraph v) :
    p.1 ∈ Shift.T ρ := by
  obtain ⟨j, -, h1, -⟩ := mem_coordGraph.mp hp
  have hj : j.1 ∈ hρ.toFinset ×ˢ Finset.range f := j.2
  rw [Finset.mem_product] at hj
  rw [← h1]
  exact hρ.mem_toFinset.mp hj.1

/-- The first components of the coordinate graph over the star index lie in `T*_ρ`
([Pagano 2022, §3.3.5, p.430][Pagano2022]). -/
theorem coordGraph_fst_mem_T_star {ρ : Shift} (hρ : (Shift.T ρ).Finite) {f : ℕ}
    {v : ↥(Shift.starIndex hρ f) → R} {p : ℕ+ × ℕ+} (hp : p ∈ coordGraph v) :
    p.1 ∈ Shift.T_star ρ hρ := by
  obtain ⟨j, -, h1, -⟩ := mem_coordGraph.mp hp
  have hj : j.1 ∈ Shift.freeIndex hρ f ∪ {(Shift.e_star ρ hρ, 0)} := j.2
  rw [Finset.mem_union] at hj
  rw [← h1]
  rcases hj with hj | hj
  · have hj' : j.1 ∈ hρ.toFinset ×ˢ Finset.range f := hj
    rw [Finset.mem_product] at hj'
    exact Or.inl (hρ.mem_toFinset.mp hj'.1)
  · rw [Finset.mem_singleton] at hj
    right
    rw [hj]
    rfl

end Atlas.Knowledge
