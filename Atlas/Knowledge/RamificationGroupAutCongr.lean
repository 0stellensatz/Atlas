import Mathlib
import Atlas.Knowledge.HerbrandPhi
import Atlas.Knowledge.HerbrandPsi
import Atlas.Knowledge.LowerRamificationGroup
import Atlas.Knowledge.RealLowerRamificationGroup
import Atlas.Knowledge.UpperRamificationGroup

/-!
# ramification groups under field isomorphisms

The ramification filtrations are invariants of the extension up to `K`-isomorphism of the top
field: an isomorphism `e : L ≃ₐ[K] L'` conjugates the Galois groups by `AlgEquiv.autCongr e`,
and conjugation carries `G_i (L/K)` onto `G_i (L'/K)`, leaves the Herbrand functions
unchanged, and so carries `G^v (L/K)` onto `G^v (L'/K)`. The layer's concrete extensions are
stated where they are constructed — the Lubin–Tate level fields inside the separable closure,
the cyclotomic floors inside the algebraic closure — and this item is what lets a filtration
computed at one realization be read at another, with its cardinalities.

## Main statements

* `lowerRamificationGroup_map_autCongr` — `G_i` is carried onto `G_i`.
* `herbrandPhi_autCongr` / `herbrandPsi_autCongr` — the Herbrand functions agree.
* `upperRamificationGroup_map_autCongr` — `G^v` is carried onto `G^v`.
* `card_lowerRamificationGroup_autCongr` / `card_upperRamificationGroup_autCongr` — the
  orders agree.

## Implementation notes

The lower groups are defined through `galRestrict` on the integral closure of `𝒪[K]` and the
powers of its Jacobson radical (`Atlas.Knowledge.LowerRamificationGroup`), so the transport
is the isomorphism of integral closures `AlgEquiv.mapIntegralClosure` induced by `e` over
`𝒪[K]`: it intertwines the restricted actions, by the injectivity of the inclusion into the
top field, and it carries radical powers onto radical powers, by
`Ideal.map_jacobson_of_bijective`. One inclusion for an arbitrary `e` and the same inclusion
for `e.symm` give the equality. The Herbrand function is an integral of orders of lower
groups, so it is unchanged once the orders are; `ψ` is its inverse, and `G^v = G_{ψ (v)}`
transports as the lower groups do. The variables are the two algebraic extensions with no
finiteness — `Atlas.Knowledge.herbrandPhi` needs none — and every statement binds `e`
explicitly, since a statement about the two filtrations does not mention it. The three
`card_*` lemmas put `L'` on the left, opposite to the `Subgroup.map` statements: that
orientation is what lets `herbrandPhi_autCongr` rewrite the integrand of `L'`'s Herbrand
function into `L`'s by `simp only`, and a consumer reading them the other way should take
their `symm`. Serre's pages define the filtrations and the Herbrand functions; none states
this invariance, which every citation here says.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
-/

open ValuativeRel

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [ValuativeRel K] {L : Type*} [Field L] [Algebra K L]
  [Algebra.IsAlgebraic K L] {L' : Type*} [Field L'] [Algebra K L'] [Algebra.IsAlgebraic K L']

/- The induced isomorphism of integral closures intertwines the restricted actions. -/
private theorem mapIntegralClosure_galRestrict (e : L ≃ₐ[K] L') (σ : L ≃ₐ[K] L)
    (x : integralClosure 𝒪[K] L) :
    (e.restrictScalars 𝒪[K]).mapIntegralClosure
        (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ x) =
      galRestrict 𝒪[K] K L' (integralClosure 𝒪[K] L') (AlgEquiv.autCongr e σ)
        ((e.restrictScalars 𝒪[K]).mapIntegralClosure x) := by
  apply Subtype.ext
  have h1 := algebraMap_galRestrict_apply (A := 𝒪[K]) (K := K) (L := L)
    (B := integralClosure 𝒪[K] L) σ x
  have h2 := algebraMap_galRestrict_apply (A := 𝒪[K]) (K := K) (L := L')
    (B := integralClosure 𝒪[K] L') (AlgEquiv.autCongr e σ)
    ((e.restrictScalars 𝒪[K]).mapIntegralClosure x)
  change e (algebraMap (integralClosure 𝒪[K] L) L
      (galRestrict 𝒪[K] K L (integralClosure 𝒪[K] L) σ x)) =
    algebraMap (integralClosure 𝒪[K] L') L'
      (galRestrict 𝒪[K] K L' (integralClosure 𝒪[K] L') (AlgEquiv.autCongr e σ)
        ((e.restrictScalars 𝒪[K]).mapIntegralClosure x))
  rw [h1, h2]
  change e (σ (x : L)) = (AlgEquiv.autCongr e σ) (e (x : L))
  rw [AlgEquiv.autCongr_apply, AlgEquiv.trans_apply, AlgEquiv.trans_apply,
    AlgEquiv.symm_apply_apply]

omit [Algebra.IsAlgebraic K L] [Algebra.IsAlgebraic K L'] in
/- The induced isomorphism carries radical powers to radical powers. -/
private theorem mapIntegralClosure_mem_jacobson_pow (e : L ≃ₐ[K] L') {n : ℕ}
    {z : integralClosure 𝒪[K] L}
    (hz : z ∈ Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) ^ n) :
    (e.restrictScalars 𝒪[K]).mapIntegralClosure z ∈
      Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L')) ^ n := by
  have hmem : (e.restrictScalars 𝒪[K]).mapIntegralClosure z ∈
      Ideal.map (((e.restrictScalars 𝒪[K]).mapIntegralClosure).toRingEquiv :
          integralClosure 𝒪[K] L →+* integralClosure 𝒪[K] L')
        (Ideal.jacobson (⊥ : Ideal (integralClosure 𝒪[K] L)) ^ n) :=
    Ideal.mem_map_of_mem _ hz
  have hbij : Function.Bijective
      ⇑(((e.restrictScalars 𝒪[K]).mapIntegralClosure).toRingEquiv :
        integralClosure 𝒪[K] L →+* integralClosure 𝒪[K] L') :=
    ((e.restrictScalars 𝒪[K]).mapIntegralClosure).bijective
  rwa [Ideal.map_pow, Ideal.map_jacobson_of_bijective hbij, Ideal.map_bot] at hmem

/-- Conjugation by a `K`-isomorphism of the top field carries the `i`th lower ramification
group into the `i`th lower ramification group of the other realization
([Serre 1979, Chap. IV, §1, p.62][Serre1979] — the invariance its definition leaves
implicit). -/
theorem lowerRamificationGroup_map_autCongr_le (e : L ≃ₐ[K] L') (i : ℤ) :
    Subgroup.map (AlgEquiv.autCongr e).toMonoidHom (lowerRamificationGroup K L i) ≤
      lowerRamificationGroup K L' i := by
  rintro _ ⟨σ, hσ, rfl⟩
  intro y
  obtain ⟨x, rfl⟩ := (e.restrictScalars 𝒪[K]).mapIntegralClosure.surjective y
  change galRestrict 𝒪[K] K L' (integralClosure 𝒪[K] L') (AlgEquiv.autCongr e σ)
      ((e.restrictScalars 𝒪[K]).mapIntegralClosure x) -
    (e.restrictScalars 𝒪[K]).mapIntegralClosure x ∈ _
  rw [← mapIntegralClosure_galRestrict K e σ x, ← map_sub]
  exact mapIntegralClosure_mem_jacobson_pow K e (hσ x)

/-- **Lower ramification groups transport along field isomorphisms**: conjugation by
`e : L ≃ₐ[K] L'` carries `G_i (L/K)` onto `G_i (L'/K)`
([Serre 1979, Chap. IV, §1, p.62][Serre1979] — the invariance its definition leaves
implicit). -/
theorem lowerRamificationGroup_map_autCongr (e : L ≃ₐ[K] L') (i : ℤ) :
    Subgroup.map (AlgEquiv.autCongr e).toMonoidHom (lowerRamificationGroup K L i) =
      lowerRamificationGroup K L' i := by
  refine le_antisymm (lowerRamificationGroup_map_autCongr_le K e i) ?_
  intro σ' hσ'
  refine ⟨AlgEquiv.autCongr e.symm σ', ?_, ?_⟩
  · exact lowerRamificationGroup_map_autCongr_le K e.symm i ⟨σ', hσ', rfl⟩
  · change AlgEquiv.autCongr e (AlgEquiv.autCongr e.symm σ') = σ'
    rw [← AlgEquiv.autCongr_symm, MulEquiv.apply_symm_apply]

/-- The orders of the lower ramification groups agree across a field isomorphism. -/
theorem card_lowerRamificationGroup_autCongr (e : L ≃ₐ[K] L') (i : ℤ) :
    Nat.card (lowerRamificationGroup K L' i) = Nat.card (lowerRamificationGroup K L i) := by
  rw [← lowerRamificationGroup_map_autCongr K e i]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (AlgEquiv.autCongr e).injective).toEquiv).symm

/-- The real-indexed lower groups transport as the integer-indexed ones do. -/
theorem realLowerRamificationGroup_map_autCongr (e : L ≃ₐ[K] L') (u : ℝ) :
    Subgroup.map (AlgEquiv.autCongr e).toMonoidHom (realLowerRamificationGroup K L u) =
      realLowerRamificationGroup K L' u :=
  lowerRamificationGroup_map_autCongr K e ⌈u⌉

/-- The orders of the real-indexed lower groups agree across a field isomorphism. -/
theorem card_realLowerRamificationGroup_autCongr (e : L ≃ₐ[K] L') (u : ℝ) :
    Nat.card (realLowerRamificationGroup K L' u) =
      Nat.card (realLowerRamificationGroup K L u) :=
  card_lowerRamificationGroup_autCongr K e ⌈u⌉

/-- **The Herbrand function is invariant under field isomorphisms**: it is an integral of
orders of lower groups, which agree ([Serre 1979, Chap. IV, §3, p.73][Serre1979] — the
invariance its definition leaves implicit). -/
theorem herbrandPhi_autCongr (e : L ≃ₐ[K] L') : herbrandPhi K L' = herbrandPhi K L := by
  funext u
  unfold herbrandPhi
  simp only [card_realLowerRamificationGroup_autCongr K e,
    card_lowerRamificationGroup_autCongr K e]

/-- The inverse Herbrand function is invariant under field isomorphisms. -/
theorem herbrandPsi_autCongr (e : L ≃ₐ[K] L') : herbrandPsi K L' = herbrandPsi K L := by
  unfold herbrandPsi
  rw [herbrandPhi_autCongr K e]

/-- **Upper ramification groups transport along field isomorphisms**: conjugation by
`e : L ≃ₐ[K] L'` carries `G^v (L/K)` onto `G^v (L'/K)`
([Serre 1979, Chap. IV, §3, p.74][Serre1979] — the invariance its definition leaves
implicit). -/
theorem upperRamificationGroup_map_autCongr (e : L ≃ₐ[K] L') (v : ℝ) :
    Subgroup.map (AlgEquiv.autCongr e).toMonoidHom (upperRamificationGroup K L v) =
      upperRamificationGroup K L' v := by
  unfold upperRamificationGroup
  rw [herbrandPsi_autCongr K e]
  exact realLowerRamificationGroup_map_autCongr K e _

/-- The orders of the upper ramification groups agree across a field isomorphism. -/
theorem card_upperRamificationGroup_autCongr (e : L ≃ₐ[K] L') (v : ℝ) :
    Nat.card (upperRamificationGroup K L' v) = Nat.card (upperRamificationGroup K L v) := by
  rw [← upperRamificationGroup_map_autCongr K e v]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _
    (AlgEquiv.autCongr e).injective).toEquiv).symm

end Atlas.Knowledge
