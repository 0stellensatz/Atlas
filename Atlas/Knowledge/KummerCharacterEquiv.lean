import Mathlib
import Atlas.Knowledge.KummerRadicalSubgroup

/-!
# Kummer character equivalence

The finite Kummer correspondence in its character form, fully proved: for a finite Galois
extension `L / K` whose `n`-th roots of unity all come from the base,

`Δ / (Δ ∩ (Kˣ)ⁿ) ≃* Hom (Gal (L/K), μ_n (L))`,

`Δ` the radical subgroup `Atlas.Knowledge.KummerRadicalSubgroup`. A class of `a` goes to the
character `σ ↦ σ (β) / β` for `β` an `n`-th root of `a` — the literature's `φ_a` — and the
equivalence carries no recorded claim: injectivity is the Galois fixed-field computation,
and surjectivity is Noether's Hilbert 90, which Mathlib provides. The classical texts print
the two halves separately — the absolute character isomorphism and the finite lattice
correspondence — and the finite character packaging is the read repository's; this item
proves it rather than transcribing it.

## Main definitions

* `kummerCharacterEquiv` — the equivalence, assembled from bijectivity.
* `kummerCharacterHom` — the underlying character homomorphism, defined without Galois or
  finiteness hypotheses.

## Main statements

* `kummerCharacterEquiv_apply` / `kummerCharacterHom_apply` — the defining formula
  `σ (β) / β`, quantified over every root `β`, so the interface is choice-free.
* `kummerCharacterHom_injective` / `kummerCharacterHom_surjective` — bijectivity, proved.

## Implementation notes

No multiplicative system of roots exists in general, so the construction chooses a root per
element of `Δ` (`Classical.choose` over the membership's own existence — the legitimate use)
and proves every consumer of the choice independent of it: the one lemma
`character_apply_eq`, root-independence, discharges multiplicativity, descent to the
quotient, and the surjectivity endgame alike. The roots-in-the-base hypothesis is the
literature's `μ_n ⊆ K` restricted to the roots of unity that occur in `L`, stated inline as
a `∀`; every automorphism then fixes `μ_n (L)`, which is what makes the root quotient a
character and the cocycle of Hilbert 90 a homomorphism. Mathlib's
`groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units` has its coboundary
oriented `σ • β / β = f σ`, exactly the root-quotient shape, so surjectivity composes with
no inversion. `Δ ∩ (Kˣ)ⁿ` enters as `subgroupOf` of the range of `powMonoidHom n`, matching
the power-class vocabulary of the Hilbert-symbol items. Only the bijectivity halves and the
equivalence ask for `FiniteDimensional` and `IsGalois`; the homomorphism exists for any
extension, and `n = 0` degenerates consistently throughout.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [MilneCFT] J. S. Milne, *Class field theory* (v4.03), available at www.jmilne.org/math/,
  2020.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

open groupCohomology

namespace Atlas.Knowledge

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

namespace KummerCharacterEquiv

private noncomputable def rootOf {a : Kˣ} (ha : a ∈ kummerRadicalSubgroup K L n) : Lˣ :=
  ((mem_kummerRadicalSubgroup_iff K L n).mp ha).choose

private theorem rootOf_pow {a : Kˣ} (ha : a ∈ kummerRadicalSubgroup K L n) :
    rootOf ha ^ n = Units.map (algebraMap K L).toMonoidHom a :=
  ((mem_kummerRadicalSubgroup_iff K L n).mp ha).choose_spec

private theorem smul_algebraMap_unit (σ : L ≃ₐ[K] L) (c : Kˣ) :
    σ • Units.map (algebraMap K L).toMonoidHom c = Units.map (algebraMap K L).toMonoidHom c := by
  ext
  simp

private theorem smul_div_mem_rootsOfUnity {a : Kˣ} {β : Lˣ}
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) (σ : L ≃ₐ[K] L) :
    σ • β / β ∈ rootsOfUnity n L := by
  rw [mem_rootsOfUnity, div_pow, ← smul_pow', hβ, smul_algebraMap_unit, div_self']

private theorem smul_eq_self_of_pow_eq_one
    (hmu : ∀ u : Lˣ, u ^ n = 1 → ∃ ζ : Kˣ, Units.map (algebraMap K L).toMonoidHom ζ = u)
    (σ : L ≃ₐ[K] L) {u : Lˣ} (hu : u ^ n = 1) : σ • u = u := by
  obtain ⟨ζ, rfl⟩ := hmu u hu
  exact smul_algebraMap_unit σ ζ

private theorem smul_div_eq_smul_div
    (hmu : ∀ u : Lˣ, u ^ n = 1 → ∃ ζ : Kˣ, Units.map (algebraMap K L).toMonoidHom ζ = u)
    (σ : L ≃ₐ[K] L) {β β' : Lˣ} {a : Kˣ}
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a)
    (hβ' : β' ^ n = Units.map (algebraMap K L).toMonoidHom a) :
    σ • β / β = σ • β' / β' := by
  have h1 : (β / β') ^ n = 1 := by rw [div_pow, hβ, hβ', div_self']
  have h2 := smul_eq_self_of_pow_eq_one hmu σ h1
  rw [smul_div'] at h2
  rw [div_eq_div_iff_mul_eq_mul] at h2 ⊢
  rw [h2]
  exact mul_comm _ _

/-- The character attached to one element of the radical subgroup. -/
private noncomputable def character
    (hmu : ∀ u : Lˣ, u ^ n = 1 → ∃ ζ : Kˣ, Units.map (algebraMap K L).toMonoidHom ζ = u)
    (δ : ↥(kummerRadicalSubgroup K L n)) : (L ≃ₐ[K] L) →* ↥(rootsOfUnity n L) :=
  MonoidHom.mk'
    (fun σ => ⟨σ • rootOf δ.2 / rootOf δ.2, smul_div_mem_rootsOfUnity (rootOf_pow δ.2) σ⟩)
    (fun σ τ => Subtype.ext <| by
      change (σ * τ) • rootOf δ.2 / rootOf δ.2
          = σ • rootOf δ.2 / rootOf δ.2 * (τ • rootOf δ.2 / rootOf δ.2)
      have hfix : σ • (τ • rootOf δ.2 / rootOf δ.2) = τ • rootOf δ.2 / rootOf δ.2 :=
        smul_eq_self_of_pow_eq_one hmu σ
          ((mem_rootsOfUnity n _).mp (smul_div_mem_rootsOfUnity (rootOf_pow δ.2) τ))
      have key : (σ * τ) • rootOf δ.2 / rootOf δ.2
          = σ • (τ • rootOf δ.2 / rootOf δ.2) * (σ • rootOf δ.2 / rootOf δ.2) := by
        rw [mul_smul, smul_div', div_mul_div_cancel]
      rw [key, hfix]
      exact mul_comm _ _)

private theorem character_apply_coe
    (hmu : ∀ u : Lˣ, u ^ n = 1 → ∃ ζ : Kˣ, Units.map (algebraMap K L).toMonoidHom ζ = u)
    (δ : ↥(kummerRadicalSubgroup K L n)) (σ : L ≃ₐ[K] L) :
    (character hmu δ σ : Lˣ) = σ • rootOf δ.2 / rootOf δ.2 := rfl

/-- Root-independence: the character computes with any root, not just the chosen one. -/
private theorem character_apply_eq
    (hmu : ∀ u : Lˣ, u ^ n = 1 → ∃ ζ : Kˣ, Units.map (algebraMap K L).toMonoidHom ζ = u)
    {δ : ↥(kummerRadicalSubgroup K L n)} {β : Lˣ}
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom (δ : Kˣ)) (σ : L ≃ₐ[K] L) :
    (character hmu δ σ : Lˣ) = σ • β / β := by
  rw [character_apply_coe]
  exact smul_div_eq_smul_div hmu σ (rootOf_pow δ.2) hβ

private noncomputable def characterHom
    (hmu : ∀ u : Lˣ, u ^ n = 1 → ∃ ζ : Kˣ, Units.map (algebraMap K L).toMonoidHom ζ = u) :
    ↥(kummerRadicalSubgroup K L n) →* ((L ≃ₐ[K] L) →* ↥(rootsOfUnity n L)) :=
  MonoidHom.mk' (character hmu) (fun δ δ' => MonoidHom.ext fun σ => Subtype.ext <| by
    have h : (rootOf δ.2 * rootOf δ'.2) ^ n
        = Units.map (algebraMap K L).toMonoidHom
            ((δ * δ' : ↥(kummerRadicalSubgroup K L n)) : Kˣ) := by
      rw [mul_pow, rootOf_pow δ.2, rootOf_pow δ'.2, ← map_mul, Subgroup.coe_mul]
    calc (character hmu (δ * δ') σ : Lˣ)
        = σ • (rootOf δ.2 * rootOf δ'.2) / (rootOf δ.2 * rootOf δ'.2) :=
          character_apply_eq hmu h σ
      _ = σ • rootOf δ.2 / rootOf δ.2 * (σ • rootOf δ'.2 / rootOf δ'.2) := by
          rw [smul_mul', mul_div_mul_comm]
      _ = ((character hmu δ * character hmu δ') σ : Lˣ) := by
          simp only [MonoidHom.mul_apply, Subgroup.coe_mul, character_apply_coe])

private theorem character_eq_one
    (hmu : ∀ u : Lˣ, u ^ n = 1 → ∃ ζ : Kˣ, Units.map (algebraMap K L).toMonoidHom ζ = u)
    {δ : ↥(kummerRadicalSubgroup K L n)}
    (hδ : δ ∈ (MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ)).subgroupOf
      (kummerRadicalSubgroup K L n)) :
    character hmu δ = 1 := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp (Subgroup.mem_subgroupOf.mp hδ)
  have hc' : c ^ n = (δ : Kˣ) := hc
  have hroot : Units.map (algebraMap K L).toMonoidHom c ^ n
      = Units.map (algebraMap K L).toMonoidHom (δ : Kˣ) := by
    rw [← map_pow, hc']
  refine MonoidHom.ext fun σ => Subtype.ext ?_
  rw [character_apply_eq hmu hroot σ, smul_algebraMap_unit, div_self']
  simp

private theorem exists_algebraMap_unit_eq [FiniteDimensional K L] [IsGalois K L] {u : Lˣ}
    (hfix : ∀ σ : L ≃ₐ[K] L, σ • u = u) :
    ∃ c : Kˣ, Units.map (algebraMap K L).toMonoidHom c = u := by
  have h1 : (u : L) ∈ IntermediateField.fixedField (⊤ : Subgroup (L ≃ₐ[K] L)) :=
    (IntermediateField.mem_fixedField_iff _ _).mpr fun σ _ => congrArg Units.val (hfix σ)
  rw [IsGalois.fixedField_top] at h1
  obtain ⟨c₀, hc₀⟩ := IntermediateField.mem_bot.mp h1
  have hc₀ne : c₀ ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by simpa using hc₀.symm)
  exact ⟨Units.mk0 c₀ hc₀ne, Units.ext hc₀⟩

end KummerCharacterEquiv

open KummerCharacterEquiv

variable (K L)

/-- The **Kummer character homomorphism** `Δ / (Δ ∩ (Kˣ)ⁿ) →* Hom (Gal (L/K), μ_n (L))`:
the class of `a` acts by `σ ↦ σ (β) / β` for a root `β ^ n = a`
([Serre 1979, Chap. X, §3, p.155][Serre1979];
[Milne 2020, Chap. VII, App. A, Thm. A.3, p.226][MilneCFT];
[Yamaguchi 2026, `KummerTheory/Concrete/FiniteCharacterEquiv.lean:141`][Yamaguchi2026]). -/
noncomputable def kummerCharacterHom (n : ℕ)
    (hmu : ∀ u : Lˣ, u ^ n = 1 → ∃ ζ : Kˣ, Units.map (algebraMap K L).toMonoidHom ζ = u) :
    ↥(kummerRadicalSubgroup K L n) ⧸
        (MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ)).subgroupOf
          (kummerRadicalSubgroup K L n) →*
      ((L ≃ₐ[K] L) →* ↥(rootsOfUnity n L)) :=
  QuotientGroup.lift _ (characterHom hmu)
    (fun _ hδ => MonoidHom.mem_ker.mpr (character_eq_one hmu hδ))

/-- The Kummer character homomorphism computes by the root quotient, against *any* root: the
choice inside the construction is invisible to the interface
([Serre 1979, Chap. X, §3, p.155][Serre1979]). -/
theorem kummerCharacterHom_apply (n : ℕ)
    (hmu : ∀ u : Lˣ, u ^ n = 1 → ∃ ζ : Kˣ, Units.map (algebraMap K L).toMonoidHom ζ = u)
    {a : Kˣ} (ha : a ∈ kummerRadicalSubgroup K L n) {β : Lˣ}
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) (σ : L ≃ₐ[K] L) :
    (kummerCharacterHom K L n hmu (QuotientGroup.mk ⟨a, ha⟩) σ : Lˣ) = σ • β / β :=
  character_apply_eq hmu hβ σ

/-- The Kummer character homomorphism is injective: a class with trivial character has a
Galois-fixed root, which descends to the base and exhibits the class as a power. Proved —
no recorded claim ([Milne 2020, Chap. VII, App. A, Thm. A.3, p.226][MilneCFT];
[Yamaguchi 2026, `KummerTheory/Concrete/RadicalQuotient.lean:269`][Yamaguchi2026]). -/
theorem kummerCharacterHom_injective [FiniteDimensional K L] [IsGalois K L] (n : ℕ)
    (hmu : ∀ u : Lˣ, u ^ n = 1 → ∃ ζ : Kˣ, Units.map (algebraMap K L).toMonoidHom ζ = u) :
    Function.Injective (kummerCharacterHom K L n hmu) := by
  rw [injective_iff_map_eq_one]
  intro x
  refine QuotientGroup.induction_on x ?_
  intro δ h1'
  have h1 : character hmu δ = 1 := h1'
  have hfix : ∀ σ : L ≃ₐ[K] L, σ • rootOf δ.2 = rootOf δ.2 := by
    intro σ
    have h2 : (character hmu δ σ : Lˣ) = 1 := by rw [h1]; simp
    rw [character_apply_coe] at h2
    exact div_eq_one.mp h2
  obtain ⟨c, hc⟩ := exists_algebraMap_unit_eq hfix
  have hcn : c ^ n = (δ : Kˣ) :=
    Units.map_injective (f := (algebraMap K L).toMonoidHom) (algebraMap K L).injective
      (by rw [map_pow, hc, rootOf_pow δ.2])
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact MonoidHom.mem_range.mpr ⟨c, hcn⟩

/-- The Kummer character homomorphism is surjective: a character is a cocycle by the
roots-in-base hypothesis, Hilbert 90 writes it as a root quotient `σ (β) / β`, and `β ^ n`
is Galois-fixed, hence a base unit whose class maps to the character. Proved — no recorded
claim; the Hilbert 90 input is Mathlib's
([Serre 1979, Chap. X, §3, p.155][Serre1979];
[Yamaguchi 2026, `KummerTheory/Concrete/FiniteCharacterEquiv.lean:78`][Yamaguchi2026]). -/
theorem kummerCharacterHom_surjective [FiniteDimensional K L] [IsGalois K L] (n : ℕ)
    (hmu : ∀ u : Lˣ, u ^ n = 1 → ∃ ζ : Kˣ, Units.map (algebraMap K L).toMonoidHom ζ = u) :
    Function.Surjective (kummerCharacterHom K L n hmu) := by
  intro χ
  have hcoc : IsMulCocycle₁ (fun σ : L ≃ₐ[K] L => (χ σ : Lˣ)) := by
    intro σ τ
    change (χ (σ * τ) : Lˣ) = σ • (χ τ : Lˣ) * (χ σ : Lˣ)
    have hfixv : σ • (χ τ : Lˣ) = (χ τ : Lˣ) :=
      smul_eq_self_of_pow_eq_one hmu σ ((mem_rootsOfUnity n _).mp (χ τ).2)
    rw [map_mul, Subgroup.coe_mul, hfixv]
    exact mul_comm _ _
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units _ hcoc
  have hfixpow : ∀ σ : L ≃ₐ[K] L, σ • β ^ n = β ^ n := by
    intro σ
    have h1 : (σ • β / β) ^ n = 1 := by
      rw [hβ σ]
      exact (mem_rootsOfUnity n _).mp (χ σ).2
    rw [div_pow, ← smul_pow'] at h1
    exact div_eq_one.mp h1
  obtain ⟨a, ha⟩ := exists_algebraMap_unit_eq hfixpow
  have haΔ : a ∈ kummerRadicalSubgroup K L n := ⟨β, ha.symm⟩
  refine ⟨QuotientGroup.mk ⟨a, haΔ⟩, MonoidHom.ext fun σ => Subtype.ext ?_⟩
  have hb : β ^ n = Units.map (algebraMap K L).toMonoidHom
      ((⟨a, haΔ⟩ : ↥(kummerRadicalSubgroup K L n)) : Kˣ) := ha.symm
  calc (kummerCharacterHom K L n hmu (QuotientGroup.mk ⟨a, haΔ⟩) σ : Lˣ)
      = (character hmu ⟨a, haΔ⟩ σ : Lˣ) := rfl
    _ = σ • β / β := character_apply_eq hmu hb σ
    _ = (χ σ : Lˣ) := hβ σ

/-- The **Kummer character equivalence** `Δ / (Δ ∩ (Kˣ)ⁿ) ≃* Hom (Gal (L/K), μ_n (L))`,
fully proved: bijectivity is the two statements above, injectivity by the fixed-field
computation and surjectivity by Hilbert 90
([Serre 1979, Chap. X, §3, p.155][Serre1979];
[Milne 2020, Chap. VII, App. A, Thm. A.3, p.226][MilneCFT];
[Yamaguchi 2026, `KummerTheory/Concrete/FiniteCharacterEquiv.lean:141`][Yamaguchi2026]). -/
noncomputable def kummerCharacterEquiv [FiniteDimensional K L] [IsGalois K L] (n : ℕ)
    (hmu : ∀ u : Lˣ, u ^ n = 1 → ∃ ζ : Kˣ, Units.map (algebraMap K L).toMonoidHom ζ = u) :
    (↥(kummerRadicalSubgroup K L n) ⧸
        (MonoidHom.range (powMonoidHom n : Kˣ →* Kˣ)).subgroupOf
          (kummerRadicalSubgroup K L n)) ≃*
      ((L ≃ₐ[K] L) →* ↥(rootsOfUnity n L)) :=
  MulEquiv.ofBijective (kummerCharacterHom K L n hmu)
    ⟨kummerCharacterHom_injective K L n hmu, kummerCharacterHom_surjective K L n hmu⟩

/-- The equivalence computes by the root quotient, against any root
([Serre 1979, Chap. X, §3, p.155][Serre1979]). -/
theorem kummerCharacterEquiv_apply [FiniteDimensional K L] [IsGalois K L] (n : ℕ)
    (hmu : ∀ u : Lˣ, u ^ n = 1 → ∃ ζ : Kˣ, Units.map (algebraMap K L).toMonoidHom ζ = u)
    {a : Kˣ} (ha : a ∈ kummerRadicalSubgroup K L n) {β : Lˣ}
    (hβ : β ^ n = Units.map (algebraMap K L).toMonoidHom a) (σ : L ≃ₐ[K] L) :
    (kummerCharacterEquiv K L n hmu (QuotientGroup.mk ⟨a, ha⟩) σ : Lˣ) = σ • β / β :=
  kummerCharacterHom_apply K L n hmu ha hβ σ

end Atlas.Knowledge
