import Mathlib

/-!
# Herbrand quotient

The Herbrand quotient of a cyclic action on an abelian group, in the elementary presentation:
for `σ` an automorphism of a commutative group `A` with `σ ^ n = 1`, the norm
`N a = ∏ σ^i a` and the difference `D a = σ a * a⁻¹` compose to `1` in both orders, the
graded pieces are `Ĥ⁰ = ker D ⧸ im N` and `Ĥ¹ = ker N ⧸ im D`, and the quotient
`q = #Ĥ⁰ / #Ĥ¹` is multiplicative along short exact sequences and `1` on finite modules.
This is the counting engine of the first inequality of local class field theory: with the
value `n` on the trivial module `ℤ` it computes the norm index `(Kˣ : N Lˣ) = [L : K]` of a
cyclic extension. The generator and its order are carried as data, and no group `G`
appears: the pieces are those of the `ZMod n`-action through `σ`, Serre's groups when `σ`
has order exactly `n`, which is how the consumer, a chosen generator of a cyclic Galois
group acting on `Lˣ`, will instantiate it.

## Main definitions

* `HerbrandQuotient.norm`, `HerbrandQuotient.diff` — the two arrows of the action.
* `HerbrandQuotient.H0`, `HerbrandQuotient.H1` — the mod-2 graded Tate pieces of the action.
* `herbrandQuotient` — their cardinality ratio in `ℚ`.
* `HerbrandQuotient.stableRestrict` / `HerbrandQuotient.stableQuotient` — the action on a
  stable subgroup and on its quotient.
* `HerbrandQuotient.shiftAut` — the shift of the co-induced module `ZMod n → M`.

## Main statements

* `HerbrandQuotient.card_identity_of_exact` — division-free multiplicativity along an
  equivariant short exact sequence: the exact hexagon, counted; proved.
* `HerbrandQuotient.finite_of_exact` — finiteness of the outer pieces propagates to the
  middle; the consumed half of Serre's "two of three defined"; proved.
* `HerbrandQuotient.card_H0_eq_card_H1_of_finite` / `herbrandQuotient_finite` — a finite
  module has equal graded pieces, `q = 1`; proved.
* `herbrandQuotient_mul` — the `ℚ`-valued form of multiplicativity; proved.
* `HerbrandQuotient.card_identity_of_finiteIndex` — a stable subgroup of finite index has
  the same graded counts: the inclusion case of Serre's Corollary; proved.
* `HerbrandQuotient.card_H0_int` / `HerbrandQuotient.card_H1_int` — the trivial action on
  `ℤ` counts `n` and `1`; proved.
* `HerbrandQuotient.card_H0_shiftAut` / `HerbrandQuotient.card_H1_shiftAut` — both graded
  pieces of the co-induced module count `1`; proved.
* `HerbrandQuotient.card_H0_congr` / `HerbrandQuotient.card_H1_congr` — isomorphic actions
  count the same, the transport the staged computations travel; proved.

## Implementation notes

Division-free statements carry the content: `herbrandQuotient` takes values in `ℚ` with the
`Nat.card` junk value `0` on infinite pieces, so the theorems that matter are equations
between products of cardinalities under explicit finiteness hypotheses, and the `ℚ`-valued
forms are packaging. Both graded pieces are one construction — for a pair of endomorphisms
`u v` with both composites trivial, the subquotient `ker u ⧸ im v`, kept private as `piece` —
`Ĥ⁰` at `(D, N)` and `Ĥ¹` at `(N, D)`, so each of the three exactness lemmas of the hexagon
is proved once for an abstract pair and instantiated twice with the roles swapped; the
connecting map is built on witnesses by choice, made a homomorphism by its own
choice-independence. `Subgroup.subgroupOf` needs no inclusion to be well formed, so the
pieces exist without `σ ^ n = 1`, and the containments are the two telescoping lemmas
`diff_norm_apply` and `norm_diff_apply`, not data. The multiplicativity avoids Mathlib's
Tate and group cohomology deliberately: the pinned
`RepresentationTheory/Homological/GroupCohomology/FiniteCyclic.lean` supplies periodicity
isomorphisms pointwise but not their naturality, which is what the count needs, and the
elementary route keeps the eventual consumer on `Lˣ` multiplicatively, with no
`Rep`/`Additive` transport. The source proves the same count through Mathlib's homology
long exact sequence over its own periodic complex instead. The toolkit closes with the
stability layer, the trivial-`ℤ` counts, and the co-induced module's vanishing — the four
inputs the norm-index computation of the class field axiom will consume, staged here so
that the consuming phase carries only the arithmetic.

## References

* [Serre1979] J-P. Serre, *Local fields*, Graduate Texts in Mathematics **67**, Springer New
  York, 1979.
* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in
  Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

namespace HerbrandQuotient
variable {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]

private abbrev piece (u v : A →* A) : Type _ := u.ker ⧸ v.range.subgroupOf u.ker

private abbrev pieceMk (u v : A →* A) : u.ker →* piece u v :=
  QuotientGroup.mk' (v.range.subgroupOf u.ker)

private theorem pieceMk_eq_one_iff (u v : A →* A) (x : u.ker) :
    pieceMk u v x = 1 ↔ (x : A) ∈ v.range := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

private theorem exists_of_pieceMk_eq {u v : A →* A} {x y : u.ker}
    (h : pieceMk u v x = pieceMk u v y) : ∃ a : A, v a * (x : A) = (y : A) := by
  rw [QuotientGroup.mk'_eq_mk'] at h
  obtain ⟨z, hz, hxy⟩ := h
  rw [Subgroup.mem_subgroupOf] at hz
  obtain ⟨a, ha⟩ := hz
  refine ⟨a, ?_⟩
  have := congrArg (Subtype.val) hxy
  simp only [Subgroup.coe_mul] at this
  rw [← this, ha]
  exact mul_comm _ _

private theorem pieceMk_eq_of_witness {u v : A →* A} (hvu : ∀ a, u (v a) = 1) {x y : u.ker}
    (a : A) (ha : v a * (x : A) = (y : A)) : pieceMk u v x = pieceMk u v y := by
  rw [QuotientGroup.mk'_eq_mk']
  refine ⟨⟨v a, MonoidHom.mem_ker.mpr (hvu a)⟩, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact ⟨a, rfl⟩
  · ext
    simpa [mul_comm] using ha

variable {uA vA : A →* A} {uB vB : B →* B} {uC vC : C →* C}

private def kerRestrict (f : A →* B) (hfu : ∀ a, f (uA a) = uB (f a)) :
    uA.ker →* uB.ker :=
  (f.comp uA.ker.subtype).codRestrict uB.ker fun x => by
    have hx : uA (x : A) = 1 := MonoidHom.mem_ker.mp x.2
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, ← hfu, hx, map_one]

@[simp] private theorem kerRestrict_coe (f : A →* B) (hfu : ∀ a, f (uA a) = uB (f a))
    (x : uA.ker) : (kerRestrict f hfu x : B) = f x := rfl

private def pieceMap (f : A →* B) (hfu : ∀ a, f (uA a) = uB (f a))
    (hfv : ∀ a, f (vA a) = vB (f a)) : piece uA vA →* piece uB vB :=
  QuotientGroup.map _ _ (kerRestrict f hfu) (by
    rintro ⟨x, hx⟩ hmem
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨a, ha⟩ := hmem
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact ⟨f a, by rw [← hfv]; rw [Subgroup.coe_mk] at ha; rw [ha]; rfl⟩)

private theorem pieceMap_mk (f : A →* B) (hfu : ∀ a, f (uA a) = uB (f a))
    (hfv : ∀ a, f (vA a) = vB (f a)) (x : uA.ker) :
    pieceMap f hfu hfv (pieceMk uA vA x) = pieceMk uB vB (kerRestrict f hfu x) :=
  rfl

variable {f : A →* B} {g : B →* C}

private theorem pieceδ_indep
    (hAvu : ∀ a : A, vA (uA a) = 1) (hBuv : ∀ b : B, uB (vB b) = 1)
    (hfu : ∀ a, f (uA a) = uB (f a)) (hgv : ∀ b, g (vB b) = vC (g b))
    (hinj : Function.Injective f) (hsurj : Function.Surjective g)
    (hexact : g.ker = f.range)
    {c c' : uC.ker} {b b' : B} {a a' : A}
    (hb : g b = (c : C)) (ha : f a = uB b) (hka : a ∈ vA.ker)
    (hb' : g b' = (c' : C)) (ha' : f a' = uB b') (hka' : a' ∈ vA.ker)
    (hcc : pieceMk uC vC c = pieceMk uC vC c') :
    pieceMk vA uA ⟨a, hka⟩ = pieceMk vA uA ⟨a', hka'⟩ := by
  obtain ⟨c₀, hc₀⟩ := exists_of_pieceMk_eq hcc
  obtain ⟨b₀, hb₀⟩ := hsurj c₀
  have hlift : g (b' * (vB b₀ * b)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, hgv, hb₀, hb, hb', ← hc₀]
    group
  have hmem : b' * (vB b₀ * b)⁻¹ ∈ f.range := by
    rw [← hexact]; exact MonoidHom.mem_ker.mpr hlift
  obtain ⟨a₀, ha₀⟩ := hmem
  have key : f a' = f (uA a₀ * a) := by
    have hb'eq : b' = f a₀ * (vB b₀ * b) := by rw [ha₀]; group
    rw [ha', hb'eq, map_mul, map_mul, hBuv, one_mul, map_mul, hfu, ha]
  exact pieceMk_eq_of_witness hAvu a₀ (hinj key).symm

private theorem pieceδ_exists
    (hBvu : ∀ b : B, vB (uB b) = 1) (hfv : ∀ a, f (vA a) = vB (f a))
    (hgu : ∀ b, g (uB b) = uC (g b))
    (hinj : Function.Injective f) (hsurj : Function.Surjective g)
    (hexact : g.ker = f.range) (c : uC.ker) :
    ∃ (a : A) (b : B), a ∈ vA.ker ∧ g b = (c : C) ∧ f a = uB b := by
  obtain ⟨b, hb⟩ := hsurj (c : C)
  have hub : uB b ∈ g.ker := by
    rw [MonoidHom.mem_ker, hgu, hb, MonoidHom.mem_ker.mp c.2]
  rw [hexact] at hub
  obtain ⟨a, ha⟩ := hub
  refine ⟨a, b, ?_, hb, ha⟩
  rw [MonoidHom.mem_ker]
  exact hinj (by rw [hfv, ha, hBvu, map_one])

section Delta

variable (hAvu : ∀ a : A, vA (uA a) = 1)
variable (hBvu : ∀ b : B, vB (uB b) = 1) (hBuv : ∀ b : B, uB (vB b) = 1)
variable (hfu : ∀ a, f (uA a) = uB (f a)) (hfv : ∀ a, f (vA a) = vB (f a))
variable (hgu : ∀ b, g (uB b) = uC (g b)) (hgv : ∀ b, g (vB b) = vC (g b))
variable (hinj : Function.Injective f) (hsurj : Function.Surjective g)
variable (hexact : g.ker = f.range)

private noncomputable def pieceδFun (uA : A →* A) (c : uC.ker) : piece vA uA :=
  pieceMk vA uA ⟨(pieceδ_exists hBvu hfv hgu hinj hsurj hexact c).choose,
    (pieceδ_exists hBvu hfv hgu hinj hsurj hexact c).choose_spec.choose_spec.1⟩

include hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact in
private theorem pieceδFun_eq {c : uC.ker} {b : B} {a : A}
    (hb : g b = (c : C)) (ha : f a = uB b) (hka : a ∈ vA.ker) :
    pieceδFun hBvu hfv hgu hinj hsurj hexact uA c = pieceMk vA uA ⟨a, hka⟩ := by
  have hspec := (pieceδ_exists hBvu hfv hgu hinj hsurj hexact c).choose_spec.choose_spec
  exact pieceδ_indep hAvu hBuv hfu hgv hinj hsurj hexact
    hspec.2.1 hspec.2.2 hspec.1 hb ha hka rfl

include hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact in
private theorem pieceδFun_mul (c₁ c₂ : uC.ker) :
    pieceδFun hBvu hfv hgu hinj hsurj hexact uA (c₁ * c₂) =
      pieceδFun hBvu hfv hgu hinj hsurj hexact uA c₁ *
        pieceδFun hBvu hfv hgu hinj hsurj hexact uA c₂ := by
  have h₁ := (pieceδ_exists hBvu hfv hgu hinj hsurj hexact c₁).choose_spec.choose_spec
  have h₂ := (pieceδ_exists hBvu hfv hgu hinj hsurj hexact c₂).choose_spec.choose_spec
  have hmul : pieceδFun hBvu hfv hgu hinj hsurj hexact uA (c₁ * c₂) =
      pieceMk vA uA ⟨(pieceδ_exists hBvu hfv hgu hinj hsurj hexact c₁).choose *
        (pieceδ_exists hBvu hfv hgu hinj hsurj hexact c₂).choose,
        mul_mem h₁.1 h₂.1⟩ := by
    refine pieceδFun_eq hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact
      (b := (pieceδ_exists hBvu hfv hgu hinj hsurj hexact c₁).choose_spec.choose *
        (pieceδ_exists hBvu hfv hgu hinj hsurj hexact c₂).choose_spec.choose) ?_ ?_ _
    · rw [map_mul, h₁.2.1, h₂.2.1]; rfl
    · rw [map_mul f, map_mul uB]
      exact congrArg₂ (· * ·) h₁.2.2 h₂.2.2
  rw [hmul]
  rfl

private noncomputable def pieceδ : piece uC vC →* piece vA uA :=
  QuotientGroup.lift _
    (MonoidHom.mk' (pieceδFun hBvu hfv hgu hinj hsurj hexact uA)
      (pieceδFun_mul hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact))
    (by
      rintro ⟨x, hx⟩ hmem
      rw [Subgroup.mem_subgroupOf] at hmem
      obtain ⟨c₀, hc₀⟩ := hmem
      obtain ⟨b₀, hb₀⟩ := hsurj c₀
      have h1 : pieceδFun hBvu hfv hgu hinj hsurj hexact uA ⟨x, hx⟩ =
          pieceMk vA uA ⟨1, one_mem _⟩ := by
        refine pieceδFun_eq hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact
          (b := vB b₀) ?_ ?_ _
        · rw [hgv, hb₀, hc₀]
        · rw [map_one, hBuv]
      have h2 : (⟨(1 : A), one_mem _⟩ : vA.ker) = 1 := rfl
      change pieceδFun hBvu hfv hgu hinj hsurj hexact uA ⟨x, hx⟩ = 1
      rw [h1, h2, map_one])

include hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact in
private theorem pieceδ_mk {c : uC.ker} {b : B} {a : A}
    (hb : g b = (c : C)) (ha : f a = uB b) (hka : a ∈ vA.ker) :
    pieceδ hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact (pieceMk uC vC c) =
      pieceMk vA uA ⟨a, hka⟩ :=
  pieceδFun_eq hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact hb ha hka

end Delta

section Exactness

variable {uA vA : A →* A} {uB vB : B →* B} {uC vC : C →* C}
variable {f : A →* B} {g : B →* C}
variable (hAvu : ∀ a : A, vA (uA a) = 1)
variable (hBvu : ∀ b : B, vB (uB b) = 1) (hBuv : ∀ b : B, uB (vB b) = 1)
variable (hfu : ∀ a, f (uA a) = uB (f a)) (hfv : ∀ a, f (vA a) = vB (f a))
variable (hgu : ∀ b, g (uB b) = uC (g b)) (hgv : ∀ b, g (vB b) = vC (g b))
variable (hinj : Function.Injective f) (hsurj : Function.Surjective g)
variable (hexact : g.ker = f.range)

include hBuv hinj hsurj hexact in
/- Exactness at the middle node: the image of the piece of `A` is the kernel of the map to
the piece of `C`. -/
private theorem pieceMap_exact_middle :
    (pieceMap f hfu hfv).range = (pieceMap g hgu hgv).ker := by
  ext q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ q
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ p
    rw [MonoidHom.mem_ker, ← hp, pieceMap_mk, pieceMap_mk, pieceMk_eq_one_iff]
    have hgf : g (f (x : A)) = 1 := by
      have : f (x : A) ∈ g.ker := by rw [hexact]; exact ⟨x, rfl⟩
      exact MonoidHom.mem_ker.mp this
    exact ⟨1, by rw [map_one]; exact hgf.symm⟩
  · intro hq
    rw [MonoidHom.mem_ker, pieceMap_mk, pieceMk_eq_one_iff] at hq
    obtain ⟨c₀, hc₀⟩ := hq
    obtain ⟨b₀, hb₀⟩ := hsurj c₀
    have hker : g ((b : B) * (vB b₀)⁻¹) = 1 := by
      rw [map_mul, map_inv, hgv, hb₀, hc₀]
      have : (kerRestrict g hgu b : C) = g (b : B) := rfl
      rw [← this]
      group
    have hmem : (b : B) * (vB b₀)⁻¹ ∈ f.range := by
      rw [← hexact]; exact MonoidHom.mem_ker.mpr hker
    obtain ⟨a, ha⟩ := hmem
    have hka : a ∈ uA.ker := by
      rw [MonoidHom.mem_ker]
      refine hinj ?_
      rw [hfu, ha, map_one, map_mul, map_inv, hBuv,
        MonoidHom.mem_ker.mp b.2]
      group
    refine ⟨pieceMk uA vA ⟨a, hka⟩, ?_⟩
    rw [pieceMap_mk]
    refine pieceMk_eq_of_witness hBuv b₀ ?_
    rw [kerRestrict_coe, ha, mul_comm, inv_mul_cancel_right]

include hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact in
/- Exactness at the right node: the image of the piece of `B` is the kernel of the
connecting map. -/
private theorem pieceMap_exact_right :
    (pieceMap g hgu hgv).range =
      (pieceδ hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact).ker := by
  ext q
  obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ q
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective _ p
    rw [MonoidHom.mem_ker, ← hp, pieceMap_mk]
    have h1 : pieceδ hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact
        (pieceMk uC vC (kerRestrict g hgu b)) = pieceMk vA uA ⟨1, one_mem _⟩ := by
      refine pieceδ_mk hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact
        (b := (b : B)) rfl ?_ _
      rw [map_one, MonoidHom.mem_ker.mp b.2]
    rw [h1]
    have h2 : (⟨(1 : A), one_mem _⟩ : vA.ker) = 1 := rfl
    rw [h2, map_one]
  · intro hq
    rw [MonoidHom.mem_ker] at hq
    obtain ⟨a, b, hka, hb, ha⟩ := pieceδ_exists hBvu hfv hgu hinj hsurj hexact c
    have hδ := pieceδ_mk hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact hb ha hka
    rw [hδ] at hq
    rw [pieceMk_eq_one_iff] at hq
    obtain ⟨a₀, ha₀⟩ := hq
    have hb' : (b * (f a₀)⁻¹) ∈ uB.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← hfu, ha₀]
      dsimp only []
      rw [← ha]
      group
    refine ⟨pieceMk uB vB ⟨b * (f a₀)⁻¹, hb'⟩, ?_⟩
    rw [pieceMap_mk]
    congr 1
    ext
    rw [kerRestrict_coe, map_mul, map_inv]
    have hgf : g (f a₀) = 1 := by
      have : f a₀ ∈ g.ker := by rw [hexact]; exact ⟨a₀, rfl⟩
      exact MonoidHom.mem_ker.mp this
    rw [hgf, hb]
    group

include hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact in
/- Exactness at the left node: the image of the connecting map is the kernel of the induced
map on the swapped pieces. -/
private theorem pieceδ_exact_left :
    (pieceδ hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact).range =
      (pieceMap (uA := vA) (vA := uA) (uB := vB) (vB := uB) f hfv hfu).ker := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ p
    obtain ⟨a, b, hka, hb, ha⟩ := pieceδ_exists hBvu hfv hgu hinj hsurj hexact c
    have hδ := pieceδ_mk hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact hb ha hka
    rw [MonoidHom.mem_ker, ← hp, hδ, pieceMap_mk, pieceMk_eq_one_iff]
    exact ⟨b, by rw [kerRestrict_coe, ha]⟩
  · intro hq
    rw [MonoidHom.mem_ker, pieceMap_mk, pieceMk_eq_one_iff] at hq
    obtain ⟨b, hb⟩ := hq
    have hc : g b ∈ uC.ker := by
      rw [MonoidHom.mem_ker, ← hgu]
      have hfx : f (x : A) ∈ g.ker := by rw [hexact]; exact ⟨x, rfl⟩
      rw [kerRestrict_coe] at hb
      rw [hb]
      exact MonoidHom.mem_ker.mp hfx
    refine ⟨pieceMk uC vC ⟨g b, hc⟩, ?_⟩
    refine pieceδ_mk hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact
      (b := b) rfl ?_ _
    rw [kerRestrict_coe] at hb
    exact hb.symm

end Exactness

section Count

private theorem card_ker_mul_card_range' {X Y : Type*} [Group X] [Group Y] [Finite X]
    (h : X →* Y) : Nat.card h.ker * Nat.card h.range = Nat.card X := by
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange h).toEquiv, mul_comm]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup h.ker).symm

private theorem card_cycle_identity
    {X₀ X₁ X₂ X₃ X₄ X₅ : Type*}
    [Group X₀] [Group X₁] [Group X₂] [Group X₃] [Group X₄] [Group X₅]
    [Finite X₀] [Finite X₁] [Finite X₂] [Finite X₃] [Finite X₄] [Finite X₅]
    (m₀ : X₀ →* X₁) (m₁ : X₁ →* X₂) (m₂ : X₂ →* X₃)
    (m₃ : X₃ →* X₄) (m₄ : X₄ →* X₅) (m₅ : X₅ →* X₀)
    (e₁ : m₀.range = m₁.ker) (e₂ : m₁.range = m₂.ker) (e₃ : m₂.range = m₃.ker)
    (e₄ : m₃.range = m₄.ker) (e₅ : m₄.range = m₅.ker) (e₀ : m₅.range = m₀.ker) :
    Nat.card X₀ * Nat.card X₂ * Nat.card X₄ =
      Nat.card X₁ * Nat.card X₃ * Nat.card X₅ := by
  have h₀ := card_ker_mul_card_range' m₀
  have h₁ := card_ker_mul_card_range' m₁
  have h₂ := card_ker_mul_card_range' m₂
  have h₃ := card_ker_mul_card_range' m₃
  have h₄ := card_ker_mul_card_range' m₄
  have h₅ := card_ker_mul_card_range' m₅
  rw [← e₀] at h₀
  rw [← e₁] at h₁
  rw [← e₂] at h₂
  rw [← e₃] at h₃
  rw [← e₄] at h₄
  rw [← e₅] at h₅
  rw [← h₀, ← h₂, ← h₄, ← h₁, ← h₃, ← h₅]
  ring

end Count

section Assembly

variable {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
variable {uA vA : A →* A} {uB vB : B →* B} {uC vC : C →* C}
variable {f : A →* B} {g : B →* C}

/- The counted hexagon: for an equivariant short exact sequence with all six pieces finite,
the alternating product of the piece orders is one, in product form. -/
private theorem piece_card_identity
    (hAuv : ∀ a : A, uA (vA a) = 1) (hAvu : ∀ a : A, vA (uA a) = 1)
    (hBuv : ∀ b : B, uB (vB b) = 1) (hBvu : ∀ b : B, vB (uB b) = 1)
    (hfu : ∀ a, f (uA a) = uB (f a)) (hfv : ∀ a, f (vA a) = vB (f a))
    (hgu : ∀ b, g (uB b) = uC (g b)) (hgv : ∀ b, g (vB b) = vC (g b))
    (hinj : Function.Injective f) (hsurj : Function.Surjective g)
    (hexact : g.ker = f.range)
    [Finite (piece uA vA)] [Finite (piece uB vB)] [Finite (piece uC vC)]
    [Finite (piece vA uA)] [Finite (piece vB uB)] [Finite (piece vC uC)] :
    Nat.card (piece uA vA) * Nat.card (piece uC vC) * Nat.card (piece vB uB) =
      Nat.card (piece uB vB) * Nat.card (piece vA uA) * Nat.card (piece vC uC) :=
  card_cycle_identity
    (pieceMap f hfu hfv) (pieceMap g hgu hgv)
    (pieceδ hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact)
    (pieceMap f hfv hfu) (pieceMap g hgv hgu)
    (pieceδ hAuv hBuv hBvu hfv hfu hgv hgu hinj hsurj hexact)
    (pieceMap_exact_middle hBuv hfu hfv hgu hgv hinj hsurj hexact)
    (pieceMap_exact_right hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact)
    (pieceδ_exact_left hAvu hBvu hBuv hfu hfv hgu hgv hinj hsurj hexact)
    (pieceMap_exact_middle hBvu hfv hfu hgv hgu hinj hsurj hexact)
    (pieceMap_exact_right hAuv hBuv hBvu hfv hfu hgv hgu hinj hsurj hexact)
    (pieceδ_exact_left hAuv hBuv hBvu hfv hfu hgv hgu hinj hsurj hexact)

/- Finiteness propagates to the middle node: its map to the `C`-piece has kernel the image
of a finite piece and range inside a finite piece, and a group is finite when a homomorphism
out of it has finite kernel and finite range. -/
private theorem piece_finite_middle
    (hBuv : ∀ b : B, uB (vB b) = 1)
    (hfu : ∀ a, f (uA a) = uB (f a)) (hfv : ∀ a, f (vA a) = vB (f a))
    (hgu : ∀ b, g (uB b) = uC (g b)) (hgv : ∀ b, g (vB b) = vC (g b))
    (hinj : Function.Injective f) (hsurj : Function.Surjective g)
    (hexact : g.ker = f.range)
    [Finite (piece uA vA)] [Finite (piece uC vC)] : Finite (piece uB vB) := by
  haveI h1 : Finite (pieceMap g hgu hgv :
      piece uB vB →* piece uC vC).ker := by
    rw [← pieceMap_exact_middle hBuv hfu hfv hgu hgv hinj hsurj hexact]
    exact Set.Finite.to_subtype (Set.finite_range _)
  haveI h2 : Finite (piece uB vB ⧸ (pieceMap g hgu hgv :
      piece uB vB →* piece uC vC).ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange _).symm.toEquiv
  exact Finite.of_equiv _
    (Subgroup.groupEquivQuotientProdSubgroup
      (s := (pieceMap g hgu hgv : piece uB vB →* piece uC vC).ker)).symm

/- Transport along an intertwining isomorphism: the pieces of isomorphic actions count the
same — the kernel-level restriction of the isomorphism is bijective and matches the range
parts. -/
private theorem piece_card_congr (e : A ≃* B)
    (heu : ∀ a, (e : A →* B) (uA a) = uB ((e : A →* B) a))
    (hev : ∀ a, (e : A →* B) (vA a) = vB ((e : A →* B) a)) :
    Nat.card (piece uA vA) = Nat.card (piece uB vB) := by
  have heu' : ∀ b, e.symm (uB b) = uA (e.symm b) := by
    intro b
    refine e.injective ?_
    rw [e.apply_symm_apply]
    exact ((heu (e.symm b)).trans (congrArg uB (e.apply_symm_apply b))).symm
  have hbij : Function.Bijective (kerRestrict (uA := uA) (uB := uB) (e : A →* B) heu) := by
    constructor
    · intro x y hxy
      refine Subtype.ext (e.injective ?_)
      exact congrArg Subtype.val hxy
    · rintro ⟨y, hy⟩
      have hmem : e.symm y ∈ uA.ker := by
        rw [MonoidHom.mem_ker, ← heu' y, MonoidHom.mem_ker.mp hy, map_one]
      exact ⟨⟨e.symm y, hmem⟩, Subtype.ext (e.apply_symm_apply y)⟩
  refine Nat.card_congr (QuotientGroup.congr _ _ (MulEquiv.ofBijective _ hbij) ?_).toEquiv
  rw [show ((MulEquiv.ofBijective _ hbij : uA.ker ≃* uB.ker) : uA.ker →* uB.ker) =
    kerRestrict (uA := uA) (uB := uB) (e : A →* B) heu from MonoidHom.ext fun x => rfl]
  ext z
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨⟨w, hw⟩, hmem, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hmem
    obtain ⟨a, ha⟩ := hmem
    refine ⟨(e : A →* B) a, ?_⟩
    rw [← hev, kerRestrict_coe]
    exact congrArg (e : A →* B) ha
  · rintro ⟨b, hb⟩
    have hmemA : e.symm (z : B) ∈ uA.ker := by
      rw [MonoidHom.mem_ker, ← heu' (z : B), MonoidHom.mem_ker.mp z.2, map_one]
    refine ⟨⟨e.symm (z : B), hmemA⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      refine ⟨e.symm b, ?_⟩
      have hev' : ∀ w, e.symm (vB w) = vA (e.symm w) := by
        intro w
        refine e.injective ?_
        rw [e.apply_symm_apply]
        exact ((hev (e.symm w)).trans (congrArg vB (e.apply_symm_apply w))).symm
      rw [show ((⟨e.symm (z : B), hmemA⟩ : uA.ker) : A) = e.symm (z : B) from rfl,
        ← hev' b, hb]
    · exact Subtype.ext (e.apply_symm_apply (z : B))

end Assembly

section Concrete

variable {A B : Type*} [CommGroup A] [CommGroup B]

/-- The **norm** of the cyclic action generated by `σ` at order `n`: `N a = ∏ i < n, σ^i a`
([Serre 1979, Chap. VIII, §4, p.132][Serre1979]). -/
noncomputable def norm (σ : A ≃* A) (n : ℕ) : A →* A :=
  ∏ i ∈ Finset.range n, ((σ ^ i : A ≃* A) : A →* A)

/-- The **difference** of the action: `D a = σ a * a⁻¹`, the multiplicative `σ - 1`
([Serre 1979, Chap. VIII, §4, p.132][Serre1979]). -/
def diff (σ : A ≃* A) : A →* A :=
  (σ : A →* A) * (MonoidHom.id A)⁻¹

/-- The norm, pointwise. -/
theorem norm_apply (σ : A ≃* A) (n : ℕ) (a : A) :
    norm σ n a = ∏ i ∈ Finset.range n, (σ ^ i : A ≃* A) a := by
  simp [norm]

/-- The difference, pointwise. -/
theorem diff_apply (σ : A ≃* A) (a : A) : diff σ a = σ a * a⁻¹ := rfl

/-- The norm absorbs the action on the inside once `σ ^ n = 1`. -/
theorem norm_apply_smul {σ : A ≃* A} {n : ℕ} (hσ : σ ^ n = 1) (a : A) :
    norm σ n (σ a) = norm σ n a := by
  have key : ∀ b : A, ∏ i ∈ Finset.range n, (σ ^ (i + 1) : A ≃* A) b =
      ∏ i ∈ Finset.range n, (σ ^ i : A ≃* A) b := by
    intro b
    have h1 := Finset.prod_range_succ' (fun i => (σ ^ i : A ≃* A) b) n
    have h2 := Finset.prod_range_succ (fun i => (σ ^ i : A ≃* A) b) n
    have h3 : (σ ^ n : A ≃* A) b = b := by rw [hσ]; rfl
    have h4 : (σ ^ (0 : ℕ) : A ≃* A) b = b := rfl
    calc ∏ i ∈ Finset.range n, (σ ^ (i + 1) : A ≃* A) b
        = (∏ i ∈ Finset.range n, (σ ^ (i + 1) : A ≃* A) b) * ((σ ^ (0 : ℕ) : A ≃* A) b) *
          ((σ ^ (0 : ℕ) : A ≃* A) b)⁻¹ := by group
      _ = (∏ i ∈ Finset.range (n + 1), (σ ^ i : A ≃* A) b) * b⁻¹ := by rw [← h1, h4]
      _ = (∏ i ∈ Finset.range n, (σ ^ i : A ≃* A) b) * ((σ ^ n : A ≃* A) b) * b⁻¹ := by
          rw [h2]
      _ = ∏ i ∈ Finset.range n, (σ ^ i : A ≃* A) b := by rw [h3]; group
  rw [norm_apply, norm_apply]
  calc ∏ i ∈ Finset.range n, (σ ^ i : A ≃* A) (σ a)
      = ∏ i ∈ Finset.range n, (σ ^ (i + 1) : A ≃* A) a := by
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [pow_succ]
        rfl
    _ = ∏ i ∈ Finset.range n, (σ ^ i : A ≃* A) a := key a

/-- The action fixes norms once `σ ^ n = 1`. -/
theorem smul_norm_apply {σ : A ≃* A} {n : ℕ} (hσ : σ ^ n = 1) (a : A) :
    σ (norm σ n a) = norm σ n a := by
  have h1 : σ (norm σ n a) = ∏ i ∈ Finset.range n, (σ ^ (i + 1) : A ≃* A) a := by
    rw [norm_apply, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [pow_succ']
    rfl
  have h2 : norm σ n (σ a) = ∏ i ∈ Finset.range n, (σ ^ i : A ≃* A) (σ a) := norm_apply σ n _
  have h3 : ∀ i, (σ ^ i : A ≃* A) (σ a) = (σ ^ (i + 1) : A ≃* A) a := by
    intro i
    rw [pow_succ]
    rfl
  rw [h1, ← norm_apply_smul hσ a, h2]
  exact Finset.prod_congr rfl fun i _ => (h3 i).symm

/-- Norms die under the difference: `D ∘ N = 1`. -/
theorem diff_norm_apply {σ : A ≃* A} {n : ℕ} (hσ : σ ^ n = 1) (a : A) :
    diff σ (norm σ n a) = 1 := by
  rw [diff_apply, smul_norm_apply hσ]
  group

/-- Differences die under the norm: `N ∘ D = 1`. -/
theorem norm_diff_apply {σ : A ≃* A} {n : ℕ} (hσ : σ ^ n = 1) (a : A) :
    norm σ n (diff σ a) = 1 := by
  rw [diff_apply, map_mul, map_inv, norm_apply_smul hσ]
  group

/-! Equivariance transports: a hom commuting with the generators commutes with the powers,
the norm, and the difference. -/

/-- A hom commuting with the generators commutes with their powers. -/
theorem map_pow_comm {σA : A ≃* A} {σB : B ≃* B} {f : A →* B}
    (hf : ∀ a, f (σA a) = σB (f a)) (i : ℕ) :
    ∀ a, f ((σA ^ i : A ≃* A) a) = (σB ^ i : B ≃* B) (f a) := by
  induction i with
  | zero => intro a; rfl
  | succ k ih =>
    intro a
    have hA : (σA ^ (k + 1) : A ≃* A) a = (σA ^ k : A ≃* A) (σA a) := by
      rw [pow_succ]
      rfl
    have hB : (σB ^ (k + 1) : B ≃* B) (f a) = (σB ^ k : B ≃* B) (σB (f a)) := by
      rw [pow_succ]
      rfl
    rw [hA, hB, ← hf]
    exact ih (σA a)

/-- A hom commuting with the generators commutes with the norms. -/
theorem map_norm_comm {σA : A ≃* A} {σB : B ≃* B} {f : A →* B}
    (hf : ∀ a, f (σA a) = σB (f a)) (n : ℕ) (a : A) :
    f (norm σA n a) = norm σB n (f a) := by
  rw [norm_apply, norm_apply, map_prod]
  exact Finset.prod_congr rfl fun i _ => map_pow_comm hf i a

/-- A hom commuting with the generators commutes with the differences. -/
theorem map_diff_comm {σA : A ≃* A} {σB : B ≃* B} {f : A →* B}
    (hf : ∀ a, f (σA a) = σB (f a)) (a : A) :
    f (diff σA a) = diff σB (f a) := by
  rw [diff_apply, diff_apply, map_mul, map_inv, hf]

/-- The even graded Tate piece `Ĥ⁰ = ker D ⧸ im N` of the `ZMod n`-action through `σ`:
fixed points of `σ` modulo norms. Serre's `A^G/NA` reads off when `σ` has order exactly
`n`, so that `⟨σ⟩` is cyclic of order `n`; at a proper divisor order the piece is that of
the `ZMod n`-action, not of `⟨σ⟩`
([Serre 1979, Chap. VIII, §4, p.133][Serre1979]). -/
def H0 (σ : A ≃* A) (n : ℕ) : Type _ := piece (diff σ) (norm σ n)

/-- The odd graded Tate piece `Ĥ¹ = ker N ⧸ im D` of the `ZMod n`-action through `σ`: the
norm kernel modulo differences — Serre's own `_N A/DA`, with the same order-exactly-`n`
reading as `Atlas.Knowledge.HerbrandQuotient.H0`
([Serre 1979, Chap. VIII, §4, p.133][Serre1979]). -/
def H1 (σ : A ≃* A) (n : ℕ) : Type _ := piece (norm σ n) (diff σ)

noncomputable instance (σ : A ≃* A) (n : ℕ) : CommGroup (H0 σ n) :=
  inferInstanceAs (CommGroup (piece (diff σ) (norm σ n)))

noncomputable instance (σ : A ≃* A) (n : ℕ) : CommGroup (H1 σ n) :=
  inferInstanceAs (CommGroup (piece (norm σ n) (diff σ)))

instance (σ : A ≃* A) (n : ℕ) [Finite A] : Finite (H0 σ n) :=
  inferInstanceAs (Finite ((diff σ).ker ⧸ (norm σ n).range.subgroupOf (diff σ).ker))

instance (σ : A ≃* A) (n : ℕ) [Finite A] : Finite (H1 σ n) :=
  inferInstanceAs (Finite ((norm σ n).ker ⧸ (diff σ).range.subgroupOf (norm σ n).ker))

/-- **Multiplicativity along a short exact sequence**, division-free: for an equivariant
short exact sequence `1 → A → B → C → 1` of cyclic actions at one order `n`, with all six
graded pieces finite, `#Ĥ⁰(B) ⬝ #Ĥ¹(A) ⬝ #Ĥ¹(C) = #Ĥ⁰(A) ⬝ #Ĥ⁰(C) ⬝ #Ĥ¹(B)` — Serre's
`h(B) = h(A) h(C)`, counted through the exact hexagon
([Serre 1979, Chap. VIII, §4, Prop. 7, p.134][Serre1979];
[Yamaguchi 2026, `CyclicCohomology/Herbrand/HerbrandLowDegree/Core.lean:67`]
[Yamaguchi2026]). -/
theorem card_identity_of_exact
    {C : Type*} [CommGroup C]
    {σA : A ≃* A} {σB : B ≃* B} {σC : C ≃* C} {n : ℕ}
    (hσA : σA ^ n = 1) (hσB : σB ^ n = 1)
    {f : A →* B} {g : B →* C}
    (hf : ∀ a, f (σA a) = σB (f a)) (hg : ∀ b, g (σB b) = σC (g b))
    (hinj : Function.Injective f) (hsurj : Function.Surjective g)
    (hexact : g.ker = f.range)
    [Finite (H0 σA n)] [Finite (H1 σA n)] [Finite (H0 σB n)] [Finite (H1 σB n)]
    [Finite (H0 σC n)] [Finite (H1 σC n)] :
    Nat.card (H0 σB n) * Nat.card (H1 σA n) * Nat.card (H1 σC n) =
      Nat.card (H0 σA n) * Nat.card (H0 σC n) * Nat.card (H1 σB n) := by
  haveI : Finite (piece (diff σA) (norm σA n)) := ‹Finite (H0 σA n)›
  haveI : Finite (piece (norm σA n) (diff σA)) := ‹Finite (H1 σA n)›
  haveI : Finite (piece (diff σB) (norm σB n)) := ‹Finite (H0 σB n)›
  haveI : Finite (piece (norm σB n) (diff σB)) := ‹Finite (H1 σB n)›
  haveI : Finite (piece (diff σC) (norm σC n)) := ‹Finite (H0 σC n)›
  haveI : Finite (piece (norm σC n) (diff σC)) := ‹Finite (H1 σC n)›
  have habs := piece_card_identity
    (uA := diff σA) (vA := norm σA n) (uB := diff σB) (vB := norm σB n)
    (uC := diff σC) (vC := norm σC n)
    (diff_norm_apply hσA) (norm_diff_apply hσA)
    (diff_norm_apply hσB) (norm_diff_apply hσB)
    (fun a => map_diff_comm hf a) (fun a => map_norm_comm hf n a)
    (fun b => map_diff_comm hg b) (fun b => map_norm_comm hg n b)
    hinj hsurj hexact
  exact habs.symm

/-- **Finiteness propagates to the middle** of an equivariant short exact sequence: with
both graded pieces of `A` and of `C` finite, both graded pieces of `B` are finite — the
half of Serre's "two of the three defined implies the third" that the norm-index
computation consumes, since there the middle piece's finiteness is the thing being
computed; the remaining two thirds of the proposition are deliberately not stated here
([Serre 1979, Chap. VIII, §4, Prop. 7, p.134][Serre1979]). -/
theorem finite_of_exact
    {C : Type*} [CommGroup C]
    {σA : A ≃* A} {σB : B ≃* B} {σC : C ≃* C} {n : ℕ}
    (hσB : σB ^ n = 1)
    {f : A →* B} {g : B →* C}
    (hf : ∀ a, f (σA a) = σB (f a)) (hg : ∀ b, g (σB b) = σC (g b))
    (hinj : Function.Injective f) (hsurj : Function.Surjective g)
    (hexact : g.ker = f.range)
    [Finite (H0 σA n)] [Finite (H1 σA n)] [Finite (H0 σC n)] [Finite (H1 σC n)] :
    Finite (H0 σB n) ∧ Finite (H1 σB n) := by
  haveI : Finite (piece (diff σA) (norm σA n)) := ‹Finite (H0 σA n)›
  haveI : Finite (piece (norm σA n) (diff σA)) := ‹Finite (H1 σA n)›
  haveI : Finite (piece (diff σC) (norm σC n)) := ‹Finite (H0 σC n)›
  haveI : Finite (piece (norm σC n) (diff σC)) := ‹Finite (H1 σC n)›
  constructor
  · exact piece_finite_middle (diff_norm_apply hσB)
      (fun a => map_diff_comm hf a) (fun a => map_norm_comm hf n a)
      (fun b => map_diff_comm hg b) (fun b => map_norm_comm hg n b)
      hinj hsurj hexact
  · exact piece_finite_middle (norm_diff_apply hσB)
      (fun a => map_norm_comm hf n a) (fun a => map_diff_comm hf a)
      (fun b => map_norm_comm hg n b) (fun b => map_diff_comm hg b)
      hinj hsurj hexact

/-- **Transport along an intertwining isomorphism**: isomorphic actions have even graded
pieces of equal cardinality — the staged computations on literal carriers reach the
consumer's carrier through this ([Serre 1979, Chap. VIII, §4, p.133][Serre1979]). -/
theorem card_H0_congr {σA : A ≃* A} {σB : B ≃* B} (n : ℕ) (e : A ≃* B)
    (he : ∀ a, e (σA a) = σB (e a)) :
    Nat.card (H0 σA n) = Nat.card (H0 σB n) :=
  piece_card_congr e (fun a => map_diff_comm (f := (e : A →* B)) (fun b => he b) a)
    (fun a => map_norm_comm (f := (e : A →* B)) (fun b => he b) n a)

/-- **Transport along an intertwining isomorphism**, odd piece
([Serre 1979, Chap. VIII, §4, p.133][Serre1979]). -/
theorem card_H1_congr {σA : A ≃* A} {σB : B ≃* B} (n : ℕ) (e : A ≃* B)
    (he : ∀ a, e (σA a) = σB (e a)) :
    Nat.card (H1 σA n) = Nat.card (H1 σB n) :=
  piece_card_congr e (fun a => map_norm_comm (f := (e : A →* B)) (fun b => he b) n a)
    (fun a => map_diff_comm (f := (e : A →* B)) (fun b => he b) a)

end Concrete

/- Cardinality of a subgroup quotient against an honest subgroup: when `N ≤ K`, the
quotient `K ⧸ N.subgroupOf K` counts as `#K / #N`, in product form. -/
private theorem card_quotient_subgroupOf_mul {A : Type*} [CommGroup A] {K N : Subgroup A}
    (h : N ≤ K) [Finite K] :
    Nat.card (K ⧸ N.subgroupOf K) * Nat.card N = Nat.card K := by
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv]
  exact (Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf K)).symm

section Finiteness

variable {A : Type*} [CommGroup A] {σ : A ≃* A} {n : ℕ}

/-- Norms land in the difference kernel: `im N ≤ ker D`. -/
theorem range_norm_le_ker_diff (hσ : σ ^ n = 1) : (norm σ n).range ≤ (diff σ).ker := by
  rintro _ ⟨a, rfl⟩
  exact MonoidHom.mem_ker.mpr (diff_norm_apply hσ a)

/-- Differences land in the norm kernel: `im D ≤ ker N`. -/
theorem range_diff_le_ker_norm (hσ : σ ^ n = 1) : (diff σ).range ≤ (norm σ n).ker := by
  rintro _ ⟨a, rfl⟩
  exact MonoidHom.mem_ker.mpr (norm_diff_apply hσ a)

/-- **A finite module has equal graded pieces**: `#Ĥ⁰ = #Ĥ¹`, Serre's Proposition 8 in
counting form — `#ker D ⬝ #im D = #A = #ker N ⬝ #im N`, and the two quotients divide out
crosswise ([Serre 1979, Chap. VIII, §4, Prop. 8, p.134][Serre1979]). -/
theorem card_H0_eq_card_H1_of_finite (hσ : σ ^ n = 1) [Finite A] :
    Nat.card (H0 σ n) = Nat.card (H1 σ n) := by
  have h0 := card_quotient_subgroupOf_mul (range_norm_le_ker_diff (σ := σ) hσ)
  have h1 := card_quotient_subgroupOf_mul (range_diff_le_ker_norm (σ := σ) hσ)
  have hid0 : Nat.card (H0 σ n) =
      Nat.card ((diff σ).ker ⧸ (norm σ n).range.subgroupOf (diff σ).ker) := rfl
  have hid1 : Nat.card (H1 σ n) =
      Nat.card ((norm σ n).ker ⧸ (diff σ).range.subgroupOf (norm σ n).ker) := rfl
  rw [hid0, hid1]
  have hD := card_ker_mul_card_range' (diff σ)
  have hN := card_ker_mul_card_range' (norm σ n)
  set q0 := Nat.card ((diff σ).ker ⧸ (norm σ n).range.subgroupOf (diff σ).ker)
  set q1 := Nat.card ((norm σ n).ker ⧸ (diff σ).range.subgroupOf (norm σ n).ker)
  have key : q0 * (Nat.card (norm σ n).range * Nat.card (diff σ).range) =
      q1 * (Nat.card (norm σ n).range * Nat.card (diff σ).range) := by
    calc q0 * (Nat.card (norm σ n).range * Nat.card (diff σ).range)
        = (q0 * Nat.card (norm σ n).range) * Nat.card (diff σ).range := by ring
      _ = Nat.card (diff σ).ker * Nat.card (diff σ).range := by rw [h0]
      _ = Nat.card A := hD
      _ = Nat.card (norm σ n).ker * Nat.card (norm σ n).range := hN.symm
      _ = (q1 * Nat.card (diff σ).range) * Nat.card (norm σ n).range := by rw [h1]
      _ = q1 * (Nat.card (norm σ n).range * Nat.card (diff σ).range) := by ring
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos Nat.card_pos Nat.card_pos) key

end Finiteness

/-!
Stability: a subgroup preserved by the action carries the restricted automorphism, its
quotient the descended one, and a stable subgroup of finite index leaves the graded counts
unchanged — Serre's Corollary to Propositions 7 and 8.
-/

/-- The restriction of the action to a stable subgroup. Stability is asked in both
directions because no order for `σ` is data here, and without one the inverse direction is
not a consequence ([Serre 1979, Chap. VIII, §4, p.134][Serre1979]). -/
def stableRestrict (σ : A ≃* A) (N : Subgroup A) (hN : ∀ x ∈ N, σ x ∈ N)
    (hN' : ∀ x ∈ N, σ.symm x ∈ N) : ↥N ≃* ↥N where
  toFun x := ⟨σ x, hN x x.2⟩
  invFun x := ⟨σ.symm x, hN' x x.2⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply (x : A))
  right_inv x := Subtype.ext (σ.apply_symm_apply (x : A))
  map_mul' x y := Subtype.ext (map_mul σ (x : A) (y : A))

/-- The descent of the action to the quotient by a stable subgroup
([Serre 1979, Chap. VIII, §4, p.134][Serre1979]). -/
noncomputable def stableQuotient (σ : A ≃* A) (N : Subgroup A) (hN : ∀ x ∈ N, σ x ∈ N)
    (hN' : ∀ x ∈ N, σ.symm x ∈ N) : (A ⧸ N) ≃* (A ⧸ N) := by
  refine MonoidHom.toMulEquiv
    (QuotientGroup.map N N (σ : A →* A) (fun x hx => hN x hx))
    (QuotientGroup.map N N (σ.symm : A →* A) (fun x hx => hN' x hx)) ?_ ?_
  · ext a
    simp
  · ext a
    simp

/-- The restricted action inherits `σ ^ n = 1`. -/
theorem stableRestrict_pow (σ : A ≃* A) {n : ℕ} (hσ : σ ^ n = 1) (N : Subgroup A)
    (hN : ∀ x ∈ N, σ x ∈ N) (hN' : ∀ x ∈ N, σ.symm x ∈ N) :
    stableRestrict σ N hN hN' ^ n = 1 := by
  ext x
  have hpow : ∀ (k : ℕ) (y : ↥N),
      ((stableRestrict σ N hN hN' ^ k) y : A) = (σ ^ k) (y : A) := by
    intro k
    induction k with
    | zero => intro y; rfl
    | succ m ih =>
      intro y
      have h1 : (stableRestrict σ N hN hN' ^ (m + 1)) y =
          (stableRestrict σ N hN hN' ^ m) (stableRestrict σ N hN hN' y) := by
        rw [pow_succ]
        rfl
      have h2 : (σ ^ (m + 1) : A ≃* A) (y : A) = (σ ^ m : A ≃* A) (σ (y : A)) := by
        rw [pow_succ]
        rfl
      rw [h1, h2, ih (stableRestrict σ N hN hN' y)]
      rfl
  have := hpow n x
  rw [hσ] at this
  exact this

/-- The descended action inherits `σ ^ n = 1`. -/
theorem stableQuotient_pow (σ : A ≃* A) {n : ℕ} (hσ : σ ^ n = 1) (N : Subgroup A)
    (hN : ∀ x ∈ N, σ x ∈ N) (hN' : ∀ x ∈ N, σ.symm x ∈ N) :
    stableQuotient σ N hN hN' ^ n = 1 := by
  have hpow : ∀ (k : ℕ) (b : A), ((stableQuotient σ N hN hN' ^ k)
      (QuotientGroup.mk b) : A ⧸ N) = QuotientGroup.mk ((σ ^ k : A ≃* A) b) := by
    intro k
    induction k with
    | zero => intro b; rfl
    | succ m ih =>
      intro b
      have h1 : (stableQuotient σ N hN hN' ^ (m + 1)) (QuotientGroup.mk b) =
          (stableQuotient σ N hN hN' ^ m)
            (stableQuotient σ N hN hN' (QuotientGroup.mk b)) := by
        rw [pow_succ]
        rfl
      have h2 : stableQuotient σ N hN hN' (QuotientGroup.mk b) =
          QuotientGroup.mk (σ b) := rfl
      have h3 : (σ ^ (m + 1) : A ≃* A) b = (σ ^ m : A ≃* A) (σ b) := by
        rw [pow_succ]
        rfl
      rw [h1, h2, ih (σ b), h3]
  ext x
  induction x using QuotientGroup.induction_on with
  | H a =>
    have := hpow n a
    rw [hσ] at this
    exact this

/-- **A stable subgroup of finite index has the same graded counts**: the inclusion case of
Serre's Corollary, in counting form, `#Ĥ⁰(A) ⬝ #Ĥ¹(N) = #Ĥ⁰(N) ⬝ #Ĥ¹(A)` — the sequence
`1 → N → A → A ⧸ N → 1` against
`Atlas.Knowledge.HerbrandQuotient.card_identity_of_exact`, with the finite
quotient's two pieces cancelling by
`Atlas.Knowledge.HerbrandQuotient.card_H0_eq_card_H1_of_finite`
([Serre 1979, Chap. VIII, §4, Corollary, p.134][Serre1979]). -/
theorem card_identity_of_finiteIndex
    {σ : A ≃* A} {n : ℕ} (hσ : σ ^ n = 1) (N : Subgroup A)
    (hN : ∀ x ∈ N, σ x ∈ N) (hN' : ∀ x ∈ N, σ.symm x ∈ N)
    [Finite (A ⧸ N)]
    [Finite (H0 (stableRestrict σ N hN hN') n)]
    [Finite (H1 (stableRestrict σ N hN hN') n)]
    [Finite (H0 σ n)] [Finite (H1 σ n)] :
    Nat.card (H0 σ n) * Nat.card (H1 (stableRestrict σ N hN hN') n) =
      Nat.card (H0 (stableRestrict σ N hN hN') n) * Nat.card (H1 σ n) := by
  have hexact : (QuotientGroup.mk' N).ker = N.subtype.range := by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
  have hcard := card_identity_of_exact
    (σA := stableRestrict σ N hN hN') (σB := σ) (σC := stableQuotient σ N hN hN')
    (stableRestrict_pow σ hσ N hN hN') hσ
    (f := N.subtype) (g := QuotientGroup.mk' N)
    (fun x => rfl) (fun b => rfl)
    N.subtype_injective (QuotientGroup.mk'_surjective N) hexact
  have hCeq := card_H0_eq_card_H1_of_finite
    (σ := stableQuotient σ N hN hN') (stableQuotient_pow σ hσ N hN hN')
  rw [hCeq] at hcard
  have hpos : 0 < Nat.card (H1 (stableQuotient σ N hN hN') n) := Nat.card_pos
  have h1 : Nat.card (H0 σ n) * Nat.card (H1 (stableRestrict σ N hN hN') n) *
      Nat.card (H1 (stableQuotient σ N hN hN') n) =
      Nat.card (H0 (stableRestrict σ N hN hN') n) * Nat.card (H1 σ n) *
        Nat.card (H1 (stableQuotient σ N hN hN') n) :=
    hcard.trans (by ring)
  exact Nat.eq_of_mul_eq_mul_right hpos h1

/-!
The trivial module `ℤ`: the graded pieces of the trivial action on `Multiplicative ℤ` count
`n` and `1` — the value the norm-index computation reads off the valuation sequence.
-/

private theorem norm_refl_int (n : ℕ) (a : Multiplicative ℤ) :
    norm (MulEquiv.refl (Multiplicative ℤ)) n a = a ^ n := by
  rw [norm_apply]
  have h : ∀ i, ((MulEquiv.refl (Multiplicative ℤ)) ^ i) a = a := by
    intro i
    induction i with
    | zero => rfl
    | succ k ih => rw [pow_succ]; exact ih
  simp [h, Finset.prod_const]

/-- **`Ĥ⁰` of the trivial action on `ℤ` counts `n`**: the difference kernel is everything,
the norms are the `n`-th powers, and reduction to `ZMod n` is onto with kernel exactly
them. At `n = 0` the quotient is infinite and the equation reads through the `Nat.card`
junk value
([Serre 1979, Chap. VIII, §4, p.133][Serre1979];
[Yamaguchi 2026,
`LocalClassFieldTheory/ClassFormation/ValueGroupCohomology.lean:132`][Yamaguchi2026]). -/
theorem card_H0_int (n : ℕ) :
    Nat.card (H0 (MulEquiv.refl (Multiplicative ℤ)) n) = n := by
  set D := diff (MulEquiv.refl (Multiplicative ℤ)) with hD
  set N := norm (MulEquiv.refl (Multiplicative ℤ)) n with hN
  let f : Multiplicative ℤ →* Multiplicative (ZMod n) :=
    AddMonoidHom.toMultiplicative (Int.castAddHom (ZMod n))
  let φ : D.ker →* Multiplicative (ZMod n) := f.comp D.ker.subtype
  have hφ : ∀ x : D.ker, Multiplicative.toAdd (φ x) =
      ((Multiplicative.toAdd (x : Multiplicative ℤ) : ℤ) : ZMod n) :=
    fun x => rfl
  have hsurj : Function.Surjective φ := by
    intro z
    refine ⟨⟨Multiplicative.ofAdd (Multiplicative.toAdd z).cast, ?_⟩, ?_⟩
    · rw [hD, MonoidHom.mem_ker]
      apply Multiplicative.toAdd.injective
      simp [diff_apply]
    · apply Multiplicative.toAdd.injective
      rw [hφ]
      simp only [toAdd_ofAdd]
      exact ZMod.intCast_zmod_cast (Multiplicative.toAdd z)
  have hker : φ.ker = N.range.subgroupOf D.ker := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h0 : ((Multiplicative.toAdd (x : Multiplicative ℤ) : ℤ) : ZMod n) = 0 := by
        rw [← hφ, hx, toAdd_one]
      obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
      refine ⟨Multiplicative.ofAdd c, ?_⟩
      rw [hN, norm_refl_int]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_ofAdd, hc, nsmul_eq_mul]
    · rintro ⟨a, ha⟩
      rw [hN, norm_refl_int] at ha
      have hdvd : (n : ℤ) ∣ Multiplicative.toAdd (x : Multiplicative ℤ) := by
        refine ⟨Multiplicative.toAdd a, ?_⟩
        have := congrArg Multiplicative.toAdd ha
        rw [toAdd_pow, nsmul_eq_mul] at this
        exact this.symm
      apply Multiplicative.toAdd.injective
      rw [hφ, toAdd_one]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hdvd
  have hcongr := Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective φ hsurj).toEquiv
  rw [hker] at hcongr
  have hfinal : Nat.card (H0 (MulEquiv.refl (Multiplicative ℤ)) n) =
      Nat.card (Multiplicative (ZMod n)) := hcongr
  rw [hfinal, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- **`Ĥ¹` of the trivial action on `ℤ` is trivial**: the norm is the injective `n`-th
power ([Serre 1979, Chap. VIII, §4, p.133][Serre1979];
[Yamaguchi 2026,
`LocalClassFieldTheory/ClassFormation/ValueGroupCohomology.lean:155`][Yamaguchi2026]). -/
theorem card_H1_int (n : ℕ) (hn : n ≠ 0) :
    Nat.card (H1 (MulEquiv.refl (Multiplicative ℤ)) n) = 1 := by
  have hker : (norm (MulEquiv.refl (Multiplicative ℤ)) n).ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [MonoidHom.mem_ker, norm_refl_int] at hx
    have h1 : (n : ℤ) * Multiplicative.toAdd x = 0 := by
      have := congrArg Multiplicative.toAdd hx
      rwa [toAdd_pow, toAdd_one, nsmul_eq_mul] at this
    have hx0 : Multiplicative.toAdd x = 0 := by
      rcases mul_eq_zero.mp h1 with h | h
      · exact absurd (by exact_mod_cast h) hn
      · exact h
    apply Multiplicative.toAdd.injective
    simpa using hx0
  haveI : Subsingleton ((norm (MulEquiv.refl (Multiplicative ℤ)) n).ker) := by
    rw [hker]
    infer_instance
  haveI : Subsingleton (H1 (MulEquiv.refl (Multiplicative ℤ)) n) := by
    unfold H1
    exact Quotient.instSubsingletonQuotient _
  exact Nat.card_unique

/-!
The co-induced module: the shift action on `ZMod n → M` has both graded pieces trivial —
the elementary cyclic instance of "a co-induced module has vanishing cohomology", which is
what a normal-basis lattice will be measured against.
-/

variable {M : Type*} [CommGroup M] (n : ℕ)

/-- The **shift** of the co-induced module `ZMod n → M`: precomposition with `+1`
([Serre 1979, Chap. VII, §5, Exercise, pp.116–117][Serre1979]). -/
def shiftAut : (ZMod n → M) ≃* (ZMod n → M) where
  toFun f := fun j => f (j + 1)
  invFun f := fun j => f (j - 1)
  left_inv f := by funext j; simp
  right_inv f := by funext j; simp
  map_mul' f g := rfl

/-- Iterated shifts translate the argument. -/
theorem shiftAut_pow_apply (k : ℕ) :
    ∀ f : ZMod n → M, ((shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) ^ k) f =
      fun j => f (j + k) := by
  induction k with
  | zero => intro f; funext j; simp
  | succ m ih =>
    intro f
    have h : ((shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) ^ (m + 1)) f =
        ((shiftAut n) ^ m) (shiftAut n f) := by
      rw [pow_succ]
      rfl
    rw [h, ih (shiftAut n f)]
    funext j
    change f (j + m + 1) = f (j + (m + 1 : ℕ))
    congr 1
    push_cast
    ring

/-- The shift has order dividing `n`. -/
theorem shiftAut_pow_n : (shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) ^ n = 1 := by
  ext f j
  rw [shiftAut_pow_apply n n f]
  change f (j + (n : ZMod n)) = f j
  rw [ZMod.natCast_self, add_zero]

/-- The norm of the shift action, pointwise: the product over the translates. -/
theorem norm_shiftAut_apply (f : ZMod n → M) (j : ZMod n) :
    norm (shiftAut n) n f j = ∏ i ∈ Finset.range n, f (j + i) := by
  rw [norm_apply]
  rw [show (∏ i ∈ Finset.range n, ((shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) ^ i) f) j =
    ∏ i ∈ Finset.range n, (((shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) ^ i) f) j from by
      simp [Finset.prod_apply]]
  exact Finset.prod_congr rfl fun i _ => by rw [shiftAut_pow_apply n i f]

/-- A member of the difference kernel of the shift is constant. -/
theorem shiftAut_diff_ker [NeZero n] (f : ZMod n → M)
    (hf : f ∈ (diff (shiftAut n)).ker) (j : ZMod n) :
    f j = f 0 := by
  rw [MonoidHom.mem_ker] at hf
  have hstep : ∀ j : ZMod n, f (j + 1) = f j := by
    intro j
    have := congrFun (congrArg (fun h => h * f) hf) j
    simpa [diff_apply, shiftAut] using this
  obtain ⟨k, rfl⟩ := ZMod.natCast_zmod_surjective (n := n) j
  induction k with
  | zero => norm_num
  | succ m ih =>
    rw [show ((m + 1 : ℕ) : ZMod n) = (m : ZMod n) + 1 by push_cast; ring, hstep]
    exact ih

/-- **`Ĥ⁰` of the co-induced module is trivial**: every difference-kernel member is the
norm of the delta function at its constant value
([Serre 1979, Chap. VII, §5, Exercise, pp.116–117, read through the two-periodicity of
Chap. VIII, §4][Serre1979];
[Yamaguchi 2026, `CyclicCohomology/Herbrand/Induced.lean:703`, specialized at the trivial
subgroup][Yamaguchi2026]). -/
theorem shiftAut_norm_range_subgroupOf_eq_top [NeZero n] :
    (norm (shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) n).range.subgroupOf
      (diff (shiftAut n : (ZMod n → M) ≃* (ZMod n → M))).ker = ⊤ := by
  rw [Subgroup.eq_top_iff']
  rintro ⟨f, hf⟩
  rw [Subgroup.mem_subgroupOf]
  set c := f 0 with hc
  refine ⟨fun j => if j = 0 then c else 1, ?_⟩
  funext j
  rw [norm_shiftAut_apply]
  have hval : ((-j).val : ZMod n) = -j := ZMod.natCast_rightInverse (-j)
  have hmem : (-j).val ∈ Finset.range n := Finset.mem_range.mpr (ZMod.val_lt (-j))
  rw [Finset.prod_eq_single ((-j).val)
    (fun i hi hne => by
      have hjz : j + (i : ZMod n) ≠ 0 := by
        intro h0
        have hi' : (i : ZMod n) = -j := by linear_combination h0
        have : (-j).val = i := by
          rw [← hi', ZMod.val_cast_of_lt (Finset.mem_range.mp hi)]
        exact hne this.symm
      simp [hjz])
    (fun habs => absurd hmem habs)]
  have hzero : j + ((-j).val : ZMod n) = 0 := by
    rw [hval]
    ring
  rw [hzero]
  simp only [reduceIte]
  exact (shiftAut_diff_ker n f hf j).symm

/-- **`Ĥ¹` of the co-induced module is trivial**: a norm-kernel member telescopes into a
difference through its running products
([Serre 1979, Chap. VII, §5, Exercise, pp.116–117, read through the two-periodicity of
Chap. VIII, §4][Serre1979];
[Yamaguchi 2026, `CyclicCohomology/Herbrand/Induced.lean:1095`, specialized at the trivial
subgroup][Yamaguchi2026]). -/
theorem shiftAut_ker_norm_le_range_diff [NeZero n] :
    (norm (shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) n).ker ≤
      (diff (shiftAut n : (ZMod n → M) ≃* (ZMod n → M))).range := by
  intro f hf
  rw [MonoidHom.mem_ker] at hf
  have hprod : ∏ i ∈ Finset.range n, f (i : ZMod n) = 1 := by
    have h0 := congrFun hf (0 : ZMod n)
    rw [show ((norm (shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) n) f) (0 : ZMod n) =
      ∏ i ∈ Finset.range n, f ((0 : ZMod n) + i) from norm_shiftAut_apply n f 0] at h0
    simpa using h0
  rcases eq_or_ne n 1 with rfl | hn1
  · have hf1 : f = 1 := by
      funext j
      have hj := congrFun hf j
      rw [show ((norm (shiftAut 1 : (ZMod 1 → M) ≃* (ZMod 1 → M)) 1) f) j =
        ∏ i ∈ Finset.range 1, f (j + i) from norm_shiftAut_apply 1 f j] at hj
      simpa using hj
    exact ⟨1, by rw [map_one, hf1]⟩
  have hn2 : 1 < n := by
    have := NeZero.pos n
    omega
  set g : ZMod n → M := fun j => ∏ i ∈ Finset.range j.val, f (i : ZMod n) with hg
  refine ⟨g, ?_⟩
  funext j
  rw [diff_apply]
  change (shiftAut n) g j * g⁻¹ j = f j
  rw [show (shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) g j = g (j + 1) from rfl,
    show g⁻¹ j = (g j)⁻¹ from rfl]
  haveI : Fact (1 < n) := ⟨hn2⟩
  have hjval : (j + 1).val = (j.val + 1) % n := by
    rw [ZMod.val_add, ZMod.val_one n]
  by_cases hj : j.val + 1 < n
  · have hval : (j + 1).val = j.val + 1 := by
      rw [hjval, Nat.mod_eq_of_lt hj]
    rw [hg]
    simp only [hval, Finset.prod_range_succ]
    rw [ZMod.natCast_rightInverse j,
      mul_comm (∏ x ∈ Finset.range j.val, f (x : ZMod n)) (f j), mul_assoc,
      mul_inv_cancel, mul_one]
  · have hjtop : j.val + 1 = n := by
      have := ZMod.val_lt j
      omega
    have hval : (j + 1).val = 0 := by
      rw [hjval, hjtop, Nat.mod_self]
    have hsplit : (∏ i ∈ Finset.range j.val, f (i : ZMod n)) *
        f ((j.val : ℕ) : ZMod n) = 1 := by
      rw [← Finset.prod_range_succ, hjtop]
      exact hprod
    have hlast : f (((j.val : ℕ) : ZMod n)) = f j := by
      rw [ZMod.natCast_rightInverse j]
    rw [hg]
    simp only [hval, Finset.range_zero, Finset.prod_empty]
    rw [hlast] at hsplit
    rw [one_mul]
    exact inv_eq_of_mul_eq_one_right hsplit

/-- **`Ĥ⁰` of the co-induced module counts `1`**
([Serre 1979, Chap. VII, §5, Exercise, pp.116–117, read through the two-periodicity of
Chap. VIII, §4][Serre1979]). -/
theorem card_H0_shiftAut [NeZero n] :
    Nat.card (H0 (shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) n) = 1 := by
  haveI : Subsingleton (H0 (shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) n) := by
    change Subsingleton ((diff (shiftAut n : (ZMod n → M) ≃* (ZMod n → M))).ker ⧸
      (norm (shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) n).range.subgroupOf
        (diff (shiftAut n : (ZMod n → M) ≃* (ZMod n → M))).ker)
    rw [shiftAut_norm_range_subgroupOf_eq_top]
    exact QuotientGroup.subsingleton_quotient_top
  exact Nat.card_unique

/-- **`Ĥ¹` of the co-induced module counts `1`**
([Serre 1979, Chap. VII, §5, Exercise, pp.116–117, read through the two-periodicity of
Chap. VIII, §4][Serre1979]). -/
theorem card_H1_shiftAut [NeZero n] :
    Nat.card (H1 (shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) n) = 1 := by
  haveI : Subsingleton (H1 (shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) n) := by
    change Subsingleton ((norm (shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) n).ker ⧸
      (diff (shiftAut n : (ZMod n → M) ≃* (ZMod n → M))).range.subgroupOf
        (norm (shiftAut n : (ZMod n → M) ≃* (ZMod n → M)) n).ker)
    rw [Subgroup.subgroupOf_eq_top.mpr (shiftAut_ker_norm_le_range_diff n)]
    exact QuotientGroup.subsingleton_quotient_top
  exact Nat.card_unique

end HerbrandQuotient

/-- The **Herbrand quotient** of the cyclic action: `q = #Ĥ⁰ / #Ĥ¹` in `ℚ`, with the
`Nat.card` junk value `0` on an infinite piece — every consuming statement re-imposes
finiteness ([Serre 1979, Chap. VIII, §4, p.133][Serre1979];
[Yamaguchi 2026, `CyclicCohomology/Herbrand/HerbrandLowDegree/Core.lean:31`]
[Yamaguchi2026]). -/
noncomputable def herbrandQuotient {A : Type*} [CommGroup A] (σ : A ≃* A) (n : ℕ) : ℚ :=
  (Nat.card (HerbrandQuotient.H0 σ n) : ℚ) / (Nat.card (HerbrandQuotient.H1 σ n) : ℚ)

/-- **The Herbrand quotient of a finite module is `1`**
([Serre 1979, Chap. VIII, §4, Prop. 8, p.134][Serre1979]). -/
theorem herbrandQuotient_finite {A : Type*} [CommGroup A] {σ : A ≃* A} {n : ℕ}
    (hσ : σ ^ n = 1) [Finite A] : herbrandQuotient σ n = 1 := by
  unfold herbrandQuotient
  rw [HerbrandQuotient.card_H0_eq_card_H1_of_finite hσ]
  exact div_self (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- **The Herbrand quotient is multiplicative** along an equivariant short exact sequence
with finite graded pieces: `q(B) = q(A) ⬝ q(C)`
([Serre 1979, Chap. VIII, §4, Prop. 7, p.134][Serre1979];
[Yamaguchi 2026, `CyclicCohomology/Herbrand/HerbrandLowDegree/Core.lean:67`]
[Yamaguchi2026]). -/
theorem herbrandQuotient_mul {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]
    {σA : A ≃* A} {σB : B ≃* B} {σC : C ≃* C} {n : ℕ}
    (hσA : σA ^ n = 1) (hσB : σB ^ n = 1)
    {f : A →* B} {g : B →* C}
    (hf : ∀ a, f (σA a) = σB (f a)) (hg : ∀ b, g (σB b) = σC (g b))
    (hinj : Function.Injective f) (hsurj : Function.Surjective g)
    (hexact : g.ker = f.range)
    [Finite (HerbrandQuotient.H0 σA n)] [Finite (HerbrandQuotient.H1 σA n)]
    [Finite (HerbrandQuotient.H0 σB n)] [Finite (HerbrandQuotient.H1 σB n)]
    [Finite (HerbrandQuotient.H0 σC n)] [Finite (HerbrandQuotient.H1 σC n)] :
    herbrandQuotient σB n = herbrandQuotient σA n * herbrandQuotient σC n := by
  have hcard := HerbrandQuotient.card_identity_of_exact hσA hσB hf hg hinj hsurj hexact
  have hA1 : ((Nat.card (HerbrandQuotient.H1 σA n) : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hB1 : ((Nat.card (HerbrandQuotient.H1 σB n) : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hC1 : ((Nat.card (HerbrandQuotient.H1 σC n) : ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  unfold herbrandQuotient
  rw [div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
  · have hq : ((Nat.card (HerbrandQuotient.H0 σB n) *
        Nat.card (HerbrandQuotient.H1 σA n) *
        Nat.card (HerbrandQuotient.H1 σC n) : ℕ) : ℚ) =
        ((Nat.card (HerbrandQuotient.H0 σA n) *
        Nat.card (HerbrandQuotient.H0 σC n) *
        Nat.card (HerbrandQuotient.H1 σB n) : ℕ) : ℚ) := by
      exact_mod_cast hcard
    push_cast at hq ⊢
    linarith [hq]

end Atlas.Knowledge
