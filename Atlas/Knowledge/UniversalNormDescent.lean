import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.RelativeNormConjugation
import Atlas.Knowledge.RelativeNormLaws

/-!
# Universal norm descent

The representation-theoretic lifting and correction calculation of the
abstract reciprocity construction, with the norm, action, and iterate
identities it requires: equation `(*)` says the class of `u` in
coinvariants is fixed by `φ`; norm surjectivity on fixed elements — the
content of `Ĥ⁰ = 0` — produces the barred lifts, and the norm-kernel
eliminator — the content of `Ĥ⁻¹ = 0` — the correction term `y` (#104).

## Main definitions

* `conjugateStableAction` — the conjugation action transported back to a
  field it stabilizes.

## Main statements

* `relativeNorm_conjugateStableAction` — the relative norm is
  equivariant for a conjugation stabilizing both fields; proved.
* `universalNormDescent_cyclic_lift_and_correction` — the calculation
  in the first half of the universal norm-descent lemma; proved.
* `rep_norm_eq_generatorIterateSum` — the norm as the iterate sum of any
  pointwise-equal endomorphism; proved.

## Implementation notes

The cyclic lift-and-correction takes its two vanishing inputs
elementwise — every generator-fixed element is a norm, every norm-zero
element is a `ρ(g) − 1`-difference — where the source hypothesizes
`Limits.IsZero` on Mathlib's Tate cohomology of the restricted
representation: `tateCohomology` binds ring and group in one
`{k G : Type u}` universe block, so the cohomological spelling would
force the ambient group into `Type 0` at the layer's `ℤ` coefficients
(`Rep` itself no longer pins — only the homological layer ties the
universes). The layer's `tateVanishingNormSurjectivity` and
`tateVanishingNormKernel` record exactly this extraction, so at a
`Type 0` group the source's hypotheses are recovered by composing with
them; the generation hypothesis rides inside the elementwise inputs —
they are stated at the chosen `g` — so `hg` leaves the signature too.
The theorem has no consumer yet, so no wrapper at the old signature is
kept. The per-declaration group binders sit at `Type u` with the
class-formation stock since the #104 hoist's mechanical flip — nothing
here has forced the pin since the vanishing inputs went elementwise. The
relative subgroup is the layer's `Subgroup.subgroupOf` spelling, and the
conjugate extension's finiteness instance takes no containment, as #137
generalized it. The source's `open scoped BigOperators`, a no-op in
current Mathlib, is dropped.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u v

/- The norm over a finite normal subgroup commutes with every ambient
group action — the equivariance used when the construction applies the
norm to equation `(*)` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean:27`]
[Yamaguchi2026]). -/
private theorem restricted_norm_action
    {R : Type u} [Group R] (H : Subgroup R) [H.Normal] [Fintype H]
    (B : Rep ℤ R) (r : R) (x : B.V) :
    (∑ h : H, B.ρ h.1 (B.ρ r x)) =
      B.ρ r (∑ h : H, B.ρ h.1 x) := by
  rw [map_sum]
  let e : H ≃ H := (MulAut.conjNormal r).symm.toEquiv
  calc
    (∑ h : H, B.ρ h.1 (B.ρ r x)) =
        ∑ h : H, B.ρ r (B.ρ (e h).1 x) := by
      apply Finset.sum_congr rfl
      intro h _
      have he : (e h).1 = r⁻¹ * h.1 * r := by
        exact MulAut.conjNormal_symm_apply r h
      calc
        B.ρ h.1 (B.ρ r x) = B.ρ (h.1 * r) x := by
          rw [map_mul]
          rfl
        _ = B.ρ (r * (e h).1) x := by
          rw [he]
          simp [mul_assoc]
        _ = B.ρ r (B.ρ (e h).1 x) := by
          rw [map_mul]
          rfl
    _ = ∑ h : H, B.ρ r (B.ρ h.1 x) := by
      exact e.sum_comp (fun h : H => B.ρ r (B.ρ h.1 x))

/- The restricted representation's norm commutes with the ambient action
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean:54`]
[Yamaguchi2026]). -/
private theorem restricted_rep_norm_action
    {R : Type u} [Group R] (H : Subgroup R) [H.Normal] [Fintype H]
    (B : Rep ℤ R) (r : R) (x : B.V) :
    let U : Rep ℤ H := Rep.res H.subtype B
    U.norm.hom (B.ρ r x) = B.ρ r (U.norm.hom x) := by
  let U : Rep ℤ H := Rep.res H.subtype B
  simpa [Rep.norm, Representation.norm] using
    restricted_norm_action H B r x

/-- **The conjugation action transported back to a field it stabilizes**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean:65`]
[Yamaguchi2026]). -/
noncomputable def conjugateStableAction
    {R : Type u} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) : ambientFixedAddSubgroup B F :=
  hF ▸ conjugateFixedElement B F s a

/- Transport along an equality of fields leaves the ambient value alone
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean:72`]
[Yamaguchi2026]). -/
private theorem transport_fixed_coe
    {R : Type u} [Group R] [TopologicalSpace R]
    (B : Rep ℤ R) (F' F : ClosedSubgroup R) (h : F' = F)
    (a : ambientFixedAddSubgroup B F') :
    (((h ▸ a : ambientFixedAddSubgroup B F) : B.V)) = a.1 := by
  cases h
  rfl

/- The relative norm commutes with transport along equalities of both
fields ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean:80`]
[Yamaguchi2026]). -/
private theorem relativeNorm_transport_coe
    {R : Type u} [Group R] [TopologicalSpace R]
    (B : Rep ℤ R)
    (F' E' F E : ClosedSubgroup R)
    (hF : F' = F) (hE : E' = E)
    (hE'F' : E'.toSubgroup ≤ F'.toSubgroup)
    (hEF : E.toSubgroup ≤ F.toSubgroup)
    [Finite (F'.toSubgroup ⧸ E'.toSubgroup.subgroupOf F'.toSubgroup)]
    [Finite (F.toSubgroup ⧸ E.toSubgroup.subgroupOf F.toSubgroup)]
    (a : ambientFixedAddSubgroup B E') :
    ((relativeNorm B F E hEF (hE ▸ a) : ambientFixedAddSubgroup B F) :
        B.V) =
      ((relativeNorm B F' E' hE'F' a : ambientFixedAddSubgroup B F') :
        B.V) := by
  cases hF
  cases hE
  rfl

/-- The conjugation-stable action agrees with its ambient action after
coercion ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean:98`]
[Yamaguchi2026]). -/
@[simp]
theorem conjugateStableAction_coe
    {R : Type u} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F : ClosedSubgroup R) (s : R)
    (hF : conjugateClosedSubgroup F s = F)
    (a : ambientFixedAddSubgroup B F) :
    ((conjugateStableAction B F s hF a : ambientFixedAddSubgroup B F) :
        B.V) =
      B.ρ s⁻¹ a.1 := by
  exact transport_fixed_coe B _ F hF _

/-- **The relative norm is equivariant for a conjugation stabilizing both fields**
in the tower ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean:109`]
[Yamaguchi2026]). -/
theorem relativeNorm_conjugateStableAction
    {R : Type u} [Group R] [TopologicalSpace R] [ContinuousMul R]
    (B : Rep ℤ R) (F E : ClosedSubgroup R)
    (hEF : E.toSubgroup ≤ F.toSubgroup) (s : R)
    [Finite (F.toSubgroup ⧸ E.toSubgroup.subgroupOf F.toSubgroup)]
    (hF : conjugateClosedSubgroup F s = F)
    (hE : conjugateClosedSubgroup E s = E)
    (a : ambientFixedAddSubgroup B E) :
    relativeNorm B F E hEF (conjugateStableAction B E s hE a) =
      conjugateStableAction B F s hF (relativeNorm B F E hEF a) := by
  let hConj := conjugateClosedSubgroup_mono hEF s
  letI : Finite ((conjugateClosedSubgroup F s).toSubgroup ⧸
      (conjugateClosedSubgroup E s).toSubgroup.subgroupOf
        (conjugateClosedSubgroup F s).toSubgroup) :=
    finite_conjugateExtension F E s
  have hs := congrArg Subtype.val
    (relativeNorm_conjugate_apply B F E hEF s a)
  apply Subtype.ext
  calc
    ((relativeNorm B F E hEF (conjugateStableAction B E s hE a) :
        ambientFixedAddSubgroup B F) : B.V) =
        ((relativeNorm B (conjugateClosedSubgroup F s)
          (conjugateClosedSubgroup E s) hConj
          (conjugateFixedElement B E s a) :
            ambientFixedAddSubgroup B (conjugateClosedSubgroup F s)) :
          B.V) := by
      exact relativeNorm_transport_coe B
        (conjugateClosedSubgroup F s) (conjugateClosedSubgroup E s) F E
        hF hE hConj hEF (conjugateFixedElement B E s a)
    _ = ((conjugateFixedElement B F s (relativeNorm B F E hEF a) :
          ambientFixedAddSubgroup B (conjugateClosedSubgroup F s)) :
        B.V) := hs
    _ = ((conjugateStableAction B F s hF (relativeNorm B F E hEF a) :
          ambientFixedAddSubgroup B F) : B.V) :=
      (transport_fixed_coe B _ F hF _).symm

/-- **The calculation in the first half of the universal norm-descent lemma**:
the hypothesis `hstar` is equation `(*)` — the class of `u` in
coinvariants is fixed by `φ`; the elementwise content of `Ĥ⁰ = 0`
(`hnormSurj`) produces the barred lifts, and that of `Ĥ⁻¹ = 0`
(`hnormKer`) the correction term `y` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean:149`]
[Yamaguchi2026]). -/
theorem universalNormDescent_cyclic_lift_and_correction
    {R : Type u} [Group R] (H : Subgroup R) [H.Normal] [Fintype H]
    (B : Rep ℤ R) (g : H)
    (hnormSurj : ∀ x : B.V, B.ρ g.1 x = x →
      ∃ z : B.V, (∑ q : H, B.ρ q.1 z) = x)
    (hnormKer : ∀ x : B.V, (∑ q : H, B.ρ q.1 x) = 0 →
      ∃ z : B.V, B.ρ g.1 z - z = x)
    {ι : Type v} (s : Finset ι) (φ : R) (τ : ι → R)
    (u : B.V) (uᵢ : ι → B.V)
    (huFixed : ∀ q : H, B.ρ q.1 u = u)
    (huᵢFixed : ∀ (i : ι) (q : H), B.ρ q.1 (uᵢ i) = uᵢ i)
    (hstar : B.ρ φ u - u =
      ∑ i ∈ s, (B.ρ (τ i) (uᵢ i) - uᵢ i)) :
    ∃ (uBar : B.V) (uBarᵢ : ι → B.V) (y : B.V),
      (∑ q : H, B.ρ q.1 uBar) = u ∧
      (∀ i, (∑ q : H, B.ρ q.1 (uBarᵢ i)) = uᵢ i) ∧
      B.ρ g.1 y - y =
        B.ρ φ uBar - uBar -
          ∑ i ∈ s, (B.ρ (τ i) (uBarᵢ i) - uBarᵢ i) := by
  let U : Rep ℤ H := Rep.res H.subtype B
  have huLift : ∃ z : B.V, U.norm.hom z = u := by
    obtain ⟨z, hz⟩ := hnormSurj u (huFixed g)
    exact ⟨z, by simpa [U, Rep.norm, Representation.norm] using hz⟩
  obtain ⟨uBar, huBar⟩ := huLift
  have huᵢLift (i : ι) : ∃ z : B.V, U.norm.hom z = uᵢ i := by
    obtain ⟨z, hz⟩ := hnormSurj (uᵢ i) (huᵢFixed i g)
    exact ⟨z, by simpa [U, Rep.norm, Representation.norm] using hz⟩
  choose uBarᵢ huBarᵢ using huᵢLift
  let delta : B.V :=
    B.ρ φ uBar - uBar -
      ∑ i ∈ s, (B.ρ (τ i) (uBarᵢ i) - uBarᵢ i)
  have hdeltaNorm : U.norm.hom delta = 0 := by
    calc
      U.norm.hom delta =
          U.norm.hom (B.ρ φ uBar) - U.norm.hom uBar -
            ∑ i ∈ s,
              (U.norm.hom (B.ρ (τ i) (uBarᵢ i)) -
                U.norm.hom (uBarᵢ i)) := by
        dsimp [delta]
        rw [map_sub, map_sub, map_sum]
        simp_rw [map_sub]
      _ = B.ρ φ u - u -
          ∑ i ∈ s, (B.ρ (τ i) (uᵢ i) - uᵢ i) := by
        rw [restricted_rep_norm_action H B φ uBar, huBar]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [restricted_rep_norm_action H B (τ i) (uBarᵢ i), huBarᵢ i]
      _ = 0 := by rw [hstar, sub_self]
  obtain ⟨y, hy⟩ := hnormKer delta
    (by simpa [U, Rep.norm, Representation.norm] using hdeltaNorm)
  refine ⟨uBar, uBarᵢ, y, ?_, ?_, ?_⟩
  · simpa [U, Rep.norm, Representation.norm] using huBar
  · intro i
    simpa [U, Rep.norm, Representation.norm] using huBarᵢ i
  · simpa [delta] using hy

/-- The norm of a finite cyclic representation enumerated by the first
`n` powers of a specified generator ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean:212`]
[Yamaguchi2026]). -/
theorem rep_norm_eq_generatorPowerSum
    {Q : Type u} [Group Q] [Fintype Q]
    (B : Rep ℤ Q) (g : Q) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (n : ℕ) (hcard : Fintype.card Q = n) (x : B.V) :
    B.norm.hom x = ∑ i : Fin n, B.ρ (g ^ i.1) x := by
  classical
  have horder : orderOf g = n := by
    calc
      orderOf g = Nat.card Q :=
        orderOf_eq_card_of_forall_mem_zpowers hg
      _ = Fintype.card Q := Nat.card_eq_fintype_card
      _ = n := hcard
  let e : Fin n ≃ Q := Equiv.ofBijective (fun i => g ^ i.1) (by
    constructor
    · intro i j hij
      apply Fin.ext
      have hmod : i.1 ≡ j.1 [MOD orderOf g] :=
        (pow_eq_pow_iff_modEq).mp hij
      rw [horder] at hmod
      exact hmod.eq_of_lt_of_lt i.2 j.2
    · intro q
      have himage :
          Finset.image (fun i => g ^ i) (Finset.range n) =
            Finset.univ := by
        rw [← horder]
        exact IsCyclic.image_range_orderOf hg
      have hq : q ∈ Finset.image (fun i => g ^ i) (Finset.range n) := by
        rw [himage]
        simp
      obtain ⟨i, hi, hiq⟩ := Finset.mem_image.mp hq
      exact ⟨⟨i, Finset.mem_range.mp hi⟩, hiq⟩)
  simpa [Rep.norm, Representation.norm, e] using
    (e.sum_comp (fun q : Q => B.ρ q x)).symm

/-- Powers in a representation are the iterates of the corresponding
action map ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean:247`]
[Yamaguchi2026]). -/
theorem rep_action_pow_eq_iterate {R : Type u} [Group R]
    (B : Rep ℤ R) (g : R) (n : ℕ) (x : B.V) :
    B.ρ (g ^ n) x = ((B.ρ g)^[n]) x := by
  letI : Module ℤ B.V := B.hV2
  rw [map_pow, Module.End.coe_pow]

/-- **The norm as the iterate sum of any pointwise-equal endomorphism**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean:255`]
[Yamaguchi2026]). -/
theorem rep_norm_eq_generatorIterateSum
    {Q : Type u} [Group Q] [Fintype Q]
    (B : Rep ℤ Q) (g : Q) (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (n : ℕ) (hcard : Fintype.card Q = n)
    (f : B.V → B.V) (hf : ∀ z, B.ρ g z = f z) (x : B.V) :
    B.norm.hom x = ∑ i : Fin n, (f^[i.1]) x := by
  rw [rep_norm_eq_generatorPowerSum B g hg n hcard x]
  apply Finset.sum_congr rfl
  intro i _
  rw [rep_action_pow_eq_iterate]
  exact congrFun (congrArg (fun h : B.V → B.V => h^[i.1]) (funext hf)) x

/-- Every nonnegative power fixes an element fixed by the original group
element ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/UniversalNormDescent.lean:269`]
[Yamaguchi2026]). -/
theorem rep_action_pow_fixed {R : Type u} [Group R]
    (B : Rep ℤ R) (g : R) (x : B.V) (hx : B.ρ g x = x) (n : ℕ) :
    B.ρ (g ^ n) x = x := by
  rw [rep_action_pow_eq_iterate]
  exact Function.IsFixedPt.iterate hx n

end

end Atlas.Knowledge
