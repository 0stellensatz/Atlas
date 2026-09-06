import Mathlib
import Atlas.Knowledge.FiniteTower
import Atlas.Knowledge.QuotientTowerEquiv
import Atlas.Knowledge.RelativeNorm

/-!
# laws for relative norms

The structural laws of the engine's coset-sum norm: conjugation carries fixed
elements of `A_K` to fixed elements of `A_{K^σ}` and intertwines the absolute
norms; for a Galois abstract extension the norm is invariant under the
`G_K`-action on `A_L`; and along a finite tower the norm is transitive, by
reindexing the double coset sum through the tower's quotient product. These
are the identities the reciprocity construction's prime-element and descent
arguments consume (#104).

## Main definitions

* `conjugateClosedSubgroup` / `conjugateFixedElement` — the conjugate field
  and the conjugate of a fixed element.
* `absoluteConjugateCosetEquiv` — conjugation on the absolute coset space.
* `normalExtensionAction` — the `G_K`-action on `A_L` for Galois `L | K`.
* `FiniteTower.totalExtension` — the composite of a finite tower, finite.

## Main statements

* `relativeNorm_absoluteConjugate_apply` — the absolute norm commutes with
  conjugation; proved.
* `relativeNorm_normalExtensionAction` — the norm is action-invariant;
  proved.
* `relativeTowerQuotientFinite` — finiteness composes in a tower; proved.
* `FiniteTower.norm_trans` — norms compose along a finite tower; proved.
* `FiniteTower.totalQuotientFinite` — the composite's finiteness, as an
  instance; proved.

## Implementation notes

The construction writes the action on fields and elements on the right, so
the left action of the representation realizes `a^σ` as `ρ(σ⁻¹) a` and the
conjugate subgroup is `σ⁻¹ G_K σ`. The engine's relative subgroup is
`Subgroup.subgroupOf` as across the layer — the source's separate membership
lemma at the base is the definitional unfolding here and is not ported — and
the tower reindexing is `Atlas.Knowledge.quotientTowerEquiv`. The source
works around a stale universe restriction on `Rep` with a dedicated
acting-group type; the restriction is gone and the file is
universe-polymorphic like the rest of the engine layer.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

open scoped Pointwise

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The subgroup of the conjugate abstract field `K^σ`** — the construction
uses a right exponent, hence `G_{K^σ} = σ⁻¹ G_K σ` (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:26`). -/
def conjugateClosedSubgroup [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G) : ClosedSubgroup G where
  toSubgroup := ConjAct.toConjAct σ⁻¹ • K.toSubgroup
  isClosed' := by
    convert IsClosed.preimage
      (IsTopologicalGroup.continuous_conj (G := G) σ) K.isClosed' using 1
    ext x
    change x ∈ (ConjAct.toConjAct σ⁻¹ • K.toSubgroup : Subgroup G) ↔
      σ * x * σ⁻¹ ∈ K.toSubgroup
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp only [ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]

/-- Membership in the conjugate subgroup is conjugate membership
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:43`). -/
@[simp]
theorem conjugateClosedSubgroup_mem [ContinuousMul G]
    (K : ClosedSubgroup G) (σ x : G) :
    x ∈ conjugateClosedSubgroup K σ ↔ σ * x * σ⁻¹ ∈ K := by
  change x ∈ (ConjAct.toConjAct σ⁻¹ • K.toSubgroup : Subgroup G) ↔
    σ * x * σ⁻¹ ∈ K.toSubgroup
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [ConjAct.toConjAct_inv, inv_inv, ConjAct.toConjAct_smul]

/-- **The right-conjugate `a^σ`**, through the left action (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:53`). -/
def conjugateFixedElement [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K) :
    ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ) := by
  refine ⟨A.ρ σ⁻¹ a.1, ?_⟩
  intro x
  let k : K.toSubgroup := ⟨σ * x.1 * σ⁻¹,
    (conjugateClosedSubgroup_mem K σ x.1).mp x.2⟩
  calc
    A.ρ x.1 (A.ρ σ⁻¹ a.1) = A.ρ (x.1 * σ⁻¹) a.1 := by
      rw [map_mul]
      rfl
    _ = A.ρ (σ⁻¹ * k.1) a.1 := by simp [k, mul_assoc]
    _ = A.ρ σ⁻¹ (A.ρ k.1 a.1) := by
      rw [map_mul]
      rfl
    _ = A.ρ σ⁻¹ a.1 := by rw [a.2 k]

/-- The conjugate reads as the inverse action on the coefficient
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:76`). -/
@[simp]
theorem conjugateFixedElement_coe [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K) :
    ((conjugateFixedElement A K σ a :
      ambientFixedAddSubgroup A (conjugateClosedSubgroup K σ)) : A.V) =
      A.ρ σ⁻¹ a.1 :=
  rfl

/- Conjugation as a self-equivalence of the base subgroup (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:84`). -/
private def absoluteConjugationEquiv (σ : G) :
    (baseField G).toSubgroup ≃
      (baseField G).toSubgroup where
  toFun x := ⟨σ * x.1 * σ⁻¹, trivial⟩
  invFun x := ⟨σ⁻¹ * x.1 * σ, trivial⟩
  left_inv x := by
    apply Subtype.ext
    simp [mul_assoc]
  right_inv x := by
    apply Subtype.ext
    simp [mul_assoc]

/-- **Conjugation identifies the absolute coset spaces of `K^σ` and `K`**
(Yamaguchi 2026, `AbstractClassFieldTheory/Degree/NormLaws.lean:105`). -/
def absoluteConjugateCosetEquiv [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G) :
    ((baseField G).toSubgroup ⧸
        (conjugateClosedSubgroup K σ).toSubgroup.subgroupOf
          (baseField G).toSubgroup) ≃
      ((baseField G).toSubgroup ⧸
        K.toSubgroup.subgroupOf (baseField G).toSubgroup) :=
  Quotient.congr (absoluteConjugationEquiv σ) (by
    intro x y
    rw [QuotientGroup.leftRel_apply, QuotientGroup.leftRel_apply,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    change ((x⁻¹ * y : (baseField G).toSubgroup) : G) ∈
        conjugateClosedSubgroup K σ ↔
      (((absoluteConjugationEquiv σ x)⁻¹ *
        absoluteConjugationEquiv σ y : (baseField G).toSubgroup) : G) ∈ K
    rw [conjugateClosedSubgroup_mem]
    change σ * (x.1⁻¹ * y.1) * σ⁻¹ ∈ K.toSubgroup ↔
      (σ * x.1 * σ⁻¹)⁻¹ * (σ * y.1 * σ⁻¹) ∈ K.toSubgroup
    simp [mul_assoc])

/-- The conjugate coset equivalence acts on representatives — not a simp
lemma here: the base subgroup rewrites to `⊤` under the layer's simp set, so
the left-hand side is not normal (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:129`). -/
theorem absoluteConjugateCosetEquiv_mk [ContinuousMul G]
    (K : ClosedSubgroup G) (σ : G)
    (x : (baseField G).toSubgroup) :
    absoluteConjugateCosetEquiv K σ (QuotientGroup.mk x) =
      QuotientGroup.mk (absoluteConjugationEquiv σ x) :=
  rfl

/- The coset action of the conjugate is the conjugated coset action
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:137`). -/
private theorem relativeCosetAction_absoluteConjugate [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    (a : ambientFixedAddSubgroup A K)
    (q : (baseField G).toSubgroup ⧸
      (conjugateClosedSubgroup K σ).toSubgroup.subgroupOf
        (baseField G).toSubgroup) :
    relativeCosetAction A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) q =
      A.ρ σ⁻¹
        (relativeCosetAction A (baseField G) K
          (le_baseField K) a
          (absoluteConjugateCosetEquiv K σ q)) := by
  refine Quotient.inductionOn' q ?_
  intro x
  rw [relativeCosetAction_mk, absoluteConjugateCosetEquiv_mk,
    relativeCosetAction_mk, conjugateFixedElement_coe]
  calc
    A.ρ x.1 (A.ρ σ⁻¹ a.1) = A.ρ (x.1 * σ⁻¹) a.1 := by
      rw [map_mul]
      rfl
    _ = A.ρ (σ⁻¹ * (σ * x.1 * σ⁻¹)) a.1 := by simp [mul_assoc]
    _ = A.ρ σ⁻¹ (A.ρ (σ * x.1 * σ⁻¹) a.1) := by
      rw [map_mul]
      rfl

/-- **The absolute norm commutes with conjugation**: the norm of `a^σ` from
`K^σ` is the `σ`-conjugate of the norm of `a` from `K` (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:169`). -/
theorem relativeNorm_absoluteConjugate_apply [ContinuousMul G]
    (A : Rep ℤ G) (K : ClosedSubgroup G) (σ : G)
    [Finite
      ((baseField G).toSubgroup ⧸
        K.toSubgroup.subgroupOf (baseField G).toSubgroup)]
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite
        ((baseField G).toSubgroup ⧸
          (conjugateClosedSubgroup K σ).toSubgroup.subgroupOf
            (baseField G).toSubgroup) :=
      Finite.of_equiv
        ((baseField G).toSubgroup ⧸
          K.toSubgroup.subgroupOf (baseField G).toSubgroup)
        (absoluteConjugateCosetEquiv K σ).symm
    ((relativeNorm A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) :
      ambientFixedAddSubgroup A (baseField G)) : A.V) =
      A.ρ σ⁻¹
        ((relativeNorm A (baseField G) K
          (le_baseField K) a :
          ambientFixedAddSubgroup A (baseField G)) : A.V) := by
  letI : Finite
      ((baseField G).toSubgroup ⧸
        (conjugateClosedSubgroup K σ).toSubgroup.subgroupOf
          (baseField G).toSubgroup) :=
    Finite.of_equiv
      ((baseField G).toSubgroup ⧸
        K.toSubgroup.subgroupOf (baseField G).toSubgroup)
      (absoluteConjugateCosetEquiv K σ).symm
  letI := Fintype.ofFinite
    ((baseField G).toSubgroup ⧸
      K.toSubgroup.subgroupOf (baseField G).toSubgroup)
  letI := Fintype.ofFinite
    ((baseField G).toSubgroup ⧸
      (conjugateClosedSubgroup K σ).toSubgroup.subgroupOf
        (baseField G).toSubgroup)
  simp only [relativeNorm_apply_coe, relativeNormValue]
  calc
    ∑ q, relativeCosetAction A (baseField G)
        (conjugateClosedSubgroup K σ)
        (le_baseField (conjugateClosedSubgroup K σ))
        (conjugateFixedElement A K σ a) q =
      ∑ q, A.ρ σ⁻¹
        (relativeCosetAction A (baseField G) K
          (le_baseField K) a
          (absoluteConjugateCosetEquiv K σ q)) := by
            apply Finset.sum_congr rfl
            intro q _
            exact relativeCosetAction_absoluteConjugate A K σ a q
    _ = A.ρ σ⁻¹
        (∑ q, relativeCosetAction A (baseField G) K
          (le_baseField K) a
          (absoluteConjugateCosetEquiv K σ q)) := by
            rw [map_sum]
    _ = A.ρ σ⁻¹
        (∑ q, relativeCosetAction A (baseField G) K
          (le_baseField K) a q) := by
            rw [(absoluteConjugateCosetEquiv K σ).sum_comp]

/-- **The `G_K`-action on `A_L` for Galois `L | K`** — normality proves the
translate is still fixed by `G_L` (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:240`). -/
def normalExtensionAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    ambientFixedAddSubgroup A L := by
  refine ⟨A.ρ k.1 a.1, ?_⟩
  intro l
  let lK : K.toSubgroup := Subgroup.inclusion hLK l
  have hc : k⁻¹ * lK * k ∈ L.toSubgroup.subgroupOf K.toSubgroup :=
    by simpa using hnormal.conj_mem lK l.2 k⁻¹
  let l' : L.toSubgroup := ⟨(k⁻¹ * lK * k).1, hc⟩
  have hl'val : (l' : G) = (k⁻¹ * lK * k : K.toSubgroup) :=
    rfl
  calc
    A.ρ l.1 (A.ρ k.1 a.1) = A.ρ (l.1 * k.1) a.1 := by rw [map_mul]; rfl
    _ = A.ρ (k.1 * l'.1) a.1 := by rw [hl'val]; simp [lK, mul_assoc]
    _ = A.ρ k.1 (A.ρ l'.1 a.1) := by rw [map_mul]; rfl
    _ = A.ρ k.1 a.1 := by rw [a.2 l']

/-- The action reads on the coefficient (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:265`). -/
@[simp]
theorem normalExtensionAction_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    ((normalExtensionAction A K L hLK hnormal k a :
      ambientFixedAddSubgroup A L) : A.V) =
      A.ρ k.1 a.1 :=
  rfl

/-- **The relative norm is invariant under the `G_K`-action** on `A_L`
(Yamaguchi 2026, `AbstractClassFieldTheory/Degree/NormLaws.lean:276`). -/
theorem relativeNorm_normalExtensionAction
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    relativeNorm A K L hLK (normalExtensionAction A K L hLK hnormal k a) =
      relativeNorm A K L hLK a := by
  apply Subtype.ext
  letI := hnormal
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
  let e : (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) ≃
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
    Equiv.mulRight (QuotientGroup.mk k)
  have hterm : ∀ q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup,
      relativeCosetAction A K L hLK
          (normalExtensionAction A K L hLK hnormal k a) q =
        relativeCosetAction A K L hLK a (e q) := by
    intro q
    refine Quotient.inductionOn' q ?_
    intro x
    simp only [relativeCosetAction_mk, normalExtensionAction_coe]
    have he : e (QuotientGroup.mk x) = QuotientGroup.mk (x * k) := rfl
    rw [he, relativeCosetAction_mk]
    change A.ρ x.1 (A.ρ k.1 a.1) = A.ρ (x.1 * k.1) a.1
    rw [map_mul]
    rfl
  simp only [relativeNorm_apply_coe, relativeNormValue]
  simp_rw [hterm]
  exact e.sum_comp (relativeCosetAction A K L hLK a)

/-- **Finiteness composes in a tower of closed subgroups** (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:307`). -/
theorem relativeTowerQuotientFinite
    (K L M : ClosedSubgroup G)
    (hML : M.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    [Finite (L.toSubgroup ⧸ M.toSubgroup.subgroupOf L.toSubgroup)] :
    Finite
      (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
  Finite.of_equiv
    ((K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) ×
      (L.toSubgroup ⧸ M.toSubgroup.subgroupOf L.toSubgroup))
    (quotientTowerEquiv hML hLK).symm

namespace FiniteTower

variable (T : FiniteTower G)

/-- **The composite of a finite tower, finite** (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:326`). -/
def totalExtension : FiniteAbstractExtension G where
  toAbstractExtension := T.toTower.totalExtension
  finiteQuotient := relativeTowerQuotientFinite
    T.base T.middle T.top T.top_le_middle T.middle_le_base

/-- The top-to-base quotient of a finite tower is finite (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:332`). -/
instance totalQuotientFinite :
    Finite (T.base.toSubgroup ⧸
      T.top.toSubgroup.subgroupOf T.base.toSubgroup) :=
  T.totalExtension.finiteQuotient

end FiniteTower

/- The coset action along the tower product (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:340`). -/
private theorem relativeCosetAction_towerProductEquiv
    (A : Rep ℤ G) (K L M : ClosedSubgroup G)
    (hML : M.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A M)
    (q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (r : L.toSubgroup ⧸ M.toSubgroup.subgroupOf L.toSubgroup) :
    relativeCosetAction A K M (hML.trans hLK) a
        ((quotientTowerEquiv hML hLK).symm (q, r)) =
      A.ρ (Quotient.out q).1 (relativeCosetAction A L M hML a r) := by
  refine Quotient.inductionOn' r ?_
  intro x
  have he : (quotientTowerEquiv hML hLK).symm
      (q, QuotientGroup.mk x) =
      QuotientGroup.mk (Quotient.out q * Subgroup.inclusion hLK x) := rfl
  rw [he, relativeCosetAction_mk, relativeCosetAction_mk]
  change A.ρ ((Quotient.out q).1 * x.1) a.1 =
    A.ρ (Quotient.out q).1 (A.ρ x.1 a.1)
  rw [map_mul]
  rfl

/- Transitivity on elements, over bare subgroup data (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:361`). -/
private theorem finiteTowerNormTransApplyAux
    (A : Rep ℤ G) (K L M : ClosedSubgroup G)
    (hML : M.toSubgroup ≤ L.toSubgroup)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    [Finite (L.toSubgroup ⧸ M.toSubgroup.subgroupOf L.toSubgroup)] :
    ∀ a : ambientFixedAddSubgroup A M,
    letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
      relativeTowerQuotientFinite K L M hML hLK
    relativeNorm A K L hLK (relativeNorm A L M hML a) =
      relativeNorm A K M (hML.trans hLK) a := by
  intro a
  letI : Finite (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup) :=
    relativeTowerQuotientFinite K L M hML hLK
  apply Subtype.ext
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
  letI := Fintype.ofFinite
    (L.toSubgroup ⧸ M.toSubgroup.subgroupOf L.toSubgroup)
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ M.toSubgroup.subgroupOf K.toSubgroup)
  have houter : ∀ q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup,
      relativeCosetAction A K L hLK (relativeNorm A L M hML a) q =
        A.ρ (Quotient.out q).1 (relativeNormValue A L M hML a) := by
    intro q
    calc
      relativeCosetAction A K L hLK (relativeNorm A L M hML a) q =
          relativeCosetAction A K L hLK (relativeNorm A L M hML a)
            (QuotientGroup.mk (Quotient.out q)) := by
              exact congrArg
                (relativeCosetAction A K L hLK (relativeNorm A L M hML a))
                (Quotient.out_eq' q).symm
      _ = A.ρ (Quotient.out q).1
          ((relativeNorm A L M hML a :
            ambientFixedAddSubgroup A L) : A.V) :=
        relativeCosetAction_mk A K L hLK (relativeNorm A L M hML a)
          (Quotient.out q)
      _ = A.ρ (Quotient.out q).1 (relativeNormValue A L M hML a) := by
        rw [relativeNorm_apply_coe]
  simp only [relativeNorm_apply_coe, relativeNormValue]
  rw [Finset.sum_congr rfl (fun q _ ↦ houter q)]
  simp only [relativeNormValue]
  simp_rw [map_sum]
  rw [← Fintype.sum_prod_type (f := fun p :
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) ×
      (L.toSubgroup ⧸ M.toSubgroup.subgroupOf L.toSubgroup) ↦
        A.ρ (Quotient.out p.1).1
          (relativeCosetAction A L M hML a p.2))]
  calc
    ∑ p : (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) ×
        (L.toSubgroup ⧸ M.toSubgroup.subgroupOf L.toSubgroup),
        A.ρ (Quotient.out p.1).1 (relativeCosetAction A L M hML a p.2) =
      ∑ p, relativeCosetAction A K M (hML.trans hLK) a
        ((quotientTowerEquiv hML hLK).symm p) := by
          apply Fintype.sum_congr
          intro p
          exact (relativeCosetAction_towerProductEquiv
            A K L M hML hLK a p.1 p.2).symm
    _ = ∑ q, relativeCosetAction A K M (hML.trans hLK) a q :=
      (quotientTowerEquiv hML hLK).symm.sum_comp
        (relativeCosetAction A K M (hML.trans hLK) a)

namespace FiniteTower

variable (T : FiniteTower G)

/-- **Relative norms are transitive along a finite tower** — the containments
and finiteness witnesses all come from the tower (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:423`). -/
theorem norm_trans_apply (A : Rep ℤ G)
    (a : ambientFixedAddSubgroup A T.top) :
    relativeNorm A T.base T.middle T.middle_le_base
        (relativeNorm A T.middle T.top T.top_le_middle a) =
      relativeNorm A T.base T.top
        (T.top_le_middle.trans T.middle_le_base) a :=
  finiteTowerNormTransApplyAux A T.base T.middle T.top
    T.top_le_middle T.middle_le_base a

/-- **Norm transitivity, in homomorphism form** (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/NormLaws.lean:433`). -/
theorem norm_trans (A : Rep ℤ G) :
    (relativeNorm A T.base T.middle T.middle_le_base).comp
        (relativeNorm A T.middle T.top T.top_le_middle) =
      relativeNorm A T.base T.top
        (T.top_le_middle.trans T.middle_le_base) := by
  apply AddMonoidHom.ext
  intro a
  exact T.norm_trans_apply A a

end FiniteTower

end

end Atlas.Knowledge
