import Mathlib
import Atlas.Knowledge.QuotientTowerEquiv

/-!
# cardinal relative index

The relative index of a subgroup inclusion kept as an honest cardinal — the
cardinality of the actual coset type, never encoding an infinite index as zero —
together with the two laws the reciprocity engine's degree bookkeeping rests on
(#104): relative indices multiply in every tower, and along a homomorphism an
index splits into the index of the images times the relative index inside the
kernel. Mathlib has the natural-valued tower law and mapped indices, but no
cardinal-valued index and no kernel-intersection splitting at either value type;
the splitting's cardinal form is what lets the engine derive finiteness of its
residue and ramification quotients from finiteness of a degree — an argument the
zero-convention form cannot make, since `0 = 0 * 0`.

## Main definitions

* `intersectionIndexCardinal` / `relativeIndexCardinal` — the coset-type
  cardinality, for arbitrary subgroups and for an inclusion.
* `kernelCosetEquivSaturation` — the kernel cosets are the cosets of the
  kernel-saturated part; no normality of the lower subgroup is needed.

## Main statements

* `relativeIndexCardinal_mul` — indices multiply in a tower; proved.
* `relativeIndexCardinal_eq_map_mul_inf_ker` — the cardinal image–kernel
  splitting; proved.
* `relIndex_eq_map_relIndex_mul_inf_ker_relIndex` — the natural-valued
  splitting, valid under Mathlib's infinite-index-is-zero convention; proved.
* `relativeIndexCardinal_eq_index_of_finite` — the specialization to
  `Subgroup.relIndex` at a finite boundary; proved.

## Implementation notes

The tower law is `Atlas.Knowledge.quotientTowerEquiv` read through
`Cardinal.mk_congr`; the splitting is assembled from two coset-type
equivalences — the kernel cosets against the saturated part, and the image
cosets against the same saturated part through the comap reading — so every
identity descends from an equivalence of the actual types and no finiteness
enters. The universe lifts in the cardinal splitting are forced by the image
living over the codomain's universe. Chosen representatives occur only inside
the equivalences, never in the index laws.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

universe u v

variable {G : Type u} {D : Type v} [Group G] [Group D]

/- The inclusion of the kernel part into the saturated part. -/
private def kernelToSaturation (d : G →* D) (L K : Subgroup G) :
    ↑(K ⊓ d.ker) →* ↑(K ⊓ (L ⊔ d.ker)) :=
  Subgroup.inclusion (inf_le_inf le_rfl le_sup_right)

private theorem kernelToSaturation_rel_iff (d : G →* D) (L K : Subgroup G)
    (x y : ↑(K ⊓ d.ker)) :
    QuotientGroup.leftRel ((L ⊓ d.ker).subgroupOf (K ⊓ d.ker)) x y ↔
      QuotientGroup.leftRel (L.subgroupOf (K ⊓ (L ⊔ d.ker)))
        (kernelToSaturation d L K x) (kernelToSaturation d L K y) := by
  simp only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · exact fun h ↦ h.1
  · intro h
    exact ⟨h, d.ker.mul_mem (d.ker.inv_mem x.property.2) y.property.2⟩

private noncomputable def kernelCosetToSaturationCoset (d : G →* D) (L K : Subgroup G) :
    (↑(K ⊓ d.ker) ⧸ (L ⊓ d.ker).subgroupOf (K ⊓ d.ker)) →
      (↑(K ⊓ (L ⊔ d.ker)) ⧸ L.subgroupOf (K ⊓ (L ⊔ d.ker))) :=
  Quotient.map' (kernelToSaturation d L K) fun x y h ↦
    (kernelToSaturation_rel_iff d L K x y).mp h

private theorem kernelCosetToSaturationCoset_injective (d : G →* D) (L K : Subgroup G) :
    Function.Injective (kernelCosetToSaturationCoset d L K) := by
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro x y h
  apply Quotient.eq''.mpr
  apply (kernelToSaturation_rel_iff d L K x y).mpr
  apply Quotient.eq''.mp
  simpa only [kernelCosetToSaturationCoset, Quotient.map'_mk''] using h

private theorem kernelCosetToSaturationCoset_surjective (d : G →* D) {L K : Subgroup G}
    (hLK : L ≤ K) : Function.Surjective (kernelCosetToSaturationCoset d L K) := by
  intro q
  refine Quotient.inductionOn q ?_
  intro z
  have hzSup : (z : G) ∈ d.ker ⊔ L := by
    rw [sup_comm]
    exact z.property.2
  obtain ⟨n, hnKer, l, hlL, hnl⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := d.ker) (t := L)).mp hzSup
  have hnK : n ∈ K := by
    rw [show n = (z : G) * l⁻¹ by rw [← hnl]; simp]
    exact K.mul_mem z.property.1 (K.inv_mem (hLK hlL))
  let n' : ↑(K ⊓ d.ker) := ⟨n, hnK, hnKer⟩
  refine ⟨Quotient.mk'' n', ?_⟩
  simp only [kernelCosetToSaturationCoset, Quotient.map'_mk'']
  apply Quotient.eq''.mpr
  rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
  change n⁻¹ * (z : G) ∈ L
  rw [← hnl]
  simpa using hlL

/-- **The kernel cosets are the cosets of the kernel-saturated part**: for `L ≤ K`,
the coset type of `L ⊓ ker d` in `K ⊓ ker d` is the coset type of `L` in
`K ⊓ (L ⊔ ker d)` — the set-level second-isomorphism argument, with no normality of `L`
(Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Indices.lean:76`). -/
noncomputable def kernelCosetEquivSaturation (d : G →* D) {L K : Subgroup G}
    (hLK : L ≤ K) :
    (↑(K ⊓ d.ker) ⧸ (L ⊓ d.ker).subgroupOf (K ⊓ d.ker)) ≃
      (↑(K ⊓ (L ⊔ d.ker)) ⧸ L.subgroupOf (K ⊓ (L ⊔ d.ker))) :=
  Equiv.ofBijective (kernelCosetToSaturationCoset d L K)
    ⟨kernelCosetToSaturationCoset_injective d L K,
      kernelCosetToSaturationCoset_surjective d hLK⟩

/-- The index of `L` in the kernel-saturated part of `K` is the relative index of
the kernel intersections. -/
theorem relIndex_saturation_eq_inf_ker_relIndex (d : G →* D)
    {L K : Subgroup G} (hLK : L ≤ K) :
    L.relIndex (K ⊓ (L ⊔ d.ker)) =
      (L ⊓ d.ker).relIndex (K ⊓ d.ker) := by
  unfold Subgroup.relIndex
  exact Nat.card_congr (kernelCosetEquivSaturation d hLK).symm

/-- The mapped relative index is the index of the kernel-saturated part. -/
theorem map_relIndex_eq_saturation_relIndex (d : G →* D)
    (L K : Subgroup G) :
    (L.map d).relIndex (K.map d) =
      (K ⊓ (L ⊔ d.ker)).relIndex K := by
  rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq, ← Subgroup.inf_relIndex_right,
    inf_comm]

/-- **The natural-valued image–kernel splitting**: along a homomorphism, a relative
index is the relative index of the images times the relative index inside the
kernel — valid with no finiteness assumption, under Mathlib's convention that an
infinite relative index is zero (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Indices.lean:106`). -/
theorem relIndex_eq_map_relIndex_mul_inf_ker_relIndex (d : G →* D) {L K : Subgroup G}
    (hLK : L ≤ K) :
    L.relIndex K =
      (L.map d).relIndex (K.map d) * (L ⊓ d.ker).relIndex (K ⊓ d.ker) := by
  rw [map_relIndex_eq_saturation_relIndex,
    ← relIndex_saturation_eq_inf_ker_relIndex d hLK, mul_comm]
  exact (Subgroup.relIndex_mul_relIndex L (K ⊓ (L ⊔ d.ker)) K
    (fun x hx ↦ ⟨hLK hx, (show L ≤ L ⊔ d.ker from le_sup_left) hx⟩) inf_le_left).symm

/-- **The intersection index as a cardinal**: the cardinality of the coset type,
for arbitrary subgroups; for the index of an inclusion, `relativeIndexCardinal`
records the containment in its domain (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Indices.lean:128`). -/
noncomputable def intersectionIndexCardinal (L K : Subgroup G) : Cardinal :=
  Cardinal.mk (K ⧸ L.subgroupOf K)

/-- **The cardinal relative index of an inclusion**: the coset-type cardinality,
with the inclusion recorded in the domain — an infinite index stays an infinite cardinal
(Yamaguchi 2026, `AbstractClassFieldTheory/Degree/Indices.lean:132`). -/
noncomputable def relativeIndexCardinal {L K : Subgroup G} (_ : L ≤ K) : Cardinal :=
  intersectionIndexCardinal L K

/-- At a finite boundary the cardinal relative index is Mathlib's
`Subgroup.relIndex`. -/
theorem relativeIndexCardinal_eq_index_of_finite {L K : Subgroup G} (hLK : L ≤ K)
    [Finite (K ⧸ L.subgroupOf K)] :
    relativeIndexCardinal hLK = (L.relIndex K : Cardinal) := by
  rw [relativeIndexCardinal, intersectionIndexCardinal, Subgroup.relIndex,
    Subgroup.index]
  exact Nat.cast_card.symm

/-- The relative index of a subgroup in itself is one. -/
@[simp] theorem relativeIndexCardinal_self (K : Subgroup G) :
    relativeIndexCardinal (le_refl K) = 1 := by
  let α := K ⧸ K.subgroupOf K
  letI : Subsingleton α := by
    constructor
    intro q r
    refine Quotient.inductionOn₂ q r ?_
    intro x y
    apply Quotient.eq''.mpr
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    exact (x⁻¹ * y).2
  letI : Nonempty α := ⟨QuotientGroup.mk 1⟩
  change Cardinal.mk α = 1
  exact Cardinal.mk_eq_one α

/-- **Relative cardinal indices multiply in every subgroup tower** —
`Atlas.Knowledge.quotientTowerEquiv` read through `Cardinal.mk_congr`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Indices.lean:160`). -/
theorem relativeIndexCardinal_mul {M L K : Subgroup G}
    (hML : M ≤ L) (hLK : L ≤ K) :
    relativeIndexCardinal hML * relativeIndexCardinal hLK =
      relativeIndexCardinal (hML.trans hLK) := by
  rw [mul_comm, relativeIndexCardinal, relativeIndexCardinal,
    relativeIndexCardinal, intersectionIndexCardinal, intersectionIndexCardinal,
    intersectionIndexCardinal, Cardinal.mul_def]
  exact Cardinal.mk_congr (quotientTowerEquiv hML hLK).symm

/- The restriction of a homomorphism to a subgroup, onto its image. -/
private def subgroupMapRestriction (d : G →* D) (K : Subgroup G) :
    K →* K.map d where
  toFun x := ⟨d x.1, ⟨x.1, x.2, rfl⟩⟩
  map_one' := Subtype.ext (map_one d)
  map_mul' x y := Subtype.ext (map_mul d x.1 y.1)

private theorem subgroupMapRestriction_surjective (d : G →* D) (K : Subgroup G) :
    Function.Surjective (subgroupMapRestriction d K) := by
  rintro ⟨_, x, hx, rfl⟩
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem subgroupMapRestriction_rel_iff (d : G →* D)
    (H : Subgroup D) (K : Subgroup G) (x y : K) :
    QuotientGroup.leftRel ((H.comap d).subgroupOf K) x y ↔
      QuotientGroup.leftRel (H.subgroupOf (K.map d))
        (subgroupMapRestriction d K x) (subgroupMapRestriction d K y) := by
  simp only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf,
    Subgroup.mem_comap]
  change d (x.1⁻¹ * y.1) ∈ H ↔ (d x.1)⁻¹ * d y.1 ∈ H
  rw [map_mul, map_inv]

private noncomputable def relativeCosetComapMap (d : G →* D)
    (H : Subgroup D) (K : Subgroup G) :
    (K ⧸ (H.comap d).subgroupOf K) →
      (K.map d ⧸ H.subgroupOf (K.map d)) :=
  Quotient.map' (subgroupMapRestriction d K) fun x y h ↦
    (subgroupMapRestriction_rel_iff d H K x y).mp h

private theorem relativeCosetComapMap_injective (d : G →* D)
    (H : Subgroup D) (K : Subgroup G) :
    Function.Injective (relativeCosetComapMap d H K) := by
  intro q₁ q₂
  refine Quotient.inductionOn₂ q₁ q₂ ?_
  intro x y h
  apply Quotient.eq''.mpr
  apply (subgroupMapRestriction_rel_iff d H K x y).mpr
  apply Quotient.eq''.mp
  simpa only [relativeCosetComapMap, Quotient.map'_mk''] using h

private theorem relativeCosetComapMap_surjective (d : G →* D)
    (H : Subgroup D) (K : Subgroup G) :
    Function.Surjective (relativeCosetComapMap d H K) := by
  intro q
  refine Quotient.inductionOn' q ?_
  intro z
  obtain ⟨x, rfl⟩ := subgroupMapRestriction_surjective d K z
  exact ⟨Quotient.mk'' x, by
    simp only [relativeCosetComapMap, Quotient.map'_mk'']⟩

private noncomputable def relativeCosetComapEquiv (d : G →* D)
    (H : Subgroup D) (K : Subgroup G) :
    (K ⧸ (H.comap d).subgroupOf K) ≃
      (K.map d ⧸ H.subgroupOf (K.map d)) :=
  Equiv.ofBijective (relativeCosetComapMap d H K)
    ⟨relativeCosetComapMap_injective d H K,
      relativeCosetComapMap_surjective d H K⟩

private noncomputable def imageCosetEquivSaturation (d : G →* D)
    (L K : Subgroup G) :
    (K ⧸ (K ⊓ (L ⊔ d.ker)).subgroupOf K) ≃
      (K.map d ⧸ (L.map d).subgroupOf (K.map d)) := by
  have hsub :
      ((L.map d).comap d).subgroupOf K =
        (K ⊓ (L ⊔ d.ker)).subgroupOf K := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    rw [Subgroup.comap_map_eq]
    exact (and_iff_right x.2).symm
  exact (Subgroup.quotientEquivOfEq hsub.symm).trans
    (relativeCosetComapEquiv d (L.map d) K)

/-- The image contribution as a cardinal: the intersection index of the
kernel-saturated part. -/
theorem intersectionIndexCardinal_image_eq_saturation (d : G →* D)
    (L K : Subgroup G) :
    Cardinal.lift.{u} (intersectionIndexCardinal (L.map d) (K.map d)) =
      Cardinal.lift.{v}
        (intersectionIndexCardinal (K ⊓ (L ⊔ d.ker)) K) :=
  (imageCosetEquivSaturation d L K).lift_cardinal_eq.symm

/-- The kernel contribution as a cardinal: intersecting both subgroups with the
kernel gives the saturated inner index. -/
theorem relativeIndexCardinal_kernel_eq_saturation (d : G →* D)
    {L K : Subgroup G} (hLK : L ≤ K) :
    relativeIndexCardinal
      (show L ⊓ d.ker ≤ K ⊓ d.ker from inf_le_inf hLK le_rfl) =
      relativeIndexCardinal
        (show L ≤ K ⊓ (L ⊔ d.ker) from fun _ hx ↦
          ⟨hLK hx, (show L ≤ L ⊔ d.ker from le_sup_left) hx⟩) :=
  Cardinal.mk_congr (kernelCosetEquivSaturation d hLK)

/-- **The cardinal image–kernel splitting**: along a homomorphism, the cardinal
relative index of an inclusion is the index of the images times the relative index
inside the kernel — every factor an actual coset-type cardinality, so the identity
holds with no finiteness assumption (Yamaguchi 2026,
`AbstractClassFieldTheory/Degree/Indices.lean:263`). -/
theorem relativeIndexCardinal_eq_map_mul_inf_ker (d : G →* D)
    {L K : Subgroup G} (hLK : L ≤ K) :
    Cardinal.lift.{v} (relativeIndexCardinal hLK) =
      Cardinal.lift.{u}
          (relativeIndexCardinal (Subgroup.map_mono (f := d) hLK)) *
        Cardinal.lift.{v}
          (relativeIndexCardinal
            (show L ⊓ d.ker ≤ K ⊓ d.ker from inf_le_inf hLK le_rfl)) := by
  have hLS : L ≤ K ⊓ (L ⊔ d.ker) := fun _ hx ↦
    ⟨hLK hx, (show L ≤ L ⊔ d.ker from le_sup_left) hx⟩
  have hSK : K ⊓ (L ⊔ d.ker) ≤ K := inf_le_left
  calc
    Cardinal.lift.{v} (relativeIndexCardinal hLK) =
        Cardinal.lift.{v}
            (relativeIndexCardinal hLS) *
          Cardinal.lift.{v}
            (relativeIndexCardinal hSK) := by
      rw [← Cardinal.lift_mul, relativeIndexCardinal_mul hLS hSK]
    _ = Cardinal.lift.{v}
            (relativeIndexCardinal
              (show L ⊓ d.ker ≤ K ⊓ d.ker from inf_le_inf hLK le_rfl)) *
          Cardinal.lift.{u}
            (relativeIndexCardinal (Subgroup.map_mono (f := d) hLK)) := by
      have hkernel :
          intersectionIndexCardinal (L ⊓ d.ker) (K ⊓ d.ker) =
            intersectionIndexCardinal L (K ⊓ (L ⊔ d.ker)) := by
        simpa only [relativeIndexCardinal] using
          relativeIndexCardinal_kernel_eq_saturation d hLK
      change
        Cardinal.lift.{v}
            (intersectionIndexCardinal L (K ⊓ (L ⊔ d.ker))) *
          Cardinal.lift.{v}
            (intersectionIndexCardinal (K ⊓ (L ⊔ d.ker)) K) =
          Cardinal.lift.{v}
            (intersectionIndexCardinal (L ⊓ d.ker) (K ⊓ d.ker)) *
          Cardinal.lift.{u}
            (intersectionIndexCardinal (L.map d) (K.map d))
      rw [hkernel, intersectionIndexCardinal_image_eq_saturation d L K]
    _ = Cardinal.lift.{u}
            (relativeIndexCardinal (Subgroup.map_mono (f := d) hLK)) *
          Cardinal.lift.{v}
            (relativeIndexCardinal
              (show L ⊓ d.ker ≤ K ⊓ d.ker from inf_le_inf hLK le_rfl)) :=
      mul_comm _ _

end Atlas.Knowledge
