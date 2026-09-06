import Mathlib
import Atlas.Knowledge.ExtensionFixedRepresentation
import Atlas.Knowledge.RelativeNorm

/-!
# fixed carrier and norm of the extension representation

The descended quotient representation of an abstract extension, compared with
the engine's explicit fixed subgroups: its carrier is the fixed subgroup
`A_L`, its quotient action is the relative coset action, and its
representation-theoretic norm is the relative norm on the underlying fixed
coefficient. These identities are what let the cohomological engine's
statements about the descended representation read as statements about the
concrete coefficient module (#104).

## Main definitions

* `extensionFixedRepresentationEquiv` — the carrier is `A_L`.

## Main statements

* `extensionFixedRepresentation_action_coe` — the quotient action is the
  relative coset action; proved.
* `extensionFixedRepresentation_norm_coe` — the representation norm is the
  relative norm; proved.

## Implementation notes

The source works around a stale universe restriction on `Rep` with a
dedicated acting-group type; the restriction is gone and the file is
universe-polymorphic like the rest of the engine layer. The engine's relative
subgroup is spelled `Subgroup.subgroupOf`. The `Module ℤ` reading of the
descended carrier is pinned to the representation's own instance, as in the
source — the derived `AddCommGroup.toIntModule` is not definitionally the
same, and the norm sum must be read through the former.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The carrier of the descended representation is the fixed subgroup**
`A_L` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean:27`). -/
def extensionFixedRepresentationEquiv
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal) :
    (extensionFixedRepresentation A K L hLK hnormal).V ≃+
      ambientFixedAddSubgroup A L where
  toFun x := ⟨x.1, by
    intro l
    exact x.2 ⟨⟨l.1, hLK l.2⟩, l.2⟩⟩
  invFun a := ⟨a.1, by
    intro s
    let l : L.toSubgroup := ⟨s.1.1, s.2⟩
    change A.ρ s.1.1 a.1 = a.1
    exact a.2 l⟩
  left_inv x := by
    apply Subtype.ext
    rfl
  right_inv a := by
    apply Subtype.ext
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    rfl

/-- The carrier reading forgets to the ambient coefficient (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean:56`). -/
@[simp]
theorem extensionFixedRepresentationEquiv_apply_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) :
    ((extensionFixedRepresentationEquiv A K L hLK hnormal a :
        ambientFixedAddSubgroup A L) : A.V) = a.1 :=
  rfl

/-- The inverse reading forgets to the same coefficient (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean:69`). -/
@[simp]
theorem extensionFixedRepresentationEquiv_symm_apply_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (a : ambientFixedAddSubgroup A L) :
    ((extensionFixedRepresentationEquiv A K L hLK hnormal).symm a).1 = a.1 :=
  rfl

/-- **The quotient action on `A_L` is the relative coset action**
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean:79`). -/
theorem extensionFixedRepresentation_action_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (q : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) :
    ((extensionFixedRepresentation A K L hLK hnormal).ρ q a).1 =
      relativeCosetAction A K L hLK
        (extensionFixedRepresentationEquiv A K L hLK hnormal a) q := by
  letI := hnormal
  refine Quotient.inductionOn' q ?_
  intro k
  rw [relativeCosetAction_mk]
  rfl

/-- **The representation norm is the relative norm** on the underlying fixed
coefficient (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/FieldRepresentation.lean:96`). -/
theorem extensionFixedRepresentation_norm_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    [Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)]
    (a : (extensionFixedRepresentation A K L hLK hnormal).V) :
    letI := hnormal
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    ((extensionFixedRepresentation A K L hLK hnormal).norm.hom a).1 =
      ((relativeNorm A K L hLK
        (extensionFixedRepresentationEquiv A K L hLK hnormal a) :
          ambientFixedAddSubgroup A K) : A.V) := by
  letI := hnormal
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
  rw [relativeNorm_apply_coe]
  simp only [Rep.norm, Representation.norm, relativeNormValue]
  let M := extensionFixedRepresentation A K L hLK hnormal
  letI : Module ℤ M.V := M.hV2
  change ((∑ q, M.ρ q) a).1 =
    ∑ q, relativeCosetAction A K L hLK
      (extensionFixedRepresentationEquiv A K L hLK hnormal a) q
  rw [LinearMap.sum_apply]
  let coeToAmbient :
      (extensionFixedRepresentation A K L hLK hnormal).V →+ A.V :=
    { toFun := fun x => x.1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change coeToAmbient (∑ q, M.ρ q a) =
    ∑ q, relativeCosetAction A K L hLK
      (extensionFixedRepresentationEquiv A K L hLK hnormal a) q
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro q _
  exact extensionFixedRepresentation_action_coe A K L hLK hnormal q a

end

end Atlas.Knowledge
