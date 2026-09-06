import Mathlib
import Atlas.Knowledge.FiniteAbelianSubextension
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.IntermediateGaloisCorrespondence
import Atlas.Knowledge.NormTopology

/-!
# class field candidate

The source-producing half of the finite abelian classification
theorem's surjectivity (#104): an open subgroup `H ≤ A_K` in the norm
topology contains the norm subgroup `N_E` of an actual finite Galois
subextension `E`; modulo `N_E` it is a concrete subgroup `H / N_E` of
the finite norm quotient, which a finite reciprocity equivalence
`rE : A_K / N_E ≃ G(E/K)ᵃᵇ` transports to the abelianization, and
pulling back along `G(E/K) → G(E/K)ᵃᵇ` gives a subgroup of the finite
Galois quotient containing its commutator; the finite Galois
correspondence then cuts out a finite abelian intermediate extension
`L`, the candidate. The equivalence is an explicit argument, supplied
by a later specialization from finite reciprocity; no existence
statement, norm-kernel equality, or classification conclusion depending
on it is asserted here.

## Main definitions

* `FiniteGaloisSubextension.normQuotientSubgroup`,
  `FiniteGaloisSubextension.reciprocityAbelianizedSubgroup`,
  `FiniteGaloisSubextension.reciprocityPreimageSubgroup` — `H / N_E`,
  its transport to `G(E/K)ᵃᵇ`, and its pullback to `G(E/K)`.
* `FiniteGaloisSubextension.reciprocityAbelianizedClassHom` — the
  abelianized class map `A_K → G(E/K)ᵃᵇ` through `rE`.
* `abelianizationPreimageSubgroup` — the pullback of a subgroup of an
  abelianization.
* `FiniteGaloisSubextension.intermediateFiniteAbelianOfCommutatorLe` —
  the finite abelian subextension cut out by a subgroup containing the
  commutator, with its `_field` formula.
* `FiniteGaloisSubextension.classFieldCandidate` — the candidate.

## Main statements

* `normOpenAddSubgroup_contains_finiteNormSubgroup` — a norm-open
  subgroup contains a finite Galois norm subgroup; proved.
* `FiniteGaloisSubextension.commutator_le_reciprocityPreimageSubgroup`
  — the pulled-back subgroup contains the commutator, for any `rE`;
  proved.
* `FiniteGaloisSubextension.finiteNormClass_mem_normQuotientSubgroup_iff`,
  `FiniteGaloisSubextension.reciprocityClass_mem_abelianizedSubgroup_iff`,
  `FiniteGaloisSubextension.reciprocityClass_mem_preimageSubgroup_iff`,
  `FiniteGaloisSubextension.candidateQuotient_eq_one_iff` — under
  `N_E ≤ H`, each of the three subgroups has exactly `H` as its inverse
  image, and the candidate's own quotient kills the transported class
  exactly on `H`; proved.
* `FiniteGaloisSubextension.classFieldCandidate_field` — the
  candidate's field is the fixed field of the pulled-back subgroup;
  proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
and the ambient group is `Type u` with the class-formation stock, so
the binders with which the source re-declares the second finiteness
instance and the commutator-cut extension at `Type*`, to escape the
universe pin on its `Rep ℤ G`, are merged into the section's; that
second local instance stays, re-declared for the section that builds
the candidate as in the source. The norm subgroup of a finite Galois
subextension is `Atlas.Knowledge.NormTopology`'s and the intermediate
correspondence is `Atlas.Knowledge.IntermediateGaloisCorrespondence`'s.
Everything else ports token-for-token; the file is the source's
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean` whole
in its declarations, its three section comments not carried, as the
layer's items carry none.

## References

* n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory in Lean 4*,
  [GitHub repository](https://github.com/n-yamaguchi-0729/ClassFieldTheory), pinned commit
  `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- **A norm-open subgroup contains a finite Galois norm subgroup**:
the first step of the finite abelian classification theorem's
surjectivity proof — an open subgroup in the norm topology contains the
norm subgroup of an actual finite Galois subextension (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:40`). -/
theorem normOpenAddSubgroup_contains_finiteNormSubgroup
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hH : IsNormOpen A K H) :
    ∃ E : FiniteGaloisSubextension K, FiniteGaloisSubextension.normSubgroup A E ≤ H :=
  (normTopology_addSubgroup_isOpen_iff A K H).1 hH

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The relative quotient of a finite Galois subextension is finite, as
an instance local to the section (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:51`). -/
local instance normQuotient_extensionQuotient_finite
    (E : FiniteGaloisSubextension K) :
    Finite (K.toSubgroup ⧸ E.field.toSubgroup.subgroupOf K.toSubgroup) :=
  E.finite

/-- The image of `H` in the actual norm quotient under the quotient map
— the subgroup `H / N_E` once `N_E ≤ H` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:58`). -/
def normQuotientSubgroup
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K)) :
    AddSubgroup (FiniteNormQuotient A K E.field E.below) := by
  letI : Finite (K.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf K.toSubgroup) := E.finite
  exact H.map (finiteNormClassHom A K E.field E.below)

omit [IsTopologicalGroup G] in
/-- If `N_E ⊆ H`, then `H` is exactly the full inverse image of
`H / N_E` — the group-theoretic fact used in the middle of the
finite-classification surjectivity proof (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:70`). -/
theorem finiteNormClass_mem_normQuotientSubgroup_iff
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hEH : normSubgroup A E ≤ H)
    (a : ambientFixedAddSubgroup A K) :
    letI : Finite (K.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf K.toSubgroup) := E.finite
    finiteNormClass A K E.field E.below a ∈
        normQuotientSubgroup A E H ↔
      a ∈ H := by
  letI : Finite (K.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf K.toSubgroup) := E.finite
  constructor
  · rintro ⟨b, hb, hba⟩
    have hba' : finiteNormClass A K E.field E.below b =
        finiteNormClass A K E.field E.below a := by
      simpa [finiteNormClass] using hba
    have hzero : finiteNormClass A K E.field E.below (b - a) = 0 := by
      rw [finiteNormClass_sub, hba', sub_self]
    have hsub : b - a ∈ normSubgroup A E :=
      (finiteNormClass_eq_zero_iff A K E.field E.below (b - a)).1 hzero
    have hsubH : b - a ∈ H := hEH hsub
    have ha : a = b - (b - a) := by abel
    rw [ha]
    exact H.sub_mem hb hsubH
  · intro ha
    exact ⟨a, ha, rfl⟩

/-- Transport `H / N_E` through a specified finite reciprocity
equivalence and forget additive notation: a genuine subgroup of the
actual abelianization `G(E/K)ᵃᵇ`. The argument `rE` is kept explicit;
this definition does not construct the finite reciprocity equivalence
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:106`). -/
def reciprocityAbelianizedSubgroup
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    Subgroup (Abelianization E.extensionQuotient) := by
  letI : Finite (K.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf K.toSubgroup) := E.finite
  exact AddSubgroup.toSubgroup'
    ((normQuotientSubgroup A E H).map rE.toAddMonoidHom)

omit [IsTopologicalGroup G] in
/-- Membership in the transported subgroup is literal membership of the
corresponding reciprocity class in the image of `H / N_E` under the
equivalence (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:120`). -/
theorem mem_reciprocityAbelianizedSubgroup_iff
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (q : Abelianization E.extensionQuotient) :
    q ∈ reciprocityAbelianizedSubgroup A E H rE ↔
      ∃ z ∈ normQuotientSubgroup A E H,
        rE z = Additive.ofMul q := by
  letI : Finite (K.toSubgroup ⧸
      E.field.toSubgroup.subgroupOf K.toSubgroup) := E.finite
  rfl

/-- The representative-level abelianized class map, obtained by first
passing to `A_K / N_E` and then applying the specified equivalence
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:135`). -/
def reciprocityAbelianizedClassHom
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    ambientFixedAddSubgroup A K →+
      Additive (Abelianization E.extensionQuotient) :=
  rE.toAddMonoidHom.comp (finiteNormClassHom A K E.field E.below)

omit [IsTopologicalGroup G] in
/-- If `N_E ⊆ H`, the transported subgroup has exactly `H` as its
inverse image under the abelianized class map — the precise
full-preimage statement used before taking the fixed field in the
finite classification argument (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:147`). -/
theorem reciprocityClass_mem_abelianizedSubgroup_iff
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hEH : normSubgroup A E ≤ H)
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (a : ambientFixedAddSubgroup A K) :
    Additive.toMul (reciprocityAbelianizedClassHom A E rE a) ∈
        reciprocityAbelianizedSubgroup A E H rE ↔
      a ∈ H := by
  change rE (finiteNormClass A K E.field E.below a) ∈
      (normQuotientSubgroup A E H).map rE.toAddMonoidHom ↔
    a ∈ H
  constructor
  · rintro ⟨z, hz, hza⟩
    have hzEq : z = finiteNormClass A K E.field E.below a :=
      rE.injective hza
    rw [hzEq] at hz
    exact (finiteNormClass_mem_normQuotientSubgroup_iff A E H hEH a).1 hz
  · intro ha
    refine ⟨finiteNormClass A K E.field E.below a, ?_, rfl⟩
    exact (finiteNormClass_mem_normQuotientSubgroup_iff A E H hEH a).2 ha

end FiniteGaloisSubextension

/-- Pull a subgroup of an abelianization back to the original finite
Galois group (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:176`). -/
def abelianizationPreimageSubgroup
    {Q : Type*} [Group Q] (T : Subgroup (Abelianization Q)) :
    Subgroup Q :=
  T.comap (Abelianization.of : Q →* Abelianization Q)

/-- Every such pullback contains the commutator subgroup of that group
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:182`). -/
theorem commutator_le_abelianizationPreimageSubgroup
    {Q : Type*} [Group Q] (T : Subgroup (Abelianization Q)) :
    commutator Q ≤ abelianizationPreimageSubgroup T := by
  intro q hq
  change Abelianization.of q ∈ T
  have hk : q ∈
      MonoidHom.ker (Abelianization.of : Q →* Abelianization Q) :=
    Abelianization.commutator_subset_ker
      (Abelianization.of : Q →* Abelianization Q) hq
  rw [MonoidHom.mem_ker.mp hk]
  exact T.one_mem

namespace FiniteGaloisSubextension

variable {K : ClosedSubgroup G}

/-- The finiteness of the relative quotient again, local to the section
that builds the candidate (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:198`). -/
local instance candidate_extensionQuotient_finite
    (E : FiniteGaloisSubextension K) :
    Finite (K.toSubgroup ⧸ E.field.toSubgroup.subgroupOf K.toSubgroup) :=
  E.finite

/-- The actual finite abelian intermediate extension cut out by a
subgroup `S ≤ G(E/K)` containing the commutator (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:206`). -/
def intermediateFiniteAbelianOfCommutatorLe
    (E : FiniteGaloisSubextension K)
    (S : Subgroup E.extensionQuotient)
    (hS : commutator E.extensionQuotient ≤ S) :
    FiniteAbelianSubextension K := by
  let hnormal : S.Normal :=
    Subgroup.Normal.of_commutator_le E.extensionQuotient hS
  letI : S.Normal := hnormal
  let M := E.intermediateFiniteGalois S hnormal
  refine
    { toFiniteGaloisExtension := M
      commutative := ?_ }
  let e := E.upperQuotientEquiv S
  letI : IsMulCommutative (E.extensionQuotient ⧸ S) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 hS
  refine ⟨⟨?_⟩⟩
  intro x y
  obtain ⟨x', rfl⟩ := e.surjective x
  obtain ⟨y', rfl⟩ := e.surjective y
  calc
    e x' * e y' = e (x' * y') := (map_mul e x' y').symm
    _ = e (y' * x') := congrArg e
      (Std.Commutative.comm
        (op := fun a b : E.extensionQuotient ⧸ S => a * b) x' y')
    _ = e y' * e x' := map_mul e y' x'

/-- The field underlying the preceding package is the literal fixed
field of `S` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:237`). -/
@[simp]
theorem intermediateFiniteAbelianOfCommutatorLe_field
    (E : FiniteGaloisSubextension K)
    (S : Subgroup E.extensionQuotient)
    (hS : commutator E.extensionQuotient ≤ S) :
    (intermediateFiniteAbelianOfCommutatorLe E S hS).field =
      E.intermediateField S :=
  rfl

/-- The subgroup obtained from `H / N_E` on the abelianization side,
pulled back to the actual finite Galois quotient (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:249`). -/
def reciprocityPreimageSubgroup
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    Subgroup E.extensionQuotient :=
  abelianizationPreimageSubgroup
    (reciprocityAbelianizedSubgroup A E H rE)

omit [IsTopologicalGroup G] in
/-- The actual subgroup used to define the intermediate field contains
the commutator, independently of any kernel assertion for `rE`
(Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:261`). -/
theorem commutator_le_reciprocityPreimageSubgroup
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    commutator E.extensionQuotient ≤
      reciprocityPreimageSubgroup A E H rE :=
  commutator_le_abelianizationPreimageSubgroup _

omit [IsTopologicalGroup G] in
/-- The pulled-back subgroup has exactly `H` as the inverse image of
the representative-level reciprocity class — the group-side form of the
full-preimage assertion used in the finite-classification surjectivity
proof (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:274`). -/
theorem reciprocityClass_mem_preimageSubgroup_iff
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hEH : normSubgroup A E ≤ H)
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (a : ambientFixedAddSubgroup A K) :
    Quotient.out (Additive.toMul
        (reciprocityAbelianizedClassHom A E rE a)) ∈
        reciprocityPreimageSubgroup A E H rE ↔
      a ∈ H := by
  change Abelianization.of (Quotient.out (Additive.toMul
      (reciprocityAbelianizedClassHom A E rE a))) ∈
        reciprocityAbelianizedSubgroup A E H rE ↔ a ∈ H
  rw [show Abelianization.of (Quotient.out (Additive.toMul
      (reciprocityAbelianizedClassHom A E rE a))) =
        Additive.toMul (reciprocityAbelianizedClassHom A E rE a) by
      exact Quotient.out_eq' _]
  exact reciprocityClass_mem_abelianizedSubgroup_iff A E H hEH rE a

omit [IsTopologicalGroup G] in
/-- Equivalently, the representative of the transported reciprocity
class restricts trivially to the quotient cut out by the candidate
precisely for the elements of `H` (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:298`). -/
theorem candidateQuotient_eq_one_iff
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (hEH : normSubgroup A E ≤ H)
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient))
    (a : ambientFixedAddSubgroup A K) :
    let S := reciprocityPreimageSubgroup A E H rE
    letI : S.Normal := Subgroup.Normal.of_commutator_le E.extensionQuotient
      (commutator_le_reciprocityPreimageSubgroup A E H rE)
    QuotientGroup.mk' S
        (Quotient.out (Additive.toMul
          (reciprocityAbelianizedClassHom A E rE a))) = 1 ↔
      a ∈ H := by
  dsimp only
  letI : (reciprocityPreimageSubgroup A E H rE).Normal :=
    Subgroup.Normal.of_commutator_le E.extensionQuotient
      (commutator_le_reciprocityPreimageSubgroup A E H rE)
  constructor
  · intro h
    apply (reciprocityClass_mem_preimageSubgroup_iff
      A E H hEH rE a).1
    exact (QuotientGroup.eq_one_iff _).1 h
  · intro ha
    apply (QuotientGroup.eq_one_iff _).2
    exact (reciprocityClass_mem_preimageSubgroup_iff
      A E H hEH rE a).2 ha

/-- **The class field candidate**: the finite abelian intermediate
extension determined by the subgroup transported from `H / N_E`, the
field candidate in the surjectivity proof of the finite abelian
classification theorem. No claim that its norm subgroup equals `H` is
made before finite reciprocity is available (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:330`). -/
def classFieldCandidate
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    FiniteAbelianSubextension K :=
  intermediateFiniteAbelianOfCommutatorLe E
    (reciprocityPreimageSubgroup A E H rE)
    (commutator_le_reciprocityPreimageSubgroup A E H rE)

/-- The candidate is cut out by the explicit pulled-back subgroup, not
by an opaque correspondence object (Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/ClassFieldCandidate.lean:343`). -/
@[simp]
theorem classFieldCandidate_field
    (A : Rep ℤ G) (E : FiniteGaloisSubextension K)
    (H : AddSubgroup (ambientFixedAddSubgroup A K))
    (rE : FiniteNormQuotient A K E.field E.below ≃+
      Additive (Abelianization E.extensionQuotient)) :
    (classFieldCandidate A E H rE).field =
      E.intermediateField
        (reciprocityPreimageSubgroup A E H rE) :=
  by simp [classFieldCandidate]

end FiniteGaloisSubextension

end

end Atlas.Knowledge
