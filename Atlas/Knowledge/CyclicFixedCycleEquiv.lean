import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ExtensionFixedRepresentation
import Atlas.Knowledge.ExtensionFixedRepresentationEquiv
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.RelativeNorm

/-!
# cyclic fixed-cycle equivalence

For a finite cyclic extension `L / K` with chosen generator `g` of
`G(L/K)`, the actual fixed group `A_K` is additively equivalent to the
cycles object — the kernel of `ρ(g) − 1` — of the norm-composed-sub
short complex of the descended extension representation: the bridge that
lets a `ρ(g)`-fixed vector be read back as an element of `A_K` (#104).

## Main definitions

* `cyclicFixedCycleEquiv` — `A_K ≃+` the cycles object of
  `Rep.FiniteCyclicGroup.normHomCompSub` at the extension
  representation.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling. Of
the source file's eleven declarations this is the only one the
reciprocity assembly still consumes: the layer's
`Atlas.Knowledge.ClassFieldAxiom` item states the class-field axiom
elementarily on the norm quotient, which absorbs the source's
Tate-comparison chain (`cyclicNormClassHom` with its kernel,
surjectivity, and application lemmas, `cyclicFixedCycleEquiv_relativeNorm`,
and the three equivalences through degree-zero Tate cohomology) and
already carries the file's three consequence theorems under their source
names; `additiveExtensionQuotient_card` lives in
`Atlas.Knowledge.FiniteAbstractExtension`. The acting group is pinned
to `Type` as in the source's `IntegralRepGroupType`, and the pin is
real: Mathlib's `Rep.FiniteCyclicGroup` namespace puts the coefficient
ring and the acting group in one universe, and `ℤ` sits in `Type 0`.
The source's `isCyclic_of_generator` is the anonymous instance
`⟨⟨g, hg⟩⟩`, the layer's standing conversion.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

open CategoryTheory

variable {G : Type} [Group G] [TopologicalSpace G]

/-- **The actual fixed group `A_K` is the kernel of `ρ(g)-1` on `A_L`
when `g` generates `G(L/K)`** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean:30`]
[Yamaguchi2026]). -/
def cyclicFixedCycleEquiv
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (hfinite : Finite (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup))
    (g : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    letI := hnormal
    letI := hfinite
    letI := Fintype.ofFinite
      (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    letI : IsCyclic
        (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      ⟨⟨g, hg⟩⟩
    letI : CommGroup
        (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
      IsCyclic.commGroup
    let M := extensionFixedRepresentation A K L hLK hnormal
    let T := Rep.FiniteCyclicGroup.normHomCompSub M g
    ambientFixedAddSubgroup A K ≃+
      T.moduleCatLeftHomologyData.K := by
  dsimp only
  letI := hnormal
  letI := hfinite
  letI := Fintype.ofFinite
    (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
  letI : IsCyclic (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
    ⟨⟨g, hg⟩⟩
  letI : CommGroup (K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A K L hLK hnormal
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  let toCycle : ambientFixedAddSubgroup A K →
      T.moduleCatLeftHomologyData.K := fun a => by
    let aL := fixedFieldInclusion A K L hLK a
    let aM : M.V :=
      (extensionFixedRepresentationEquiv A K L hLK hnormal).symm aL
    refine ⟨aM, sub_eq_zero.mpr ?_⟩
    refine Quotient.inductionOn' g ?_
    intro k
    apply Subtype.ext
    change A.ρ k.1 a.1 = a.1
    exact a.2 k
  let fromCycle : T.moduleCatLeftHomologyData.K →
      ambientFixedAddSubgroup A K := fun x => by
    let aM : M.V := x.1
    let aL : ambientFixedAddSubgroup A L :=
      extensionFixedRepresentationEquiv A K L hLK hnormal aM
    have hxzero : T.g.hom aM = 0 := x.2
    have hxg : M.ρ g aM = aM := by
      apply sub_eq_zero.mp
      exact hxzero
    have hxall : ∀ q, M.ρ q aM = aM := by
      letI : Module ℤ M := M.hV2
      exact (Representation.mem_invariants_iff_of_forall_mem_zpowers
        M.ρ g hg aM).2 hxg
    refine ⟨aL.1, ?_⟩
    intro k
    have hk := hxall
      ((QuotientGroup.mk' (L.toSubgroup.subgroupOf K.toSubgroup)) k)
    have haction := extensionFixedRepresentation_action_coe
      A K L hLK hnormal
      ((QuotientGroup.mk' (L.toSubgroup.subgroupOf K.toSubgroup)) k) aM
    have haction' :
        (M.ρ ((QuotientGroup.mk'
          (L.toSubgroup.subgroupOf K.toSubgroup)) k) aM).1 =
          A.ρ k.1 aL.1 := by
      calc
        _ = relativeCosetAction A K L hLK aL
              ((QuotientGroup.mk'
                (L.toSubgroup.subgroupOf K.toSubgroup)) k) := haction
        _ = A.ρ k.1 aL.1 :=
          relativeCosetAction_mk A K L hLK aL k
    exact haction'.symm.trans ((congrArg Subtype.val hk).trans rfl)
  exact
    { toFun := toCycle
      invFun := fromCycle
      left_inv := by
        intro a
        apply Subtype.ext
        rfl
      right_inv := by
        intro x
        apply Subtype.ext
        rfl
      map_add' := by
        intro a b
        apply Subtype.ext
        apply Subtype.ext
        rfl }

end

end Atlas.Knowledge
