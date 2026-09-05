import Mathlib
import Atlas.Knowledge.AmbientFixedAddSubgroup
import Atlas.Knowledge.ElementFixedAddSubgroup
import Atlas.Knowledge.ExtensionFixedRepresentation
import Atlas.Knowledge.ExtensionFixedRepresentationEquiv
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.RelativeNorm

/-!
# cyclic fixed-cycle equivalence

For a finite cyclic extension `L / K` with chosen generator `g` of
`G(L/K)`, the actual fixed group `A_K` is additively equivalent to the
fixed subgroup of `ρ(g)` on the descended extension representation —
the cycles of the norm-vs-difference complex read elementwise: the
bridge that lets a `ρ(g)`-fixed vector be read back as an element of
`A_K` (#104).

## Main definitions

* `cyclicFixedCycleEquiv` — `A_K ≃+` the `ρ(g)`-fixed subgroup of the
  extension representation.

## Implementation notes

The cycles object is stated as
`Atlas.Knowledge.elementFixedAddSubgroup`, not as the cycles of
Mathlib's `Rep.FiniteCyclicGroup.normHomCompSub`: the two carry the
same elements (`ker(ρ(g) − 1)` against fixed points, `sub_eq_zero`
apart), but the complex lives in a one-universe `{k G : Type u}` block,
which at the layer's `ℤ` coefficients would force the ambient group
into `Type 0` — the pin this item carried until the #104 universe
hoist. The elementwise codomain also needs no finiteness, cyclicity, or
commutativity of the quotient, so the finite-quotient argument and the
instance tower the homological spelling demanded are gone; `hg` alone
drives the fixed-point reduction through
`Representation.mem_invariants_iff_of_forall_mem_zpowers`. The relative
subgroup is the layer's `Subgroup.subgroupOf` spelling. Of the source
file's fourteen declarations this is the only one the reciprocity
assembly still consumes: the layer's `Atlas.Knowledge.ClassFieldAxiom`
item states the class-field axiom elementarily on the norm quotient,
which absorbs the source's Tate-comparison chain (`cyclicNormClassHom`
with its kernel, surjectivity, and application lemmas,
`cyclicFixedCycleEquiv_relativeNorm`, and the three equivalences
through degree-zero Tate cohomology) and already carries the file's
three consequence theorems under their source names — absorbing with
them the camelCase helper `finiteNormQuotientFiniteOfClassFieldAxiom`
the finiteness theorem wraps, consumed nowhere outside the file;
`additiveExtensionQuotient_card` lives in
`Atlas.Knowledge.FiniteAbstractExtension`. The source's
`isCyclic_of_generator` instance is not even needed here any more.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- **The actual fixed group `A_K` is the fixed subgroup of `ρ(g)` on
`A_L` when `g` generates `G(L/K)`** ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/CyclicNormQuotient.lean:30`]
[Yamaguchi2026]). -/
def cyclicFixedCycleEquiv
    (A : Rep ℤ G)
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (L.toSubgroup.subgroupOf K.toSubgroup).Normal)
    (g : K.toSubgroup ⧸ L.toSubgroup.subgroupOf K.toSubgroup)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    ambientFixedAddSubgroup A K ≃+
      elementFixedAddSubgroup
        (extensionFixedRepresentation A K L hLK hnormal) g := by
  letI := hnormal
  let M := extensionFixedRepresentation A K L hLK hnormal
  let toCycle : ambientFixedAddSubgroup A K →
      elementFixedAddSubgroup M g := fun a => by
    let aL := fixedFieldInclusion A K L hLK a
    let aM : M.V :=
      (extensionFixedRepresentationEquiv A K L hLK hnormal).symm aL
    refine ⟨aM, show M.ρ g aM = aM from ?_⟩
    refine Quotient.inductionOn' g ?_
    intro k
    apply Subtype.ext
    change A.ρ k.1 a.1 = a.1
    exact a.2 k
  let fromCycle : elementFixedAddSubgroup M g →
      ambientFixedAddSubgroup A K := fun x => by
    let aM : M.V := x.1
    let aL : ambientFixedAddSubgroup A L :=
      extensionFixedRepresentationEquiv A K L hLK hnormal aM
    have hxg : M.ρ g aM = aM := x.2
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
