import Mathlib
import Atlas.Knowledge.ChosenPrimeElement
import Atlas.Knowledge.ClassFieldAxiom
import Atlas.Knowledge.CyclicFixedCycleEquiv
import Atlas.Knowledge.ExtensionFixedRepresentation
import Atlas.Knowledge.ExtensionFixedRepresentationEquiv
import Atlas.Knowledge.FiniteAbstractExtension
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteNormQuotient
import Atlas.Knowledge.FixedFieldInclusion
import Atlas.Knowledge.NormalizedValuationLaws
import Atlas.Knowledge.ProfiniteInteger
import Atlas.Knowledge.RelativeNorm
import Atlas.Knowledge.UnitRepresentation
import Atlas.Knowledge.ValuationData

/-!
# totally ramified fixed source

The totally ramified calculation of the abstract reciprocity proof: an
equality in an actual finite norm quotient is turned into an equality
of actual norms, the class-field axiom supplies the `σ − 1`-primitive,
and the element `π_L^k v a^{1-σ̃}` descends from `A_M` to the actual
fixed group `A_{M⁰}` with normalized valuation exactly `k` — the source
the valuation endpoint then forces to `k = 0` (#104).

## Main statements

* `ValuationData.primeNormClass_eq_zero_exists_unit_norm_eq` — a zero
  prime-norm class rewrites its representative as `π_L^k v` with an
  actual unit; proved.
* `ValuationData.abstractReciprocity_totallyRamified_fixedSource` — the
  full source-producing calculation, returning the primitive and the
  descended element of valuation `k`; proved.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
`DegreeData.FiniteAbstractExtension` is the layer's top-level
`FiniteAbstractExtension` (in `let`s and `simpa` unfold sets alike),
`ZHat` is `ProfiniteInteger`, and `isCyclic_of_generator` is the
anonymous instance `⟨⟨g, hg⟩⟩`. The source's
`abstractReciprocity_exists_hMinusOne_primitive` (its `:230`) is not
here: it already lives in `Atlas.Knowledge.ClassFieldAxiom` as a
projection of the elementary axiom under its source name, and the
final calculation consumes it unchanged. One `noncomputable section`
holds two ambient-group scopes with a shadowing `variable` line: the
private linear calculation (polymorphic in its own commutative group),
the prime/valuation calculation, and the action invariance precede it,
while the fixed-source theorem — a consumer of the Type-pinned
`Atlas.Knowledge.cyclicFixedCycleEquiv` — follows it. The private
helper keeps the source's privacy; its only consumer is in this file.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/- The additive form of the calculation: here `g` is `σ`, `t` is `σ̃`,
`c = π_Σ^k`, and `b = π_L^k v`; the hypotheses say that `t` fixes `c`,
that `g` and `t` have the same action on `b`, and that `b-c = a^g-a`;
commutativity of the cyclic quotient then shows that `b+a-a^t` is fixed
by `g` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean:40`]
[Yamaguchi2026]). -/
private theorem abstractReciprocity_fixedCombination
    {Q : Type*} [CommGroup Q] (M : Rep ℤ Q)
    (g t : Q) (c b a : M.V)
    (htc : M.ρ t c = c)
    (hgb : M.ρ g b = M.ρ t b)
    (hbc : b - c = M.ρ g a - a) :
    M.ρ g (b + a - M.ρ t a) = b + a - M.ρ t a := by
  have hcomm : M.ρ g (M.ρ t a) = M.ρ t (M.ρ g a) := by
    calc
      M.ρ g (M.ρ t a) = M.ρ (g * t) a := by
        rw [map_mul]
        rfl
      _ = M.ρ (t * g) a := by rw [mul_comm]
      _ = M.ρ t (M.ρ g a) := by
        rw [map_mul]
        rfl
  have hb : b = c + M.ρ g a - a := by
    calc
      b = (b - c) + c := by abel
      _ = (M.ρ g a - a) + c := by rw [hbc]
      _ = c + M.ρ g a - a := by abel
  have htbc := congrArg (fun z : M.V ↦ M.ρ t z) hbc
  have htbc' : M.ρ t b - c =
      M.ρ t (M.ρ g a) - M.ρ t a := by
    simpa only [map_sub, htc] using htbc
  have htb : M.ρ t b =
      c + M.ρ t (M.ρ g a) - M.ρ t a := by
    calc
      M.ρ t b = (M.ρ t b - c) + c := by abel
      _ = (M.ρ t (M.ρ g a) - M.ρ t a) + c := by rw [htbc']
      _ = c + M.ρ t (M.ρ g a) - M.ρ t a := by abel
  calc
    M.ρ g (b + a - M.ρ t a) =
        M.ρ g b + M.ρ g a - M.ρ g (M.ρ t a) := by
      simp only [map_add, map_sub]
    _ = M.ρ t b + M.ρ g a - M.ρ t (M.ρ g a) := by
      rw [hgb, hcomm]
    _ = c + M.ρ g a - M.ρ t a := by rw [htb]; abel
    _ = b + a - M.ρ t a := by rw [hb]; abel

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- **The representative extracted from a zero prime-norm class can be
written as `π_L^k v` with an actual unit `v ∈ U_L`** — the
prime/valuation calculation: both `L / K` and the Frobenius fixed field
`Σ / K` have relative residue degree one ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean:89`]
[Yamaguchi2026]). -/
theorem primeNormClass_eq_zero_exists_unit_norm_eq
    (v : ValuationData D A)
    (K L S : FiniteAbstractField G)
    (hLK : L.field.toSubgroup ≤ K.field.toSubgroup)
    (hSK : S.field.toSubgroup ≤ K.field.toSubgroup)
    (hTot : (AbstractExtension.mk
      L.field K.field hLK).IsTotallyRamified D)
    [hLKfinite : Finite
      (K.field.toSubgroup ⧸
        L.field.toSubgroup.subgroupOf K.field.toSubgroup)]
    [hSKfinite : Finite
      (K.field.toSubgroup ⧸
        S.field.toSubgroup.subgroupOf K.field.toSubgroup)]
    (hSigmaResidue :
      ((FiniteAbstractExtension.ofInclusion
        S.field K.field hSK).residueDegree D : ℕ) = 1)
    (k : ℕ)
    (piS : ambientFixedAddSubgroup A S.field)
    (piL : ambientFixedAddSubgroup A L.field)
    (hpiS : v.IsPrimeElement S piS)
    (hpiL : v.IsPrimeElement L piL)
    (hclass :
      finiteNormClass A K.field L.field hLK
          (relativeNorm A K.field S.field hSK (k • piS)) = 0) :
    ∃ w : v.unitAddSubgroup L,
      relativeNorm A K.field L.field hLK (k • piL + w.1) =
        relativeNorm A K.field S.field hSK (k • piS) := by
  obtain ⟨b, hb⟩ :=
    (finiteNormClass_eq_zero_iff
      A K.field L.field hLK _).1 hclass
  let EL : FiniteAbstractFieldExtension G :=
    { field := L
      base := K
      below := hLK
      finiteQuotient := hLKfinite }
  let ES : FiniteAbstractFieldExtension G :=
    FiniteAbstractFieldExtension.ofInclusion S.field K hSK
  have hvalB : v.valuationAt L b = k • v.oneValue := by
    apply Subtype.ext
    have hL := v.normalizedValuation_tower EL b
    have hS := v.normalizedValuation_tower ES (k • piS)
    have hTotEL : EL.IsTotallyRamified D := by
      simpa [EL, FiniteAbstractFieldExtension.IsTotallyRamified,
        FiniteAbstractFieldExtension.toFiniteAbstractExtension] using hTot
    have hresidue : (EL.residueDegree D : ℕ) = 1 :=
      EL.toFiniteAbstractExtension.residueDegree_eq_one_of_isTotallyRamified
        D hTotEL
    change (EL.residueDegree D : ℕ) •
        ((v.valuationAt L b : v.valueGroup) : ProfiniteInteger) =
      ((v.valuationAt K (relativeNorm A K.field L.field hLK b) :
        v.valueGroup) : ProfiniteInteger) at hL
    rw [hresidue, one_nsmul] at hL
    have hSigmaResidue' : (ES.residueDegree D : ℕ) = 1 := by
      let ES₀ :=
        FiniteAbstractExtension.ofInclusion S.field K.field hSK
      have hSigmaCard :
          ES₀.toAbstractExtension.relativeResidueDegreeCardinal D = 1 := by
        calc
          ES₀.toAbstractExtension.relativeResidueDegreeCardinal D =
              ((ES₀.residueDegree D : ℕ) : Cardinal) :=
            ES₀.relativeResidueDegreeCardinal_eq_coe D
          _ = 1 := by rw [hSigmaResidue]; simp
      apply Nat.cast_injective (R := Cardinal)
      unfold FiniteAbstractFieldExtension.residueDegree
      rw [← ES.toFiniteAbstractExtension.relativeResidueDegreeCardinal_eq_coe D]
      simpa [ES, ES₀, FiniteAbstractFieldExtension.toFiniteAbstractExtension,
        FiniteAbstractFieldExtension.ofInclusion,
        FiniteAbstractExtension.toAbstractExtension,
        FiniteAbstractExtension.ofInclusion] using hSigmaCard
    change (ES.residueDegree D : ℕ) •
        ((v.valuationAt S (k • piS) : v.valueGroup) : ProfiniteInteger) =
      ((v.valuationAt K
        (relativeNorm A K.field S.field hSK (k • piS)) :
          v.valueGroup) : ProfiniteInteger) at hS
    rw [hSigmaResidue', one_nsmul] at hS
    calc
      ((v.valuationAt L b : v.valueGroup) : ProfiniteInteger) =
          ((v.valuationAt K (relativeNorm A K.field L.field hLK b) :
            v.valueGroup) : ProfiniteInteger) := hL
      _ = ((v.valuationAt K
          (relativeNorm A K.field S.field hSK (k • piS)) :
            v.valueGroup) : ProfiniteInteger) := by rw [hb]
      _ = ((v.valuationAt S (k • piS) : v.valueGroup) : ProfiniteInteger) :=
        hS.symm
      _ = ((k • v.oneValue : v.valueGroup) : ProfiniteInteger) := by
        congr 1
        rw [map_nsmul, hpiS]
  let wL : ambientFixedAddSubgroup A L.field := b - k • piL
  have hw : v.valuationAt L wL = 0 := by
    change v.valuationAt L (b - k • piL) = 0
    rw [map_sub, map_nsmul, hvalB, hpiL, sub_self]
  let w : v.unitAddSubgroup L :=
    ⟨wL, (v.mem_unitAddSubgroup_iff L wL).2 hw⟩
  refine ⟨w, ?_⟩
  calc
    relativeNorm A K.field L.field hLK (k • piL + w.1) =
        relativeNorm A K.field L.field hLK b := by
      congr 1
      apply Subtype.ext
      dsimp [w, wL]
      abel
    _ = relativeNorm A K.field S.field hSK (k • piS) := hb

/-- Normalized valuation is invariant under the actual quotient action
— the quotient-representation form of the unit-cohomology axiom's
`valuationAt_normalExtensionAction` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean:192`]
[Yamaguchi2026]). -/
theorem valuationAt_extensionFixedRepresentation_action
    (v : ValuationData D A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (E.field.field.toSubgroup.subgroupOf
      E.base.field.toSubgroup).Normal)
    (q : E.base.field.toSubgroup ⧸
      E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
    (a : (extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal).V) :
    v.valuationAt E.field
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal
          ((extensionFixedRepresentation A E.base.field E.field.field
            E.below hnormal).ρ q a)) =
      v.valuationAt E.field
        (extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal a) := by
  letI := hnormal
  refine Quotient.inductionOn' q ?_
  intro r
  let aL : ambientFixedAddSubgroup A E.field.field :=
    extensionFixedRepresentationEquiv A E.base.field E.field.field
      E.below hnormal a
  have heq :
      extensionFixedRepresentationEquiv A E.base.field E.field.field
          E.below hnormal
          ((extensionFixedRepresentation A E.base.field E.field.field
            E.below hnormal).ρ
            (QuotientGroup.mk r) a) =
        normalExtensionAction A E.base.field E.field.field E.below
          hnormal r aL := by
    apply Subtype.ext
    rfl
  rw [heq]
  exact v.valuationAt_normalExtensionAction E hnormal r aL

end ValuationData

variable {G : Type} [Group G] [TopologicalSpace G]

namespace ValuationData

variable {D : DegreeData G} {A : Rep ℤ G}

/-- **The full source-producing calculation: it returns both the `H⁻¹`
primitive `a` and an actual element of `A_K` (with `K = M⁰` and
`L = M`) whose inclusion has normalized valuation `k`.** The two action
equations are not comparison data: they are the literal claims used in
this construction, namely that `σ̃` fixes `π_Σ`, and that `σ` and `σ̃`
have the same action on the element coming from `L` ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/TotallyRamified.lean:294`]
[Yamaguchi2026]). -/
theorem abstractReciprocity_totallyRamified_fixedSource
    (v : ValuationData D A) (hcf : SatisfiesClassFieldAxiom A)
    (E : FiniteAbstractFieldExtension G)
    (hnormal : (E.field.field.toSubgroup.subgroupOf
      E.base.field.toSubgroup).Normal)
    (g : E.base.field.toSubgroup ⧸
      E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
    (hg : ∀ q, q ∈ Subgroup.zpowers g)
    (t : E.base.field.toSubgroup ⧸
      E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
    (k : ℕ)
    (piSigma piL u : ambientFixedAddSubgroup A E.field.field)
    (w : v.unitAddSubgroup E.field)
    (hpiL : v.IsPrimeElement E.field piL)
    (hprime : k • piSigma = u + k • piL)
    (hnorm : relativeNorm A E.base.field E.field.field E.below w.1 =
      relativeNorm A E.base.field E.field.field E.below u)
    (htSigma : relativeCosetAction A E.base.field E.field.field
      E.below piSigma t = piSigma.1)
    (hgt : relativeCosetAction A E.base.field E.field.field E.below
        (k • piL + w.1) g =
      relativeCosetAction A E.base.field E.field.field E.below
        (k • piL + w.1) t) :
    let M := extensionFixedRepresentation A E.base.field E.field.field
      E.below hnormal
    ∃ (a : M.V) (x : ambientFixedAddSubgroup A E.base.field),
      fixedFieldInclusion A E.base.field E.field.field E.below x =
          extensionFixedRepresentationEquiv A E.base.field E.field.field
            E.below hnormal
            ((extensionFixedRepresentationEquiv A E.base.field E.field.field
              E.below hnormal).symm
                (k • piL + w.1) + a - M.ρ t a) ∧
        ((v.valuationAt E.field
          (fixedFieldInclusion A E.base.field E.field.field E.below x) :
          v.valueGroup) : ProfiniteInteger) =
          Int.castRingHom ProfiniteInteger (k : ℤ) := by
  letI := hnormal
  letI := E.finiteQuotient
  letI := Fintype.ofFinite
    (E.base.field.toSubgroup ⧸
      E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup)
  letI : IsCyclic
      (E.base.field.toSubgroup ⧸
        E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
    ⟨⟨g, hg⟩⟩
  letI : CommGroup
      (E.base.field.toSubgroup ⧸
        E.field.field.toSubgroup.subgroupOf E.base.field.toSubgroup) :=
    IsCyclic.commGroup
  let M := extensionFixedRepresentation A E.base.field E.field.field
    E.below hnormal
  let e := extensionFixedRepresentationEquiv A E.base.field E.field.field
    E.below hnormal
  let piSigmaM : M.V := e.symm piSigma
  let piLM : M.V := e.symm piL
  let uM : M.V := e.symm u
  let wM : M.V := e.symm w.1
  obtain ⟨a, ha⟩ :=
    abstractReciprocity_exists_hMinusOne_primitive hcf E hnormal
      g hg u w.1 hnorm
  have hSigmaM : M.ρ t piSigmaM = piSigmaM := by
    apply Subtype.ext
    calc
      (M.ρ t piSigmaM).1 =
          relativeCosetAction A E.base.field E.field.field E.below
            piSigma t := by
        simpa [M, e, piSigmaM] using
          extensionFixedRepresentation_action_coe
            A E.base.field E.field.field E.below hnormal t piSigmaM
      _ = piSigma.1 := htSigma
      _ = piSigmaM.1 := rfl
  have hSigmaPow : M.ρ t (k • piSigmaM) = k • piSigmaM := by
    calc
      M.ρ t (k • piSigmaM) = k • M.ρ t piSigmaM :=
        map_nsmul (M.ρ t) k piSigmaM
      _ = k • piSigmaM := by rw [hSigmaM]
  let bM : M.V := k • piLM + wM
  have hbAction : M.ρ g bM = M.ρ t bM := by
    apply Subtype.ext
    calc
      (M.ρ g bM).1 =
          relativeCosetAction A E.base.field E.field.field E.below
            (k • piL + w.1) g := by
        simpa [M, e, bM, piLM, wM] using
          extensionFixedRepresentation_action_coe A E.base.field
            E.field.field E.below hnormal g bM
      _ = relativeCosetAction A E.base.field E.field.field E.below
          (k • piL + w.1) t := hgt
      _ = (M.ρ t bM).1 := by
        simpa [M, e, bM, piLM, wM] using
          (extensionFixedRepresentation_action_coe
            A E.base.field E.field.field E.below hnormal t bM).symm
  have hbc : bM - k • piSigmaM = M.ρ g a - a := by
    rw [ha]
    apply Subtype.ext
    have hprime' : k • piSigma.1 = u.1 + k • piL.1 := by
      simpa using congrArg
        (fun z : ambientFixedAddSubgroup A E.field.field ↦ (z : A.V)) hprime
    change k • piL.1 + w.1.1 - k • piSigma.1 = w.1.1 - u.1
    rw [hprime']
    abel
  let xM : M.V := bM + a - M.ρ t a
  have hxM : M.ρ g xM = xM := by
    exact abstractReciprocity_fixedCombination M g t (k • piSigmaM) bM a
      hSigmaPow hbAction hbc
  let T := Rep.FiniteCyclicGroup.normHomCompSub M g
  let xCycle : T.moduleCatLeftHomologyData.K := ⟨xM, by
    change M.ρ g xM - xM = 0
    exact sub_eq_zero.mpr hxM⟩
  let x : ambientFixedAddSubgroup A E.base.field :=
    (cyclicFixedCycleEquiv A E.base.field E.field.field E.below
      hnormal E.finiteQuotient g hg).symm xCycle
  refine ⟨a, x, ?_, ?_⟩
  · apply Subtype.ext
    rfl
  · have hActionVal :=
      v.valuationAt_extensionFixedRepresentation_action
        E hnormal t a
    have hxFormula : fixedFieldInclusion A E.base.field E.field.field
        E.below x =
        k • piL + w.1 + e a - e (M.ρ t a) := by
      apply Subtype.ext
      rfl
    have hval :
        v.valuationAt E.field
          (fixedFieldInclusion A E.base.field E.field.field E.below x) =
          k • v.oneValue := by
      rw [hxFormula, map_sub, map_add, map_add, map_nsmul,
        hpiL, w.2, hActionVal]
      abel
    calc
      ((v.valuationAt E.field
        (fixedFieldInclusion A E.base.field E.field.field E.below x) :
          v.valueGroup) : ProfiniteInteger) =
          ((k • v.oneValue : v.valueGroup) : ProfiniteInteger) :=
        congrArg Subtype.val hval
      _ = k • (1 : ProfiniteInteger) := rfl
      _ = Int.castRingHom ProfiniteInteger (k : ℤ) := by
        simp

end ValuationData

end

end Atlas.Knowledge
