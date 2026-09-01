import Mathlib
import Atlas.Knowledge.FiniteAbstractField
import Atlas.Knowledge.FiniteAbstractFieldExtension
import Atlas.Knowledge.FiniteGaloisSubextension
import Atlas.Knowledge.FrobeniusField
import Atlas.Knowledge.FrobeniusPowerFixedField
import Atlas.Knowledge.GaloisSubextension

/-!
# Frobenius fixed-field tower

Finite towers of Frobenius fixed fields, bundled with the normality and
finiteness data the norm and unit calculations consume: the ambient
Galois extension, both Frobenius elements, the fixed-field inclusion, and
exactly the finiteness witnesses the unit representation asks for —
stored once, so downstream statements stop re-threading proof-dependent
inclusions and quotient instances independently (#104).

## Main definitions

* `DegreeData.frobeniusFixedAbstractField` — the Frobenius fixed field
  bundled with its absolute finiteness.
* `DegreeData.FrobeniusFixedFieldTower` — the finite normal tower between
  two Frobenius fixed fields.
* `DegreeData.FiniteAmbientFrobeniusFixedFieldTower` — the tower with a
  finite ambient extension.
* `DegreeData.FrobeniusPowerFixedFieldTower` — the power tower fixed by
  `φⁿ² ≤ φⁿ`, from which inclusion, normality, and commutation are
  consequences.

## Implementation notes

The relative subgroup is the layer's `Subgroup.subgroupOf` spelling,
which mentions no containment — so the source's statement-level
`let hTS` inside the power tower's relative-finiteness field, feeding
only `extensionSubgroup`, goes. The ambient group is generic
(`IntegralRepGroupType` is the source's universe device; the layer's
`Rep` is polymorphic).

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- **The Frobenius fixed field bundled with its proved absolute
finiteness** — the field object used by valuation and unit APIs
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:24`]
[Yamaguchi2026]). -/
noncomputable def frobeniusFixedAbstractField
    (D : DegreeData G) [IsTopologicalGroup G]
    (K : FiniteResidueAbstractField D) (L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.field.toSubgroup)
    [hLnormal : (L.toSubgroup.subgroupOf K.field.toSubgroup).Normal]
    (σ : D.FrobeniusElements K L hLK)
    [Finite ((baseField G).toSubgroup ⧸
      (D.frobeniusFixedField K L hLK σ).toSubgroup.subgroupOf
        (baseField G).toSubgroup)] :
    FiniteAbstractField G where
  field := D.frobeniusFixedField K L hLK σ
  finite := inferInstance

/-- **A finite normal tower between two Frobenius fixed fields**: the
ambient Galois extension, both Frobenius elements, the fixed-field
inclusion, and exactly the finiteness hypotheses needed by the unit
representation, stored once ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:45`]
[Yamaguchi2026]). -/
structure FrobeniusFixedFieldTower
    (D : DegreeData G) [IsTopologicalGroup G] where
  /-- The finite-residue field in which the ambient Galois extension
  begins. -/
  ambientBase : FiniteResidueAbstractField D
  /-- The ambient Galois subextension. -/
  ambient : GaloisSubextension ambientBase.field
  /-- The Frobenius element whose fixed field is the base of the tower. -/
  baseFrobenius :
    D.FrobeniusElements ambientBase ambient.field ambient.below
  /-- The Frobenius element whose fixed field is the top of the tower. -/
  fieldFrobenius :
    D.FrobeniusElements ambientBase ambient.field ambient.below
  /-- Inclusion of the top fixed field into the base fixed field. -/
  field_le_base :
    (D.frobeniusFixedField ambientBase ambient.field ambient.below
        fieldFrobenius).toSubgroup ≤
      (D.frobeniusFixedField ambientBase ambient.field ambient.below
        baseFrobenius).toSubgroup
  /-- The relative quotient between the two fixed fields is finite. -/
  finiteQuotient :
    Finite
      ((D.frobeniusFixedField ambientBase ambient.field ambient.below
          baseFrobenius).toSubgroup ⧸
        (D.frobeniusFixedField ambientBase ambient.field ambient.below
          fieldFrobenius).toSubgroup.subgroupOf
          (D.frobeniusFixedField ambientBase ambient.field ambient.below
            baseFrobenius).toSubgroup)
  /-- The base fixed field is finite over the distinguished base. -/
  baseAbsoluteFinite :
    Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField ambientBase ambient.field ambient.below
          baseFrobenius).toSubgroup.subgroupOf (baseField G).toSubgroup)
  /-- The top fixed field is finite over the distinguished base. -/
  fieldAbsoluteFinite :
    Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField ambientBase ambient.field ambient.below
          fieldFrobenius).toSubgroup.subgroupOf (baseField G).toSubgroup)
  /-- The relative subgroup between the fixed fields is normal. -/
  normal :
    ((D.frobeniusFixedField ambientBase ambient.field ambient.below
      fieldFrobenius).toSubgroup.subgroupOf
      (D.frobeniusFixedField ambientBase ambient.field ambient.below
        baseFrobenius).toSubgroup).Normal
  /-- The two chosen ambient Frobenius elements commute. -/
  commute :
    baseFrobenius.1 * fieldFrobenius.1 =
      fieldFrobenius.1 * baseFrobenius.1

namespace FrobeniusFixedFieldTower

variable {D : DegreeData G} [IsTopologicalGroup G]

/-- The lower fixed field, finite over the distinguished base
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:112`]
[Yamaguchi2026]). -/
noncomputable def base (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractField G := by
  letI : Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField T.ambientBase T.ambient.field
          T.ambient.below T.baseFrobenius).toSubgroup.subgroupOf
          (baseField G).toSubgroup) :=
    T.baseAbsoluteFinite
  exact D.frobeniusFixedAbstractField T.ambientBase T.ambient.field
    T.ambient.below T.baseFrobenius

/-- The upper fixed field, finite over the distinguished base
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:127`]
[Yamaguchi2026]). -/
noncomputable def field (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractField G := by
  letI : Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField T.ambientBase T.ambient.field
          T.ambient.below T.fieldFrobenius).toSubgroup.subgroupOf
          (baseField G).toSubgroup) :=
    T.fieldAbsoluteFinite
  exact D.frobeniusFixedAbstractField T.ambientBase T.ambient.field
    T.ambient.below T.fieldFrobenius

/-- The fixed-field inclusion as a bundled Galois subextension
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:142`]
[Yamaguchi2026]). -/
noncomputable def toGaloisSubextension (T : FrobeniusFixedFieldTower D) :
    GaloisSubextension T.base.field where
  field := T.field.field
  below := T.field_le_base
  normal := T.normal

/-- The finite extension between the two bundled fixed fields
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:149`]
[Yamaguchi2026]). -/
noncomputable def extension (T : FrobeniusFixedFieldTower D) :
    FiniteAbstractFieldExtension G where
  field := T.field
  base := T.base
  below := T.field_le_base
  finiteQuotient := T.finiteQuotient

/-- A concrete lower-fixed-field element representing its Frobenius class
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:157`]
[Yamaguchi2026]). -/
structure Representative (T : FrobeniusFixedFieldTower D) where
  /-- The chosen element in the base fixed-field subgroup. -/
  element : T.extension.base.field.toSubgroup
  /-- The chosen element maps to the prescribed ambient Frobenius
  class. -/
  mapsToFrobenius :
    D.frobeniusFixedFieldToClosure T.ambientBase T.ambient.field
        T.ambient.below T.baseFrobenius element =
      D.frobeniusInClosure T.ambientBase T.ambient.field
        T.ambient.below T.baseFrobenius

/-- The extension subgroup of a bundled Frobenius fixed-field tower is
normal ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:168`]
[Yamaguchi2026]). -/
instance extensionNormal (T : FrobeniusFixedFieldTower D) :
    (T.extension.field.field.toSubgroup.subgroupOf
      T.extension.base.field.toSubgroup).Normal :=
  T.normal

/-- A representative which generates the finite fixed-field quotient
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:174`]
[Yamaguchi2026]). -/
structure CyclicGenerator (T : FrobeniusFixedFieldTower D)
    extends Representative T where
  /-- Every relative Galois element is a power of the representative's
  class. -/
  generates :
    ∀ x :
      T.extension.base.field.toSubgroup ⧸
        T.extension.field.field.toSubgroup.subgroupOf
          T.extension.base.field.toSubgroup,
      x ∈ Subgroup.zpowers (QuotientGroup.mk toRepresentative.element)

/-- The Galois quotient of a bundled Frobenius fixed-field extension is
finite ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:185`]
[Yamaguchi2026]). -/
instance extensionFinite (T : FrobeniusFixedFieldTower D) :
    Finite
      (T.extension.base.field.toSubgroup ⧸
        T.extension.field.field.toSubgroup.subgroupOf
          T.extension.base.field.toSubgroup) :=
  T.finiteQuotient

/-- The lower Frobenius fixed field in the tower is finite over the
distinguished base field ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:193`]
[Yamaguchi2026]). -/
instance baseAbsoluteFiniteInstance (T : FrobeniusFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField T.ambientBase T.ambient.field
          T.ambient.below T.baseFrobenius).toSubgroup.subgroupOf
          (baseField G).toSubgroup) :=
  T.baseAbsoluteFinite

/-- The upper Frobenius fixed field in the tower is finite over the
distinguished base field ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:205`]
[Yamaguchi2026]). -/
instance fieldAbsoluteFiniteInstance (T : FrobeniusFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField T.ambientBase T.ambient.field
          T.ambient.below T.fieldFrobenius).toSubgroup.subgroupOf
          (baseField G).toSubgroup) :=
  T.fieldAbsoluteFinite

end FrobeniusFixedFieldTower

/-- **A Frobenius fixed-field tower whose ambient Galois extension is
finite** — the additional finiteness lives on the opaque quotient object
`GaloisSubextension` exposes ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:221`]
[Yamaguchi2026]). -/
structure FiniteAmbientFrobeniusFixedFieldTower
    (D : DegreeData G) [IsTopologicalGroup G]
    extends FrobeniusFixedFieldTower D where
  /-- The ambient Galois quotient is finite. -/
  ambientFinite : Finite toFrobeniusFixedFieldTower.ambient.extensionQuotient

namespace FiniteAmbientFrobeniusFixedFieldTower

variable {D : DegreeData G} [IsTopologicalGroup G]

/-- The ambient Galois quotient stored in a finite Frobenius fixed-field
tower is finite ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:234`]
[Yamaguchi2026]). -/
instance ambientQuotientFinite
    (T : FiniteAmbientFrobeniusFixedFieldTower D) :
    Finite T.ambient.extensionQuotient :=
  T.ambientFinite

/-- Finiteness transported to the quotient presentation required by the
underlying Frobenius calculations ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:241`]
[Yamaguchi2026]). -/
noncomputable instance ambientRepresentedQuotientFinite
    (T : FiniteAmbientFrobeniusFixedFieldTower D) :
    Finite
      (T.ambientBase.field.toSubgroup ⧸
        T.ambient.field.toSubgroup.subgroupOf
          T.ambientBase.field.toSubgroup) :=
  Finite.of_equiv T.ambient.extensionQuotient
    T.ambient.extensionQuotientMulEquiv

end FiniteAmbientFrobeniusFixedFieldTower

/-- **The power tower fixed by `φⁿ² ≤ φⁿ`**: only data the universal
norm-descent construction already requires — the finite ambient Galois
extension, a degree-one Frobenius, its positive exponent, and the three
fixed-field finiteness witnesses; inclusion, normality, and commutation
are consequences of the power construction ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:259`]
[Yamaguchi2026]). -/
structure FrobeniusPowerFixedFieldTower
    (D : DegreeData G) [IsTopologicalGroup G] where
  /-- The finite-residue field at the base of the ambient extension. -/
  ambientBase : FiniteResidueAbstractField D
  /-- The finite ambient Galois subextension. -/
  ambient : FiniteGaloisSubextension ambientBase.field
  /-- A chosen degree-one Frobenius element in the ambient extension. -/
  frobenius :
    D.FrobeniusElements ambientBase ambient.field ambient.below
  /-- The chosen Frobenius has exponent one. -/
  exponent_one :
    D.frobeniusExponent ambientBase ambient.field ambient.below frobenius = 1
  /-- The positive exponent defining the first fixed field. -/
  n : ℕ
  /-- Positivity of the fixed-field exponent. -/
  n_pos : 0 < n
  /-- The fixed field of the `n`-th Frobenius power is finite over the
  distinguished base. -/
  baseAbsoluteFinite :
    let σ := D.frobeniusPowerOfDegreeOne ambientBase ambient.field
      ambient.below frobenius exponent_one n n_pos
    Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField ambientBase ambient.field ambient.below
          σ).toSubgroup.subgroupOf (baseField G).toSubgroup)
  /-- The fixed field of the `n²`-th Frobenius power is finite over the
  distinguished base. -/
  fieldAbsoluteFinite :
    let σn := D.frobeniusPowerOfDegreeOne ambientBase ambient.field
      ambient.below frobenius exponent_one (n * n) (Nat.mul_pos n_pos n_pos)
    Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField ambientBase ambient.field ambient.below
          σn).toSubgroup.subgroupOf (baseField G).toSubgroup)
  /-- The relative quotient between the `n`- and `n²`-power fixed fields
  is finite. -/
  relativeFinite :
    let σ := D.frobeniusPowerOfDegreeOne ambientBase ambient.field
      ambient.below frobenius exponent_one n n_pos
    let σn := D.frobeniusPowerOfDegreeOne ambientBase ambient.field
      ambient.below frobenius exponent_one (n * n) (Nat.mul_pos n_pos n_pos)
    Finite
      ((D.frobeniusFixedField ambientBase ambient.field ambient.below
          σ).toSubgroup ⧸
        (D.frobeniusFixedField ambientBase ambient.field ambient.below
          σn).toSubgroup.subgroupOf
          (D.frobeniusFixedField ambientBase ambient.field ambient.below
            σ).toSubgroup)

namespace FrobeniusPowerFixedFieldTower

variable {D : DegreeData G} [IsTopologicalGroup G]

/-- Forget ambient finiteness while retaining its Galois structure
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:315`]
[Yamaguchi2026]). -/
noncomputable def ambientGalois (P : FrobeniusPowerFixedFieldTower D) :
    GaloisSubextension P.ambientBase.field :=
  P.ambient.toGaloisSubextension

/-- The Frobenius element `φⁿ` defining the lower fixed field
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:320`]
[Yamaguchi2026]). -/
def baseFrobenius (P : FrobeniusPowerFixedFieldTower D) :
    D.FrobeniusElements P.ambientBase P.ambient.field P.ambient.below :=
  D.frobeniusPowerOfDegreeOne P.ambientBase P.ambient.field P.ambient.below
    P.frobenius P.exponent_one P.n P.n_pos

/-- The Frobenius element `φⁿ²` defining the upper fixed field
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:326`]
[Yamaguchi2026]). -/
def fieldFrobenius (P : FrobeniusPowerFixedFieldTower D) :
    D.FrobeniusElements P.ambientBase P.ambient.field P.ambient.below :=
  D.frobeniusPowerOfDegreeOne P.ambientBase P.ambient.field P.ambient.below
    P.frobenius P.exponent_one (P.n * P.n)
      (Nat.mul_pos P.n_pos P.n_pos)

/-- The original Frobenius commutes with its `n`-th power
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:333`]
[Yamaguchi2026]). -/
theorem frobenius_commute_base (P : FrobeniusPowerFixedFieldTower D) :
    P.frobenius.1 * P.baseFrobenius.1 =
      P.baseFrobenius.1 * P.frobenius.1 := by
  simpa [baseFrobenius] using
    ((Commute.refl P.frobenius.1).pow_right P.n).eq

/-- The original Frobenius commutes with its `n²`-th power
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:340`]
[Yamaguchi2026]). -/
theorem frobenius_commute_field (P : FrobeniusPowerFixedFieldTower D) :
    P.frobenius.1 * P.fieldFrobenius.1 =
      P.fieldFrobenius.1 * P.frobenius.1 := by
  simpa [fieldFrobenius] using
    ((Commute.refl P.frobenius.1).pow_right (P.n * P.n)).eq

/-- Inclusion of the field fixed by `φⁿ²` into the field fixed by `φⁿ`
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:347`]
[Yamaguchi2026]). -/
theorem field_le_base (P : FrobeniusPowerFixedFieldTower D) :
    (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
        P.fieldFrobenius).toSubgroup ≤
      (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
        P.baseFrobenius).toSubgroup :=
  D.frobeniusPowerFixedField_le P.ambientBase P.ambient.field P.ambient.below
    P.frobenius P.exponent_one P.n P.n P.n_pos P.n_pos

/-- Relative finiteness in the fixed-field presentation used by the
Frobenius action and norm lemmas — the witness is projected from the
power tower rather than requested again from callers ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:358`]
[Yamaguchi2026]). -/
instance relativeRepresentedQuotientFinite
    (P : FrobeniusPowerFixedFieldTower D) :
    Finite
      ((D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
          P.baseFrobenius).toSubgroup ⧸
        (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
          P.fieldFrobenius).toSubgroup.subgroupOf
          (D.frobeniusFixedField P.ambientBase P.ambient.field
            P.ambient.below P.baseFrobenius).toSubgroup) :=
  P.relativeFinite

/-- Absolute finiteness of the lower fixed field in the presentation used
by the Frobenius action API ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:373`]
[Yamaguchi2026]). -/
instance baseRepresentedAbsoluteFinite
    (P : FrobeniusPowerFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
          P.baseFrobenius).toSubgroup.subgroupOf
          (baseField G).toSubgroup) :=
  P.baseAbsoluteFinite

/-- Absolute finiteness of the upper fixed field in the presentation used
by the Frobenius action API ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:387`]
[Yamaguchi2026]). -/
instance fieldRepresentedAbsoluteFinite
    (P : FrobeniusPowerFixedFieldTower D) :
    Finite
      ((baseField G).toSubgroup ⧸
        (D.frobeniusFixedField P.ambientBase P.ambient.field P.ambient.below
          P.fieldFrobenius).toSubgroup.subgroupOf
          (baseField G).toSubgroup) :=
  P.fieldAbsoluteFinite

/-- **The power construction as the canonical fixed-field tower bundle**
([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:400`]
[Yamaguchi2026]). -/
noncomputable def toFrobeniusFixedFieldTower
    (P : FrobeniusPowerFixedFieldTower D) [T2Space G] :
    FrobeniusFixedFieldTower D where
  ambientBase := P.ambientBase
  ambient := P.ambientGalois
  baseFrobenius := P.baseFrobenius
  fieldFrobenius := P.fieldFrobenius
  field_le_base := P.field_le_base
  finiteQuotient := P.relativeFinite
  baseAbsoluteFinite := P.baseAbsoluteFinite
  fieldAbsoluteFinite := P.fieldAbsoluteFinite
  normal :=
    D.frobeniusPowerFixedField_normal P.ambientBase P.ambient.field
      P.ambient.below P.frobenius P.exponent_one P.n P.n P.n_pos P.n_pos
  commute := by
    change P.baseFrobenius.1 * P.fieldFrobenius.1 =
      P.fieldFrobenius.1 * P.baseFrobenius.1
    simpa [baseFrobenius, fieldFrobenius] using
      ((Commute.refl P.frobenius.1).pow_pow P.n (P.n * P.n)).eq

/-- The power tower together with the already assumed finiteness of its
ambient extension ([Yamaguchi 2026,
`AbstractClassFieldTheory/Reciprocity/Construction/FrobeniusFixedFieldTower.lean:422`]
[Yamaguchi2026]). -/
noncomputable def toFiniteAmbientFrobeniusFixedFieldTower
    (P : FrobeniusPowerFixedFieldTower D) [T2Space G] :
    FiniteAmbientFrobeniusFixedFieldTower D where
  toFrobeniusFixedFieldTower := P.toFrobeniusFixedFieldTower
  ambientFinite := by
    change Finite P.ambient.toGaloisSubextension.extensionQuotient
    exact Finite.of_equiv P.ambient.extensionQuotient
      P.ambient.toGaloisExtensionQuotientMulEquiv

end FrobeniusPowerFixedFieldTower

end DegreeData

end

end Atlas.Knowledge
