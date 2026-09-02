import Mathlib
import Atlas.Knowledge.TopologicalGeneration

/-!
# Double-coset orbit geometry

The group-theoretic geometry behind the transfer formula: orbits of `S`
on `Q ⧸ H` are the double cosets `S\\Q/H`, inversion exchanges the two
sides, surjective equivariant maps and group equivalences transport
orbit and coset sets, and closing a cyclic subgroup against a closed
finite-index subgroup changes neither its double cosets nor its orbit
sets — no class-formation or field-theoretic input anywhere (#104).

## Main definitions

* `orbitQuotientEquivDoubleCoset` — orbits are double cosets.
* `doubleCosetInversionEquiv` — inversion swaps the sides.
* `orbitQuotientSwapEquiv` — the orbit-set reindexing.
* `orbitQuotientEquivOfSurjectiveEquivariant` — equivariant transport.
* `leftCosetEquivOfMulEquiv` — coset transport along an equivalence.
* `doubleCosetClosedCyclicEquiv` — closure changes no double coset.
* `orbitQuotientClosedCyclicEquiv` — closure changes no orbit set.

## Main statements

* `orbitQuotientEquivDoubleCoset_mk` — the representative computation;
  proved.
* `orbitQuotientEquivDoubleCoset_symm_mk` — the inverse computation;
  proved.
* `orbitQuotientSwapEquiv_mk` — the swap inverts the representative;
  proved.
* `orbitQuotientEquivOfSurjectiveEquivariant_mk` — transported orbits;
  proved.
* `orbitQuotientEquivOfSurjectiveEquivariant_symm_mk` — lifted orbits;
  proved.
* `leftCosetEquivOfMulEquiv_mk` — transported cosets; proved.
* `doubleCoset_closedCyclic_eq` — the density step; proved.
* `orbitQuotientClosedCyclicEquiv_mk` — closure preserves represented
  orbits; proved.

## Implementation notes

A straight port with one spelling change: the coset-transport target
writes `S.map (e : Q →* R)` where the source writes
`S.map e.toMonoidHom` — the coercion is the simp normal form, and with
the source's spelling the transport lemma fails `simpNF`. Otherwise the
file is generic group theory and already speaks the layer's
`closedSubgroupGenerated` vocabulary. The citations name this file by
bare basename; it lives at
`AbstractClassFieldTheory/Reciprocity/Construction/` in the source.

## References

* [Yamaguchi2026] n-yamaguchi-0729, *ClassFieldTheory: local and global class field theory
  in Lean 4*, GitHub repository, pinned commit `6010237`, 2026.
-/

namespace Atlas.Knowledge

noncomputable section

universe u

open MulAction

/-- **Orbits of `S` on `Q ⧸ H` are the double cosets `S\\Q/H`** — the
indexing set in Mathlib's transfer formula is literally the double-coset
set the abstract class-field construction uses ([Yamaguchi 2026,
`DoubleCosetOrbitGeometry.lean:27`][Yamaguchi2026]). -/
noncomputable def orbitQuotientEquivDoubleCoset
    {Q : Type u} [Group Q] (S H : Subgroup Q) :
    Quotient (orbitRel S (Q ⧸ H)) ≃
      DoubleCoset.Quotient (S : Set Q) (H : Set Q) where
  toFun z := Quotient.liftOn' z
    (fun q => DoubleCoset.mk S H q.out) (by
      intro q₁ q₂ hq
      rw [orbitRel_apply, mem_orbit_iff] at hq
      obtain ⟨s, hs⟩ := hq
      symm
      apply (DoubleCoset.eq S H q₂.out q₁.out).2
      have hcoset :
          (QuotientGroup.mk q₁.out : Q ⧸ H) =
            QuotientGroup.mk (s.1 * q₂.out) := by
        calc
          QuotientGroup.mk q₁.out = q₁ := Quotient.out_eq' q₁
          _ = s • q₂ := hs.symm
          _ = s • (QuotientGroup.mk q₂.out : Q ⧸ H) :=
            congrArg (s • ·) (Quotient.out_eq' q₂).symm
          _ = QuotientGroup.mk (s.1 * q₂.out) := rfl
      have hh : q₁.out⁻¹ * (s.1 * q₂.out) ∈ H :=
        QuotientGroup.eq.mp hcoset
      refine ⟨s.1, s.2, (q₁.out⁻¹ * (s.1 * q₂.out))⁻¹,
        H.inv_mem hh, ?_⟩
      simp [mul_assoc])
  invFun z := Quotient.liftOn' z
    (fun x => Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H)) (by
      intro x y hxy
      rw [DoubleCoset.rel_iff] at hxy
      obtain ⟨s, hs, h, hh, rfl⟩ := hxy
      apply Quotient.eq''.mpr
      rw [orbitRel_apply, mem_orbit_iff]
      refine ⟨⟨s⁻¹, S.inv_mem hs⟩, ?_⟩
      apply QuotientGroup.eq.mpr
      simpa [mul_assoc] using hh)
  left_inv z := by
    refine Quotient.inductionOn' z ?_
    intro q
    change Quotient.mk'' (QuotientGroup.mk q.out : Q ⧸ H) = Quotient.mk'' q
    exact congrArg Quotient.mk'' (Quotient.out_eq' q)
  right_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    change DoubleCoset.mk S H (Quotient.out
      (QuotientGroup.mk x : Q ⧸ H)) = DoubleCoset.mk S H x
    apply (DoubleCoset.eq S H _ _).2
    have hh : (Quotient.out (QuotientGroup.mk x : Q ⧸ H))⁻¹ * x ∈ H :=
      QuotientGroup.leftRel_apply.mp
        (Quotient.exact' (Quotient.out_eq' (QuotientGroup.mk x : Q ⧸ H)))
    exact ⟨1, S.one_mem,
      (Quotient.out (QuotientGroup.mk x : Q ⧸ H))⁻¹ * x,
      hh, by simp⟩

/-- **The equivalence sends the orbit represented by `x` to its double
coset**, independently of the `Quotient.out` representative
([Yamaguchi 2026, `DoubleCosetOrbitGeometry.lean:84`][Yamaguchi2026]). -/
@[simp]
theorem orbitQuotientEquivDoubleCoset_mk
    {Q : Type u} [Group Q] (S H : Subgroup Q) (x : Q) :
    orbitQuotientEquivDoubleCoset S H
        (Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H)) =
      DoubleCoset.mk S H x := by
  change DoubleCoset.mk S H
      (Quotient.out (QuotientGroup.mk x : Q ⧸ H)) =
    DoubleCoset.mk S H x
  apply (DoubleCoset.eq S H _ _).2
  have hh :
      (Quotient.out (QuotientGroup.mk x : Q ⧸ H))⁻¹ * x ∈ H :=
    QuotientGroup.leftRel_apply.mp
      (Quotient.exact'
        (Quotient.out_eq' (QuotientGroup.mk x : Q ⧸ H)))
  exact ⟨1, S.one_mem,
    (Quotient.out (QuotientGroup.mk x : Q ⧸ H))⁻¹ * x,
    hh, by simp⟩

/-- **The inverse sends a represented double coset to the represented
orbit**
([Yamaguchi 2026, `DoubleCosetOrbitGeometry.lean:105`][Yamaguchi2026]). -/
@[simp]
theorem orbitQuotientEquivDoubleCoset_symm_mk
    {Q : Type u} [Group Q] (S H : Subgroup Q) (x : Q) :
    (orbitQuotientEquivDoubleCoset S H).symm (DoubleCoset.mk S H x) =
      Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H) :=
  rfl

/-- **Inversion exchanges the two sides of a double-coset space**
([Yamaguchi 2026, `DoubleCosetOrbitGeometry.lean:112`][Yamaguchi2026]). -/
noncomputable def doubleCosetInversionEquiv
    {Q : Type u} [Group Q] (S H : Subgroup Q) :
    DoubleCoset.Quotient (S : Set Q) (H : Set Q) ≃
      DoubleCoset.Quotient (H : Set Q) (S : Set Q) where
  toFun z := Quotient.liftOn' z
    (fun x => DoubleCoset.mk H S x⁻¹) (by
      intro x y hxy
      rw [DoubleCoset.rel_iff] at hxy
      obtain ⟨s, hs, h, hh, rfl⟩ := hxy
      apply (DoubleCoset.eq H S _ _).2
      exact ⟨h⁻¹, H.inv_mem hh, s⁻¹, S.inv_mem hs,
        by simp [mul_assoc]⟩)
  invFun z := Quotient.liftOn' z
    (fun x => DoubleCoset.mk S H x⁻¹) (by
      intro x y hxy
      rw [DoubleCoset.rel_iff] at hxy
      obtain ⟨h, hh, s, hs, rfl⟩ := hxy
      apply (DoubleCoset.eq S H _ _).2
      exact ⟨s⁻¹, S.inv_mem hs, h⁻¹, H.inv_mem hh,
        by simp [mul_assoc]⟩)
  left_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    change DoubleCoset.mk S H (x⁻¹)⁻¹ = DoubleCoset.mk S H x
    rw [inv_inv]
  right_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    change DoubleCoset.mk H S (x⁻¹)⁻¹ = DoubleCoset.mk H S x
    rw [inv_inv]

/-- **Orbit sets on the two quotient spaces are exchanged by
inversion** — the reindexing between the transfer and norm double-coset
decompositions in transfer–norm naturality ([Yamaguchi 2026,
`DoubleCosetOrbitGeometry.lean:146`][Yamaguchi2026]). -/
noncomputable def orbitQuotientSwapEquiv
    {Q : Type u} [Group Q] (S H : Subgroup Q) :
    Quotient (orbitRel S (Q ⧸ H)) ≃
      Quotient (orbitRel H (Q ⧸ S)) :=
  (orbitQuotientEquivDoubleCoset S H).trans
    ((doubleCosetInversionEquiv S H).trans
      (orbitQuotientEquivDoubleCoset H S).symm)

/-- **The swap sends the orbit represented by `x` to the orbit
represented by `x⁻¹`**, independently of the `Quotient.out`
representatives
([Yamaguchi 2026, `DoubleCosetOrbitGeometry.lean:158`][Yamaguchi2026]). -/
@[simp]
theorem orbitQuotientSwapEquiv_mk
    {Q : Type u} [Group Q] (S H : Subgroup Q) (x : Q) :
    orbitQuotientSwapEquiv S H
        (Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H)) =
      Quotient.mk'' (QuotientGroup.mk x⁻¹ : Q ⧸ S) := by
  change (orbitQuotientEquivDoubleCoset H S).symm
      (doubleCosetInversionEquiv S H
        (orbitQuotientEquivDoubleCoset S H
          (Quotient.mk'' (QuotientGroup.mk x : Q ⧸ H)))) = _
  unfold orbitQuotientEquivDoubleCoset doubleCosetInversionEquiv
  simp only [Equiv.coe_fn_mk, Quotient.liftOn'_mk'', Equiv.coe_fn_symm_mk]
  let u : Q := Quotient.out (QuotientGroup.mk x : Q ⧸ H)
  have hu : u⁻¹ * x ∈ H := by
    apply QuotientGroup.eq.mp
    exact Quotient.out_eq' (QuotientGroup.mk x : Q ⧸ H)
  apply Quotient.sound'
  rw [orbitRel_apply, mem_orbit_iff]
  refine ⟨⟨u⁻¹ * x, hu⟩, ?_⟩
  change QuotientGroup.mk ((u⁻¹ * x) * x⁻¹) =
    (QuotientGroup.mk u⁻¹ : Q ⧸ S)
  simp [mul_assoc]

/-- **A surjective homomorphism and an equivariant equivalence of the
acted-on sets induce an equivalence of orbit sets** ([Yamaguchi 2026,
`DoubleCosetOrbitGeometry.lean:182`][Yamaguchi2026]). -/
noncomputable def orbitQuotientEquivOfSurjectiveEquivariant
    {M : Type*} {N : Type*} {X : Type*} {Y : Type*} [Group M] [Group N]
    [MulAction M X] [MulAction N Y]
    (f : M →* N) (hf : Function.Surjective f) (e : X ≃ Y)
    (he : ∀ (m : M) (x : X), e (m • x) = f m • e x) :
    Quotient (orbitRel M X) ≃ Quotient (orbitRel N Y) :=
  { toFun := Quotient.map' e (by
      intro x y hxy
      rw [orbitRel_apply, mem_orbit_iff] at hxy ⊢
      obtain ⟨m, hm⟩ := hxy
      exact ⟨f m, (he m y).symm.trans (congrArg e hm)⟩)
    invFun := Quotient.map' e.symm (by
      intro x y hxy
      rw [orbitRel_apply, mem_orbit_iff] at hxy ⊢
      obtain ⟨n, hn⟩ := hxy
      obtain ⟨m, rfl⟩ := hf n
      refine ⟨m, ?_⟩
      apply e.injective
      rw [he, e.apply_symm_apply, e.apply_symm_apply]
      exact hn)
    left_inv := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro x
      change Quotient.mk'' (e.symm (e x)) = Quotient.mk'' x
      rw [e.symm_apply_apply]
    right_inv := by
      intro q
      refine Quotient.inductionOn' q ?_
      intro y
      change Quotient.mk'' (e (e.symm y)) = Quotient.mk'' y
      rw [e.apply_symm_apply] }

/-- **The transported orbit is represented by the image**
([Yamaguchi 2026, `DoubleCosetOrbitGeometry.lean:217`][Yamaguchi2026]). -/
@[simp]
theorem orbitQuotientEquivOfSurjectiveEquivariant_mk
    {M : Type*} {N : Type*} {X : Type*} {Y : Type*} [Group M] [Group N]
    [MulAction M X] [MulAction N Y]
    (f : M →* N) (hf : Function.Surjective f) (e : X ≃ Y)
    (he : ∀ (m : M) (x : X), e (m • x) = f m • e x) (x : X) :
    orbitQuotientEquivOfSurjectiveEquivariant f hf e he
        (Quotient.mk'' x) = Quotient.mk'' (e x) :=
  rfl

/-- **The inverse lifts a representative to its source orbit**
([Yamaguchi 2026, `DoubleCosetOrbitGeometry.lean:228`][Yamaguchi2026]). -/
@[simp]
theorem orbitQuotientEquivOfSurjectiveEquivariant_symm_mk
    {M : Type*} {N : Type*} {X : Type*} {Y : Type*} [Group M] [Group N]
    [MulAction M X] [MulAction N Y]
    (f : M →* N) (hf : Function.Surjective f) (e : X ≃ Y)
    (he : ∀ (m : M) (x : X), e (m • x) = f m • e x) (y : Y) :
    (orbitQuotientEquivOfSurjectiveEquivariant f hf e he).symm
        (Quotient.mk'' y) = Quotient.mk'' (e.symm y) :=
  rfl

/-- **A group equivalence transports left cosets along the image of a
subgroup**, with no normality hypothesis ([Yamaguchi 2026,
`DoubleCosetOrbitGeometry.lean:239`][Yamaguchi2026]). -/
noncomputable def leftCosetEquivOfMulEquiv
    {Q : Type*} {R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (S : Subgroup Q) :
    Q ⧸ S ≃ R ⧸ S.map (e : Q →* R) where
  toFun := Quotient.map' e (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    exact ⟨x⁻¹ * y, hxy, by simp⟩)
  invFun := Quotient.map' e.symm (by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    obtain ⟨z, hz, heq⟩ := hxy
    have hzEq : e.symm (x⁻¹ * y) = z := by
      rw [← heq]
      simp
    have hxyEq : (e.symm x)⁻¹ * e.symm y = z := by
      calc
        (e.symm x)⁻¹ * e.symm y = e.symm (x⁻¹ * y) := by simp
        _ = z := hzEq
    rw [hxyEq]
    exact hz)
  left_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change QuotientGroup.mk (e.symm (e x)) = QuotientGroup.mk x
    rw [e.symm_apply_apply]
  right_inv q := by
    refine Quotient.inductionOn' q ?_
    intro x
    change QuotientGroup.mk (e (e.symm x)) = QuotientGroup.mk x
    rw [e.apply_symm_apply]

/-- **The transported coset is represented by the image**
([Yamaguchi 2026, `DoubleCosetOrbitGeometry.lean:273`][Yamaguchi2026]). -/
@[simp]
theorem leftCosetEquivOfMulEquiv_mk
    {Q : Type*} {R : Type*} [Group Q] [Group R]
    (e : Q ≃* R) (S : Subgroup Q) (x : Q) :
    leftCosetEquivOfMulEquiv e S (QuotientGroup.mk x) =
      QuotientGroup.mk (e x) :=
  rfl

/-- **Closing a cyclic subgroup does not change its double cosets
against a closed finite-index subgroup** — the density/open-subgroup
step passing from the algebraic powers of a Frobenius to its closed
procyclic subgroup ([Yamaguchi 2026,
`DoubleCosetOrbitGeometry.lean:284`][Yamaguchi2026]). -/
theorem doubleCoset_closedCyclic_eq
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (H : Subgroup Q) [H.FiniteIndex] (hHclosed : IsClosed (H : Set Q))
    (g x y : Q) :
    DoubleCoset.mk H (Subgroup.zpowers g) x =
        DoubleCoset.mk H (Subgroup.zpowers g) y ↔
      DoubleCoset.mk H
          (closedSubgroupGenerated ({g} : Set Q)).toSubgroup x =
        DoubleCoset.mk H
          (closedSubgroupGenerated ({g} : Set Q)).toSubgroup y := by
  let C := (closedSubgroupGenerated ({g} : Set Q)).toSubgroup
  have hzC : Subgroup.zpowers g ≤ C := by
    rw [Subgroup.zpowers_eq_closure]
    exact Subgroup.le_topologicalClosure _
  constructor
  · intro hxy
    rw [DoubleCoset.eq] at hxy ⊢
    obtain ⟨h, hh, s, hs, hsxy⟩ := hxy
    exact ⟨h, hh, s, hzC hs, hsxy⟩
  · intro hxy
    rw [DoubleCoset.eq] at hxy ⊢
    obtain ⟨h, hh, c, hc, rfl⟩ := hxy
    have hcclosure : c ∈ closure
        ((Subgroup.zpowers g : Subgroup Q) : Set Q) := by
      rw [Subgroup.zpowers_eq_closure]
      rw [← Subgroup.topologicalClosure_coe]
      change c ∈
        ((Subgroup.closure ({g} : Set Q)).topologicalClosure : Set Q) at hc
      exact hc
    let U : Set Q :=
      (fun s : Q => x * c * s⁻¹ * x⁻¹) ⁻¹' (H : Set Q)
    have hUopen : IsOpen U := by
      apply (((continuous_const.mul continuous_inv).mul
        continuous_const).isOpen_preimage (H : Set Q))
      exact H.isOpen_of_isClosed_of_finiteIndex hHclosed
    have hcU : c ∈ U := by
      change x * c * c⁻¹ * x⁻¹ ∈ H
      simp [mul_assoc]
    obtain ⟨s, hsU, hs⟩ :=
      (mem_closure_iff.mp hcclosure U hUopen hcU)
    have hsH : x * c * s⁻¹ * x⁻¹ ∈ H := hsU
    refine ⟨h * (x * c * s⁻¹ * x⁻¹), H.mul_mem hh hsH,
      s, hs, ?_⟩
    simp [mul_assoc]

/-- **The double-coset equivalence induced by the density argument**
([Yamaguchi 2026, `DoubleCosetOrbitGeometry.lean:330`][Yamaguchi2026]). -/
noncomputable def doubleCosetClosedCyclicEquiv
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (H : Subgroup Q) [H.FiniteIndex] (hHclosed : IsClosed (H : Set Q))
    (g : Q) :
    DoubleCoset.Quotient (H : Set Q) (Subgroup.zpowers g : Set Q) ≃
      DoubleCoset.Quotient (H : Set Q)
        ((closedSubgroupGenerated ({g} : Set Q)).toSubgroup : Set Q) where
  toFun z := Quotient.liftOn' z
    (fun x => DoubleCoset.mk H
      (closedSubgroupGenerated ({g} : Set Q)).toSubgroup x)
    (fun x y hxy =>
      (doubleCoset_closedCyclic_eq H hHclosed g x y).mp
        (Quotient.sound' hxy))
  invFun z := Quotient.liftOn' z
    (fun x => DoubleCoset.mk H (Subgroup.zpowers g) x)
    (fun x y hxy =>
      (doubleCoset_closedCyclic_eq H hHclosed g x y).mpr
        (Quotient.sound' hxy))
  left_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    rfl
  right_inv z := by
    refine Quotient.inductionOn' z ?_
    intro x
    rfl

/-- **Replacing the powers of a Frobenius by their closure is an
equivalence of orbit sets** whenever the subgroup on the other side is
closed of finite index ([Yamaguchi 2026,
`DoubleCosetOrbitGeometry.lean:360`][Yamaguchi2026]). -/
noncomputable def orbitQuotientClosedCyclicEquiv
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (H : Subgroup Q) [H.FiniteIndex] (hHclosed : IsClosed (H : Set Q))
    (g : Q) :
    Quotient (orbitRel H (Q ⧸ Subgroup.zpowers g)) ≃
      Quotient (orbitRel H
        (Q ⧸ (closedSubgroupGenerated ({g} : Set Q)).toSubgroup)) :=
  (orbitQuotientEquivDoubleCoset H (Subgroup.zpowers g)).trans
    ((doubleCosetClosedCyclicEquiv H hHclosed g).trans
      (orbitQuotientEquivDoubleCoset H
        (closedSubgroupGenerated ({g} : Set Q)).toSubgroup).symm)

/-- **Passing to the closure preserves the orbit represented by every
literal group element** ([Yamaguchi 2026,
`DoubleCosetOrbitGeometry.lean:375`][Yamaguchi2026]). -/
@[simp]
theorem orbitQuotientClosedCyclicEquiv_mk
    {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (H : Subgroup Q) [H.FiniteIndex] (hHclosed : IsClosed (H : Set Q))
    (g x : Q) :
    orbitQuotientClosedCyclicEquiv H hHclosed g
        (Quotient.mk'' (QuotientGroup.mk x : Q ⧸ Subgroup.zpowers g)) =
      Quotient.mk'' (QuotientGroup.mk x :
        Q ⧸ (closedSubgroupGenerated ({g} : Set Q)).toSubgroup) := by
  let C := (closedSubgroupGenerated ({g} : Set Q)).toSubgroup
  change (orbitQuotientEquivDoubleCoset H C).symm
      (doubleCosetClosedCyclicEquiv H hHclosed g
        (orbitQuotientEquivDoubleCoset H (Subgroup.zpowers g)
          (Quotient.mk''
            (QuotientGroup.mk x : Q ⧸ Subgroup.zpowers g)))) = _
  unfold orbitQuotientEquivDoubleCoset doubleCosetClosedCyclicEquiv
  simp only [Equiv.coe_fn_mk, Quotient.liftOn'_mk'', Equiv.coe_fn_symm_mk]
  let a := Quotient.out (QuotientGroup.mk x : Q ⧸ Subgroup.zpowers g)
  have ha : a⁻¹ * x ∈ Subgroup.zpowers g :=
    QuotientGroup.leftRel_apply.mp
      (Quotient.exact' (Quotient.out_eq'
        (QuotientGroup.mk x : Q ⧸ Subgroup.zpowers g)))
  have haC : a⁻¹ * x ∈ C := by
    apply Subgroup.le_topologicalClosure _
    simpa [Subgroup.zpowers_eq_closure] using ha
  apply congrArg Quotient.mk''
  apply QuotientGroup.eq.mpr
  exact haC

end

end Atlas.Knowledge
