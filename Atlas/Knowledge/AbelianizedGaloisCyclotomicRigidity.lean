import Mathlib
import Atlas.Knowledge.CycloField

/-!
# cyclotomic rigidity in the abelianized Galois group

Two elements of the abelianized absolute Galois group agree if membership in open subgroups
for the first implies membership for the second and both act on roots of unity by the same
power greater than one. Cyclotomic floors calibrate the exponent in their procyclic closure.

## Main statements

* `abelianizedGalois_eq_of_cyclotomic` — one-sided subgroup containment and a common power
  action determine an element of the topological abelianization.

## Implementation notes

This isolates the group-theoretic argument from `Atlas.Knowledge.IsLocalReciprocity.unique`.
The power need not be the residue cardinality of the base field; for a norm from an extension
it is the extension's residue cardinality. Only characteristic zero enters here.
-/

namespace Atlas.Knowledge

variable (K : Type*) [Field K] [CharZero K]

/- Every neighborhood of the identity in the abelianized absolute Galois group contains an
open subgroup: the Krull basis of the Galois group pushes forward along the open quotient
map. -/
omit [CharZero K] in
private theorem exists_openSubgroup_subset
    {S : Set (Field.absoluteGaloisGroupAbelianization K)} (hS : S ∈ nhds 1) :
    ∃ V : Subgroup (Field.absoluteGaloisGroupAbelianization K),
      IsOpen (V : Set (Field.absoluteGaloisGroupAbelianization K)) ∧ (V : Set _) ⊆ S := by
  have hpre : QuotientGroup.mk ⁻¹' S ∈ nhds (1 : Field.absoluteGaloisGroup K) :=
    (continuous_quot_mk.continuousAt).preimage_mem_nhds hS
  obtain ⟨E, hEfin, hEsub⟩ :=
    (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K) _).mp hpre
  haveI := hEfin
  refine ⟨Subgroup.map (QuotientGroup.mk' _) E.fixingSubgroup, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact QuotientGroup.isOpenMap_coe _ (IntermediateField.fixingSubgroup_isOpen E)
  · rintro x hx
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hx
    exact hEsub hσ

/- An element of the abelianization lying in every open subgroup is the identity: the
identity is closed, so a distinct point is separated from it by a basic open subgroup. -/
omit [CharZero K] in
private theorem eq_one_of_forall_mem_openSubgroup
    {x : Field.absoluteGaloisGroupAbelianization K}
    (hx : ∀ V : Subgroup (Field.absoluteGaloisGroupAbelianization K),
      IsOpen (V : Set (Field.absoluteGaloisGroupAbelianization K)) → x ∈ V) : x = 1 := by
  by_contra hne
  have h1 : IsClosed ({1} : Set (Field.absoluteGaloisGroupAbelianization K)) := by
    rw [← QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.isClosed_preimage]
    have : QuotientGroup.mk ⁻¹' ({1} : Set (Field.absoluteGaloisGroupAbelianization K)) =
        ((commutator (Field.absoluteGaloisGroup K)).topologicalClosure :
          Set (Field.absoluteGaloisGroup K)) := by
      ext σ
      simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
      exact QuotientGroup.eq_one_iff σ
    rw [this]
    exact Subgroup.isClosed_topologicalClosure _
  have hxc : IsClosed ({x} : Set (Field.absoluteGaloisGroupAbelianization K)) := by
    have : ({x} : Set (Field.absoluteGaloisGroupAbelianization K)) =
        (fun y => x⁻¹ * y) ⁻¹' {1} := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage, inv_mul_eq_one]
      exact eq_comm
    rw [this]
    exact h1.preimage (continuous_const.mul continuous_id)
  obtain ⟨V, hVopen, hVsub⟩ := exists_openSubgroup_subset K
    (hxc.isOpen_compl.mem_nhds (by simpa using (Ne.symm hne)))
  exact hVsub (hx V hVopen) rfl

/- Two elements lying in the same open subgroups lie in each other's procyclic closures:
the closure of the powers is the intersection of the open subgroups above them. -/
omit [CharZero K] in
private theorem mem_topologicalClosure_zpowers
    {g h : Field.absoluteGaloisGroupAbelianization K}
    (hgh : ∀ V : Subgroup (Field.absoluteGaloisGroupAbelianization K),
      IsOpen (V : Set (Field.absoluteGaloisGroupAbelianization K)) → (g ∈ V → h ∈ V)) :
    h ∈ (Subgroup.zpowers g).topologicalClosure := by
  by_contra hnot
  have hmem : ((Subgroup.zpowers g).topologicalClosure :
      Set (Field.absoluteGaloisGroupAbelianization K))ᶜ ∈ nhds h :=
    (Subgroup.isClosed_topologicalClosure _).isOpen_compl.mem_nhds hnot
  rw [← map_mul_left_nhds_one h, Filter.mem_map] at hmem
  obtain ⟨V, hVopen, hVsub⟩ := exists_openSubgroup_subset K hmem
  have hWopen : IsOpen (((Subgroup.zpowers g).topologicalClosure ⊔ V :
      Subgroup (Field.absoluteGaloisGroupAbelianization K)) :
        Set (Field.absoluteGaloisGroupAbelianization K)) :=
    Subgroup.isOpen_mono le_sup_right hVopen
  have hhW : h ∈ (Subgroup.zpowers g).topologicalClosure ⊔ V :=
    (hgh _ hWopen)
      (Subgroup.mem_sup_left (Subgroup.le_topologicalClosure _ (Subgroup.mem_zpowers g)))
  obtain ⟨c, hc, v, hv, hcv⟩ := Subgroup.mem_sup.mp hhW
  have hin : h * v⁻¹ ∈ ((Subgroup.zpowers g).topologicalClosure : Set _) := by
    rw [show h * v⁻¹ = c from by rw [← hcv]; group]
    exact hc
  exact hVsub (V.inv_mem hv) hin

/- The closed commutator subgroup restricts trivially to a cyclotomic floor: the floor's
Galois group is commutative and its fixing subgroup is closed. -/
private theorem commutator_closure_le_ker {m : ℕ} (hm : m ≠ 0) :
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure ≤
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K)
        ↥(cycloField K m)).ker := by
  refine Subgroup.topologicalClosure_minimal _ ?_ ?_
  · letI hG : Group (↥(cycloField K m) ≃ₐ[K] ↥(cycloField K m)) := inferInstance
    letI : CommGroup (↥(cycloField K m) ≃ₐ[K] ↥(cycloField K m)) :=
      { hG with mul_comm := cycloField_aut_comm K hm }
    exact Abelianization.commutator_subset_ker _
  · rw [IntermediateField.restrictNormalHom_ker]
    exact IntermediateField.fixingSubgroup_isClosed _

/-- Representatives of the same topological abelianization class agree on roots of unity. -/
theorem abelianizedGalois_eq_on_roots_of_mk_eq
    {σ τ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K}
    (h : (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization K) =
      QuotientGroup.mk τ) {m : ℕ} (hm : m ≠ 0)
    {ζ : AlgebraicClosure K} (hζ : ζ ^ m = 1) : σ ζ = τ ζ := by
  let r := QuotientGroup.lift
    (commutator (Field.absoluteGaloisGroup K)).topologicalClosure
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K) ↥(cycloField K m))
    (commutator_closure_le_ker K hm)
  have hr := congrArg r h
  change AlgEquiv.restrictNormalHom (cycloField K m) σ =
    AlgEquiv.restrictNormalHom (cycloField K m) τ at hr
  let z : cycloField K m := ⟨ζ, mem_cycloField K hm hζ⟩
  exact (AlgEquiv.restrictNormal_commutes σ (cycloField K m) z).symm.trans
    ((congrArg (fun g : cycloField K m ≃ₐ[K] cycloField K m =>
      (g z : AlgebraicClosure K)) hr).trans
      (AlgEquiv.restrictNormal_commutes τ (cycloField K m) z))

/-- Open-subgroup containment and a common power action on roots of unity pin an element
of the topological abelianization. -/
theorem abelianizedGalois_eq_of_cyclotomic
    {a b : Field.absoluteGaloisGroupAbelianization K}
    (hmem : ∀ V : Subgroup (Field.absoluteGaloisGroupAbelianization K),
      IsOpen (V : Set (Field.absoluteGaloisGroupAbelianization K)) → a ∈ V → b ∈ V)
    (q : ℕ) (hq1 : 1 < q)
    (ha : ∀ m : ℕ, Nat.Coprime m q →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
        (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization K) = a →
      ∀ ζ : AlgebraicClosure K, ζ ^ m = 1 → σ ζ = ζ ^ q)
    (hb : ∀ m : ℕ, Nat.Coprime m q →
      ∀ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
        (QuotientGroup.mk σ : Field.absoluteGaloisGroupAbelianization K) = b →
      ∀ ζ : AlgebraicClosure K, ζ ^ m = 1 → σ ζ = ζ ^ q) : a = b := by
  haveI : IsGalois K (AlgebraicClosure K) := ⟨⟩
  haveI : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (CompactSpace (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K))
  have hC : b ∈ (Subgroup.zpowers a).topologicalClosure :=
    mem_topologicalClosure_zpowers K hmem
  -- the discrepancy lies in every open subgroup, hence vanishes
  have hdis : b * a⁻¹ = 1 := by
    apply eq_one_of_forall_mem_openSubgroup K
    intro U hU
    haveI : Finite (Field.absoluteGaloisGroupAbelianization K ⧸ U) :=
      U.quotient_finite_of_isOpen hU
    -- `d`: the order of `a` modulo `U`
    set d := orderOf (QuotientGroup.mk a :
      Field.absoluteGaloisGroupAbelianization K ⧸ U) with hddef
    have hd0 : 0 < d := orderOf_pos _
    have hδd : a ^ d ∈ U := by
      have hpow : (QuotientGroup.mk a :
          Field.absoluteGaloisGroupAbelianization K ⧸ U) ^ d = 1 := pow_orderOf_eq_one _
      rwa [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hpow
    -- the cyclotomic level `q ^ d - 1`
    set m := q ^ d - 1 with hmdef
    have hqd1 : 1 ≤ q ^ d := Nat.one_le_pow _ _ (by omega)
    have hmsucc : m + 1 = q ^ d := by omega
    have hm0 : m ≠ 0 := by
      have : 1 < q ^ d := Nat.one_lt_pow hd0.ne' hq1
      omega
    have hcop : Nat.Coprime m (q) := by
      have h1 : Nat.Coprime m (m + 1) :=
        Nat.coprime_self_add_right.mpr (Nat.coprime_one_right m)
      rw [hmsucc] at h1
      exact Nat.Coprime.coprime_dvd_right (dvd_pow_self _ hd0.ne') h1
    haveI : NeZero m := ⟨hm0⟩
    haveI : NeZero (m : K) := ⟨Nat.cast_ne_zero.mpr hm0⟩
    obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) m
    have hζmem : ζ₀ ∈ cycloField K m := mem_cycloField K hm0 hζ₀.pow_eq_one
    -- the restriction of the abelianization to the cyclotomic floor
    set r := QuotientGroup.lift
      (commutator (Field.absoluteGaloisGroup K)).topologicalClosure
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := AlgebraicClosure K) ↥(cycloField K m))
      (commutator_closure_le_ker K hm0) with hrdef
    obtain ⟨σ, hσ⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨τ, hτ⟩ := QuotientGroup.mk'_surjective _ b
    have hrφ : r a =
        AlgEquiv.restrictNormalHom (F := K) ↥(cycloField K m) σ := by
      rw [← hσ]; rfl
    have hrψ : r b =
        AlgEquiv.restrictNormalHom (F := K) ↥(cycloField K m) τ := by
      rw [← hτ]; rfl
    have hfrobσ := ha m hcop σ hσ
    have hfrobτ := hb m hcop τ hτ
    -- the restricted action on a root of unity is the `q`-power map
    have hact : ∀ ρ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K,
        (∀ ζ : AlgebraicClosure K, ζ ^ m = 1 → ρ ζ = ζ ^ q) →
        ∀ (x : AlgebraicClosure K) (hx : x ∈ cycloField K m), x ^ m = 1 →
        ((AlgEquiv.restrictNormalHom (F := K) ↥(cycloField K m) ρ ⟨x, hx⟩ :
          ↥(cycloField K m)) : AlgebraicClosure K) = x ^ q := by
      intro ρ hρ x hx hxm
      have hcomm := AlgEquiv.restrictNormal_commutes ρ ↥(cycloField K m) ⟨x, hx⟩
      exact hcomm.trans (hρ x hxm)
    have hxroot : ∀ x : AlgebraicClosure K, x ^ m = 1 →
        (x ^ q) ^ m = 1 := by
      intro x hxm
      rw [← pow_mul, Nat.mul_comm, pow_mul, hxm, one_pow]
    -- iterating the restricted action iterates the exponent
    have hiterσ : ∀ (j : ℕ) (x : AlgebraicClosure K) (hx : x ∈ cycloField K m),
        x ^ m = 1 →
        (AlgEquiv.restrictNormalHom (F := K) ↥(cycloField K m) σ ^ j) ⟨x, hx⟩ =
          (⟨x ^ q ^ j, pow_mem hx _⟩ : ↥(cycloField K m)) := by
      intro j
      induction j with
      | zero => intro x hx hxm; exact Subtype.ext (by simp)
      | succ n ih =>
        intro x hx hxm
        have hstep : AlgEquiv.restrictNormalHom (F := K) ↥(cycloField K m) σ ⟨x, hx⟩ =
            (⟨x ^ q, pow_mem hx _⟩ : ↥(cycloField K m)) :=
          Subtype.ext (hact σ hfrobσ x hx hxm)
        rw [pow_succ, AlgEquiv.mul_apply, hstep,
          ih (x ^ q) (pow_mem hx _) (hxroot x hxm)]
        exact Subtype.ext (show (x ^ q) ^ q ^ n =
          x ^ q ^ (n + 1) by rw [← pow_mul, ← pow_succ'])
    -- the restriction of `a` has order exactly `d`
    have hpowd : AlgEquiv.restrictNormalHom (F := K) ↥(cycloField K m) σ ^ d = 1 := by
      apply AlgEquiv.coe_toAlgHom_injective
      refine IntermediateField.algHom_ext_of_eq_adjoin (S := cycloField K m) K rfl ?_
      intro x hx
      have hxm : x ^ m = 1 := cycloField_pow_eq_one_of_mem_rootSet K hx
      simp only [AlgEquiv.coe_toAlgHom]
      rw [hiterσ d x _ hxm]
      refine Subtype.ext ?_
      rw [AlgEquiv.one_apply]
      change x ^ q ^ d = x
      rw [← hmsucc, pow_succ, hxm, one_mul]
    have hord : orderOf (r a) = d := by
      rw [hrφ]
      have hdvd : orderOf
          (AlgEquiv.restrictNormalHom (F := K) ↥(cycloField K m) σ) ∣ d :=
        orderOf_dvd_of_pow_eq_one hpowd
      have hfin : IsOfFinOrder
          (AlgEquiv.restrictNormalHom (F := K) ↥(cycloField K m) σ) :=
        isOfFinOrder_iff_pow_eq_one.mpr ⟨d, hd0, hpowd⟩
      refine Nat.le_antisymm (Nat.le_of_dvd hd0 hdvd) ?_
      set o := orderOf (AlgEquiv.restrictNormalHom (F := K) ↥(cycloField K m) σ)
        with hodef
      have ho0 : 0 < o := hfin.orderOf_pos
      have h1 : (AlgEquiv.restrictNormalHom (F := K) ↥(cycloField K m) σ ^ o)
          ⟨ζ₀, hζmem⟩ = (⟨ζ₀, hζmem⟩ : ↥(cycloField K m)) := by
        rw [hodef, pow_orderOf_eq_one]
        rfl
      rw [hiterσ o ζ₀ hζmem hζ₀.pow_eq_one] at h1
      have h2 : ζ₀ ^ q ^ o = ζ₀ := congrArg Subtype.val h1
      have hqo1 : 1 ≤ q ^ o := Nat.one_le_pow _ _ (by omega)
      have h3 : ζ₀ ^ (q ^ o - 1) = 1 := by
        have hζne : ζ₀ ≠ 0 := hζ₀.ne_zero hm0
        have hsp : q ^ o = q ^ o - 1 + 1 := by omega
        have h4 : ζ₀ ^ (q ^ o - 1) * ζ₀ = 1 * ζ₀ := by
          rw [one_mul, ← pow_succ, ← hsp]
          exact h2
        exact mul_right_cancel₀ hζne h4
      have h5 : m ∣ q ^ o - 1 := hζ₀.dvd_of_pow_eq_one _ h3
      have hqogt : 1 < q ^ o := Nat.one_lt_pow ho0.ne' hq1
      have h6 : m ≤ q ^ o - 1 := Nat.le_of_dvd (by omega) h5
      have h7 : q ^ d ≤ q ^ o := by
        rw [← hmsucc]
        exact (Nat.le_sub_iff_add_le hqo1).mp h6
      exact (Nat.pow_le_pow_iff_right hq1).mp h7
    -- the two restrictions agree: both are the `q`-power map on the generators
    have hreq : r a = r b := by
      rw [hrφ, hrψ]
      apply AlgEquiv.coe_toAlgHom_injective
      refine IntermediateField.algHom_ext_of_eq_adjoin (S := cycloField K m) K rfl ?_
      intro x hx
      have hxm : x ^ m = 1 := cycloField_pow_eq_one_of_mem_rootSet K hx
      simp only [AlgEquiv.coe_toAlgHom]
      exact Subtype.ext
        ((hact σ hfrobσ x _ hxm).trans (hact τ hfrobτ x _ hxm).symm)
    -- the kernel of the restriction is open
    have hkeropen : IsOpen
        (MonoidHom.ker r : Set (Field.absoluteGaloisGroupAbelianization K)) := by
      rw [← QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.isOpen_preimage]
      have hpre : QuotientGroup.mk ⁻¹'
          (MonoidHom.ker r : Set (Field.absoluteGaloisGroupAbelianization K)) =
          ((cycloField K m).fixingSubgroup :
            Set (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K)) := by
        ext g
        simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker]
        have hg : r (QuotientGroup.mk g) =
            AlgEquiv.restrictNormalHom (F := K) ↥(cycloField K m) g := rfl
        rw [hg, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
        exact Iff.rfl
      rw [hpre]
      exact IntermediateField.fixingSubgroup_isOpen _
    -- `b` sits over `a` against the open subgroup `U ⊓ ker r`
    have hVopen : IsOpen ((U ⊓ MonoidHom.ker r :
        Subgroup (Field.absoluteGaloisGroupAbelianization K)) :
          Set (Field.absoluteGaloisGroupAbelianization K)) := by
      rw [Subgroup.coe_inf]
      exact hU.inter hkeropen
    have hψW : b ∈ Subgroup.zpowers a ⊔ (U ⊓ MonoidHom.ker r) := by
      refine Subgroup.topologicalClosure_minimal _ le_sup_left
        (Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono le_sup_right hVopen)) hC
    obtain ⟨c, hc, v, hv, hcv⟩ := Subgroup.mem_sup.mp hψW
    obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp hc
    have hrv : r v = 1 := MonoidHom.mem_ker.mp (Subgroup.mem_inf.mp hv).2
    -- the exponent discrepancy is a multiple of `d`
    have haz : r a ^ z = r a := by
      calc r a ^ z = r (a ^ z) := (map_zpow r _ z).symm
        _ = r (a ^ z * v) := by rw [map_mul, hrv, mul_one]
        _ = r b := by rw [hz, hcv]
        _ = r a := hreq.symm
    have hdvd : (d : ℤ) ∣ z - 1 := by
      have h1 : r a ^ (z - 1) = 1 := by
        rw [zpow_sub, haz, zpow_one]
        exact mul_inv_cancel _
      have h2 : ((orderOf (r a)) : ℤ) ∣ z - 1 :=
        orderOf_dvd_iff_zpow_eq_one.mpr h1
      rwa [hord] at h2
    -- assemble the discrepancy inside `U`
    have hsplit : b * a⁻¹ = a ^ (z - 1 : ℤ) * v := by
      rw [← hcv, ← hz, mul_right_comm, zpow_sub, zpow_one]
    rw [hsplit]
    refine U.mul_mem ?_ (Subgroup.mem_inf.mp hv).1
    obtain ⟨w', hw'⟩ := hdvd
    rw [hw', zpow_mul, zpow_natCast]
    exact U.zpow_mem hδd w'
  have := mul_inv_eq_one.mp hdis
  exact this.symm

end Atlas.Knowledge
