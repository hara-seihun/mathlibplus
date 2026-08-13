import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- An explicit two-relation simultaneous Cayley transporter defect in `A₄`.
The two relation symbols are `Set`s; finite carriers are used only to make the
witness and its finite checks computational. -/
def alternatingFourTwoRelationSimultaneousDefect : Prop :=
  let A4 := alternatingGroup (Fin 4)
  let p234 : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3
  let p243 : Equiv.Perm (Fin 4) := Equiv.swap 1 3 * Equiv.swap 2 3
  let p12_34 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
  let p123 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
  let p124 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 3
  let p132 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 2
  let p134 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 2 3
  let p13_24 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
  let p142 : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 3
  let p143 : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 2 3
  let p14_23 : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2
  let even : ∀ p : Equiv.Perm (Fin 4), Equiv.Perm.sign p = 1 → A4 :=
    fun p hp => ⟨p, Equiv.Perm.mem_alternatingGroup.mpr hp⟩
  let a4Index : Fin 12 → A4 := ![
    even 1 (by native_decide),
    even p234 (by native_decide),
    even p243 (by native_decide),
    even p12_34 (by native_decide),
    even p123 (by native_decide),
    even p124 (by native_decide),
    even p132 (by native_decide),
    even p134 (by native_decide),
    even p13_24 (by native_decide),
    even p142 (by native_decide),
    even p143 (by native_decide),
    even p14_23 (by native_decide)
  ]
  let a4Idx : A4 → Fin 12 := fun x =>
    if x = a4Index 0 then 0 else
    if x = a4Index 1 then 1 else
    if x = a4Index 2 then 2 else
    if x = a4Index 3 then 3 else
    if x = a4Index 4 then 4 else
    if x = a4Index 5 then 5 else
    if x = a4Index 6 then 6 else
    if x = a4Index 7 then 7 else
    if x = a4Index 8 then 8 else
    if x = a4Index 9 then 9 else
    if x = a4Index 10 then 10 else 11
  let a4Equiv : Fin 12 ≃ A4 := {
    toFun := a4Index
    invFun := a4Idx
    left_inv := by native_decide
    right_inv := by native_decide
  }
  let qIndex : Fin 12 → Fin 12 := ![0, 5, 7, 8, 4, 1, 6, 2, 3, 9, 10, 11]
  let qIndexEquiv : Fin 12 ≃ Fin 12 := {
    toFun := qIndex
    invFun := qIndex
    left_inv := by native_decide
    right_inv := by native_decide
  }
  let q : A4 ≃ A4 := (a4Equiv.symm.trans qIndexEquiv).trans a4Equiv
  let indexSet : Finset (Fin 12) → Finset A4 := fun s => s.image a4Index
  let Sfin : Fin 2 → Finset A4 := ![indexSet {3}, indexSet {2, 4, 7, 8, 9}]
  let Tfin : Fin 2 → Finset A4 := ![indexSet {8}, indexSet {2, 3, 4, 7, 9}]
  let S : Fin 2 → Set A4 := fun i => (Sfin i : Set A4)
  let T : Fin 2 → Set A4 := fun i => (Tfin i : Set A4)
  q (1 : A4) = 1 ∧
    (∀ x : A4, q (q x) = x) ∧
    (∀ i : Fin 2, (S i).ncard = if i = 0 then 1 else 5) ∧
    (∀ i : Fin 2, (T i).ncard = if i = 0 then 1 else 5) ∧
    (∀ x : A4, ¬ (x ∈ S 0 ∧ x ∈ S 1)) ∧
    (∀ x : A4, ¬ (x ∈ T 0 ∧ x ∈ T 1)) ∧
    (∀ i : Fin 2, 1 ∉ S i ∧ 1 ∉ T i) ∧
    (∀ i : Fin 2, ∀ y : A4,
      y ∈ T i ↔ ∃ x : A4, x ∈ S i ∧ q x = y) ∧
    (∀ i : Fin 2, ∀ x y : A4,
      x⁻¹ * y ∈ S i ↔ (q x)⁻¹ * q y ∈ T i) ∧
    (∀ i : Fin 2, ∃ φ : A4 ≃* A4, ∀ y : A4,
      y ∈ T i ↔ ∃ x : A4, x ∈ S i ∧ φ x = y) ∧
    ¬ ∃ φ : A4 ≃* A4, ∀ i : Fin 2, ∀ y : A4,
      y ∈ T i ↔ ∃ x : A4, x ∈ S i ∧ φ x = y

end MathlibPlus.Open.GraphTheory
namespace MathlibPlus.Open.GraphTheory

theorem alternatingFourTwoRelationSimultaneousDefect_witness :
    alternatingFourTwoRelationSimultaneousDefect := by
  unfold alternatingFourTwoRelationSimultaneousDefect
  let A4 := alternatingGroup (Fin 4)
  let p234 : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3
  let p243 : Equiv.Perm (Fin 4) := Equiv.swap 1 3 * Equiv.swap 2 3
  let p12_34 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
  let p123 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 2
  let p124 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 3
  let p132 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 2
  let p134 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 2 3
  let p13_24 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
  let p142 : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 3
  let p143 : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 2 3
  let p14_23 : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2
  let even : ∀ p : Equiv.Perm (Fin 4), Equiv.Perm.sign p = 1 → A4 :=
    fun p hp => ⟨p, Equiv.Perm.mem_alternatingGroup.mpr hp⟩
  let a4Index : Fin 12 → A4 := ![
    even 1 (by native_decide), even p234 (by native_decide),
    even p243 (by native_decide), even p12_34 (by native_decide),
    even p123 (by native_decide), even p124 (by native_decide),
    even p132 (by native_decide), even p134 (by native_decide),
    even p13_24 (by native_decide), even p142 (by native_decide),
    even p143 (by native_decide), even p14_23 (by native_decide)]
  let a4Idx : A4 → Fin 12 := fun x =>
    if x = a4Index 0 then 0 else
    if x = a4Index 1 then 1 else
    if x = a4Index 2 then 2 else
    if x = a4Index 3 then 3 else
    if x = a4Index 4 then 4 else
    if x = a4Index 5 then 5 else
    if x = a4Index 6 then 6 else
    if x = a4Index 7 then 7 else
    if x = a4Index 8 then 8 else
    if x = a4Index 9 then 9 else
    if x = a4Index 10 then 10 else 11
  let a4Equiv : Fin 12 ≃ A4 := {
    toFun := a4Index, invFun := a4Idx,
    left_inv := by native_decide, right_inv := by native_decide }
  let qIndex : Fin 12 → Fin 12 := ![0, 5, 7, 8, 4, 1, 6, 2, 3, 9, 10, 11]
  let qIndexEquiv : Fin 12 ≃ Fin 12 := {
    toFun := qIndex, invFun := qIndex,
    left_inv := by native_decide, right_inv := by native_decide }
  let q : A4 ≃ A4 := (a4Equiv.symm.trans qIndexEquiv).trans a4Equiv
  let indexSet : Finset (Fin 12) → Finset A4 := fun s => s.image a4Index
  let Sfin : Fin 2 → Finset A4 := ![indexSet {3}, indexSet {2, 4, 7, 8, 9}]
  let Tfin : Fin 2 → Finset A4 := ![indexSet {8}, indexSet {2, 3, 4, 7, 9}]
  let S : Fin 2 → Set A4 := fun i => (Sfin i : Set A4)
  let T : Fin 2 → Set A4 := fun i => (Tfin i : Set A4)
  change q (1 : A4) = 1 ∧
    (∀ x : A4, q (q x) = x) ∧
    (∀ i : Fin 2, (S i).ncard = if i = 0 then 1 else 5) ∧
    (∀ i : Fin 2, (T i).ncard = if i = 0 then 1 else 5) ∧
    (∀ x : A4, ¬ (x ∈ S 0 ∧ x ∈ S 1)) ∧
    (∀ x : A4, ¬ (x ∈ T 0 ∧ x ∈ T 1)) ∧
    (∀ i : Fin 2, 1 ∉ S i ∧ 1 ∉ T i) ∧
    (∀ i : Fin 2, ∀ y : A4,
      y ∈ T i ↔ ∃ x : A4, x ∈ S i ∧ q x = y) ∧
    (∀ i : Fin 2, ∀ x y : A4,
      x⁻¹ * y ∈ S i ↔ (q x)⁻¹ * q y ∈ T i) ∧
    (∀ i : Fin 2, ∃ φ : A4 ≃* A4, ∀ y : A4,
      y ∈ T i ↔ ∃ x : A4, x ∈ S i ∧ φ x = y) ∧
    ¬ ∃ φ : A4 ≃* A4, ∀ i : Fin 2, ∀ y : A4,
      y ∈ T i ↔ ∃ x : A4, x ∈ S i ∧ φ x = y
  have hqone : q (1 : A4) = 1 := by native_decide
  have hqinvol : ∀ x : A4, q (q x) = x := by native_decide
  have hscard : ∀ i : Fin 2, (S i).ncard = if i = 0 then 1 else 5 := by
    intro i
    fin_cases i
    · change (Sfin 0 : Set A4).ncard = 1
      rw [Set.ncard_coe_finset]
      native_decide
    · change (Sfin 1 : Set A4).ncard = 5
      rw [Set.ncard_coe_finset]
      native_decide
  have htcard : ∀ i : Fin 2, (T i).ncard = if i = 0 then 1 else 5 := by
    intro i
    fin_cases i
    · change (Tfin 0 : Set A4).ncard = 1
      rw [Set.ncard_coe_finset]
      native_decide
    · change (Tfin 1 : Set A4).ncard = 5
      rw [Set.ncard_coe_finset]
      native_decide
  have hdisjS : ∀ x : A4, ¬ (x ∈ S 0 ∧ x ∈ S 1) := by
    change ∀ x : A4, ¬ (x ∈ Sfin 0 ∧ x ∈ Sfin 1)
    native_decide
  have hdisjT : ∀ x : A4, ¬ (x ∈ T 0 ∧ x ∈ T 1) := by
    change ∀ x : A4, ¬ (x ∈ Tfin 0 ∧ x ∈ Tfin 1)
    native_decide
  have hfree : ∀ i : Fin 2, 1 ∉ S i ∧ 1 ∉ T i := by
    change ∀ i : Fin 2, 1 ∉ Sfin i ∧ 1 ∉ Tfin i
    native_decide
  have hqimage : ∀ i : Fin 2, ∀ y : A4,
      y ∈ T i ↔ ∃ x : A4, x ∈ S i ∧ q x = y := by
    change ∀ i : Fin 2, ∀ y : A4,
      y ∈ Tfin i ↔ ∃ x : A4, x ∈ Sfin i ∧ q x = y
    native_decide
  have hrel : ∀ i : Fin 2, ∀ x y : A4,
      x⁻¹ * y ∈ S i ↔ (q x)⁻¹ * q y ∈ T i := by
    change ∀ i : Fin 2, ∀ x y : A4,
      x⁻¹ * y ∈ Sfin i ↔ (q x)⁻¹ * q y ∈ Tfin i
    native_decide
  have htransport : ∀ i : Fin 2, ∃ φ : A4 ≃* A4, ∀ y : A4,
      y ∈ T i ↔ ∃ x : A4, x ∈ S i ∧ φ x = y := by
    intro i
    fin_cases i
    · refine ⟨MulAut.conj (a4Index 1), ?_⟩
      change ∀ y : A4, y ∈ Tfin 0 ↔
        ∃ x : A4, x ∈ Sfin 0 ∧ (MulAut.conj (a4Index 1)) x = y
      native_decide
    · refine ⟨MulAut.conj (a4Index 2), ?_⟩
      change ∀ y : A4, y ∈ Tfin 1 ↔
        ∃ x : A4, x ∈ Sfin 1 ∧ (MulAut.conj (a4Index 2)) x = y
      native_decide
  have hno : ¬ ∃ φ : A4 ≃* A4, ∀ i : Fin 2, ∀ y : A4,
      y ∈ T i ↔ ∃ x : A4, x ∈ S i ∧ φ x = y := by
    rintro ⟨φ, h⟩
    have h0 := h 0
    have h1 := h 1
    let b : A4 := a4Index 3
    let c : A4 := a4Index 8
    have hb : Sfin 0 = {b} := by native_decide
    have hc : Tfin 0 = {c} := by native_decide
    have hbmem : b ∈ S 0 := by
      change b ∈ Sfin 0
      native_decide
    have hbc : φ b = c := by
      have hmem : φ b ∈ T 0 := (h0 (φ b)).2 ⟨b, hbmem, rfl⟩
      change φ b ∈ Tfin 0 at hmem
      rw [hc] at hmem
      simpa using hmem
    let P : A4 → Prop := fun x => x * b * x⁻¹ ∈ Sfin 1
    let Q : A4 → Prop := fun y => y * c * y⁻¹ ∈ Tfin 1
    have hs : ((Sfin 1).filter P).card = 0 := by native_decide
    have ht : ((Tfin 1).filter Q).card = 4 := by native_decide
    have himage : Finset.image φ ((Sfin 1).filter P) = (Tfin 1).filter Q := by
      ext y
      constructor
      · intro hy
        rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
        have hxS : x ∈ Sfin 1 := (Finset.mem_filter.mp hx).1
        have hxP : P x := (Finset.mem_filter.mp hx).2
        have hxSset : x ∈ S 1 := hxS
        have hyTset : φ x ∈ T 1 := (h1 (φ x)).2 ⟨x, hxSset, rfl⟩
        have hyT : φ x ∈ Tfin 1 := hyTset
        have hyQ : Q (φ x) := by
          have hmemset : φ (x * b * x⁻¹) ∈ T 1 :=
            (h1 (φ (x * b * x⁻¹))).2 ⟨x * b * x⁻¹, hxP, rfl⟩
          have hmem : φ (x * b * x⁻¹) ∈ Tfin 1 := hmemset
          simpa [Q, P, hbc, map_mul] using hmem
        exact Finset.mem_filter.mpr ⟨hyT, hyQ⟩
      · intro hy
        have hyT : y ∈ Tfin 1 := (Finset.mem_filter.mp hy).1
        have hyQ : Q y := (Finset.mem_filter.mp hy).2
        have hyTset : y ∈ T 1 := hyT
        have hyimageSet := (h1 y).1 hyTset
        rcases hyimageSet with ⟨x, hxSset, hxy⟩
        have hxS : x ∈ Sfin 1 := hxSset
        have hxP : P x := by
          have hmem : φ (x * b * x⁻¹) ∈ Tfin 1 := by
            simpa [Q, hbc, map_mul, hxy] using hyQ
          have hmemset : φ (x * b * x⁻¹) ∈ T 1 := hmem
          have himemSet := (h1 (φ (x * b * x⁻¹))).1 hmemset
          rcases himemSet with ⟨z, hzSset, hzeq⟩
          have hz : z ∈ Sfin 1 := hzSset
          have hzx : z = x * b * x⁻¹ := φ.injective hzeq
          simpa [P, hzx] using hz
        exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxS, hxP⟩, hxy⟩
    have hcard : ((Sfin 1).filter P).card = ((Tfin 1).filter Q).card := by
      rw [← himage]
      exact (Finset.card_image_of_injective _ φ.injective).symm
    omega
  exact ⟨hqone, hqinvol, hscard, htcard, hdisjS, hdisjT, hfree,
    hqimage, hrel, htransport, hno⟩

end MathlibPlus.Open.GraphTheory
