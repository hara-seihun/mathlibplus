import MathlibPlus.Open.GraphTheory.CyclicEightUndirectedRelationalCI

namespace MathlibPlus.GraphTheory

private abbrev eFin : Fin 8 ≃+* ZMod 8 := ZMod.finEquiv 8
private def unit (u : Fin 4) : Fin 8 := ![1, 3, 5, 7] u
private def zunit : Fin 4 → (ZMod 8)ˣ :=
  ![Units.mkOfMulEqOne 1 1 (by native_decide),
    Units.mkOfMulEqOne 3 3 (by native_decide),
    Units.mkOfMulEqOne 5 5 (by native_decide),
    Units.mkOfMulEqOne 7 7 (by native_decide)]
private def alpha (u : Fin 4) : ZMod 8 ≃+ ZMod 8 :=
  (Units.mulLeftLinearEquiv ℤ (ZMod 8) (zunit u)).toAddEquiv
private abbrev atomBit (m : Fin 16) (k : Fin 4) : Bool :=
  decide ((m.val / 2 ^ k.val) % 2 = 1)
private abbrev mask (m : Fin 16) (x : Fin 8) : Bool :=
  if x = 0 then false
  else if x = 1 ∨ x = 7 then atomBit m 0
  else if x = 2 ∨ x = 6 then atomBit m 1
  else if x = 3 ∨ x = 5 then atomBit m 2
  else atomBit m 3
private noncomputable def maskOf (A : Set (ZMod 8)) : Fin 16 := by
  classical
  exact ⟨(if eFin 1 ∈ A then 1 else 0) +
    (if eFin 2 ∈ A then 2 else 0) +
    (if eFin 3 ∈ A then 4 else 0) +
    (if eFin 4 ∈ A then 8 else 0), by split_ifs <;> omega⟩
private abbrev image (q : Fin 8 ≃ Fin 8) (m : Fin 16) (z : Fin 8) : Bool :=
  mask m (q.symm z)
private abbrev relation (q : Fin 8 ≃ Fin 8) (m : Fin 16) : Prop :=
  ∀ x y, mask m (y - x) = image q m (q y - q x)
private theorem finiteCore :
    ∀ q : Fin 8 ≃ Fin 8, q 0 = 0 →
      ∃ u : Fin 4, ∀ m : Fin 16,
        relation q m → ∀ x, mask m x = image q m (unit u * x) := by
  native_decide

private theorem mask_bits :
    ∀ b1 b2 b3 b4 : Bool, ∀ x : Fin 8,
      (if x = 0 then false
       else if x = 1 ∨ x = 7 then b1
       else if x = 2 ∨ x = 6 then b2
       else if x = 3 ∨ x = 5 then b3
       else b4) =
      mask ⟨(if b1 then 1 else 0) + (if b2 then 2 else 0) +
        (if b3 then 4 else 0) + (if b4 then 8 else 0), by
          split_ifs <;> omega⟩ x := by
  native_decide

private lemma maskOf_rep (A : Set (ZMod 8))
    (h0 : (0 : ZMod 8) ∉ A)
    (hinv : ∀ x, x ∈ A ↔ -x ∈ A) :
    ∀ x : Fin 8, (eFin x ∈ A) = mask (maskOf A) x := by
  classical
  intro x
  have he0 : eFin 0 = 0 := by native_decide
  have he1 : eFin 1 = 1 := by native_decide
  have he2 : eFin 2 = 2 := by native_decide
  have he3 : eFin 3 = 3 := by native_decide
  have he4 : eFin 4 = 4 := by native_decide
  have he5 : eFin 5 = 5 := by native_decide
  have he6 : eFin 6 = 6 := by native_decide
  have he7 : eFin 7 = 7 := by native_decide
  have hi3 : eFin 5 ∈ A ↔ eFin 3 ∈ A := by
    rw [show eFin 5 = -(eFin 3) by native_decide]
    exact (hinv (eFin 3)).symm
  have hi2 : eFin 6 ∈ A ↔ eFin 2 ∈ A := by
    rw [show eFin 6 = -(eFin 2) by native_decide]
    exact (hinv (eFin 2)).symm
  have hi1 : eFin 7 ∈ A ↔ eFin 1 ∈ A := by
    rw [show eFin 7 = -(eFin 1) by native_decide]
    exact (hinv (eFin 1)).symm
  let b1 : Bool := if eFin 1 ∈ A then true else false
  let b2 : Bool := if eFin 2 ∈ A then true else false
  let b3 : Bool := if eFin 3 ∈ A then true else false
  let b4 : Bool := if eFin 4 ∈ A then true else false
  have hi3' : (5 : ZMod 8) ∈ A ↔ (3 : ZMod 8) ∈ A := by
    simpa [he5, he3] using hi3
  have hi2' : (6 : ZMod 8) ∈ A ↔ (2 : ZMod 8) ∈ A := by
    simpa [he6, he2] using hi2
  have hi1' : (7 : ZMod 8) ∈ A ↔ (1 : ZMod 8) ∈ A := by
    simpa [he7, he1] using hi1
  have hb : maskOf A =
      ⟨(if b1 then 1 else 0) + (if b2 then 2 else 0) +
        (if b3 then 4 else 0) + (if b4 then 8 else 0), by
          split_ifs <;> omega⟩ := by
    apply Fin.ext
    simp [maskOf, b1, b2, b3, b4]
  have hp :
      (if eFin x ∈ A then true else false) =
        (if x = 0 then false
         else if x = 1 ∨ x = 7 then b1
         else if x = 2 ∨ x = 6 then b2
         else if x = 3 ∨ x = 5 then b3
         else b4) := by
    fin_cases x <;> simp [b1, b2, b3, b4, he0, he1, he2, he3, he4, he5,
      he6, he7, h0, hi1', hi2', hi3']
  rw [hb]
  have hxbool := hp.trans (mask_bits b1 b2 b3 b4 x)
  apply propext
  rw [← hxbool]
  simp

theorem cyclicEightUndirectedRelationalCI_proved :
    MathlibPlus.Open.GraphTheory.cyclicEightUndirectedRelationalCI := by
  intro ι S T e hS0 hT0 hSinv hTinv hrel
  let q : ZMod 8 ≃ ZMod 8 := e.trans (Equiv.subRight (e 0))
  let ef : Fin 8 ≃+* ZMod 8 := eFin
  let qf : Fin 8 ≃ Fin 8 :=
    (ef : Fin 8 ≃ ZMod 8).trans (q.trans (ef.symm : ZMod 8 ≃ Fin 8))
  have hq0 : q 0 = 0 := by
    simp [q]
  have hqf0 : qf 0 = 0 := by
    simp [qf, q, ef]
  have hq_conj (x : Fin 8) : eFin (qf x) = q (eFin x) := by
    rfl
  have hq_diff (x y : ZMod 8) : q y - q x = e y - e x := by
    simp [q]
  have hmaskS (i : ι) (x : Fin 8) :
      eFin x ∈ S i ↔ mask (maskOf (S i)) x = true := by
    exact eq_iff_iff.mp (maskOf_rep (S i) (hS0 i) (fun z => (hSinv i z).symm) x)
  have hinc0 (i : ι) (x : ZMod 8) :
      x ∈ S i ↔ q x ∈ T i := by
    simpa [q] using (hrel i 0 x)
  have hTmask (i : ι) (z : Fin 8) :
      eFin z ∈ T i ↔ mask (maskOf (S i)) (qf.symm z) = true := by
    have hqpre : q (eFin (qf.symm z)) = eFin z := by
      rw [← hq_conj (qf.symm z)]
      simp
    have hi :
        eFin (qf.symm z) ∈ S i ↔ eFin z ∈ T i := by
      calc
        eFin (qf.symm z) ∈ S i ↔ q (eFin (qf.symm z)) ∈ T i := hinc0 i _
        _ ↔ eFin z ∈ T i := by rw [hqpre]
    exact hi.symm.trans (hmaskS i (qf.symm z))
  have hrelFin (i : ι) (x y : Fin 8) :
      mask (maskOf (S i)) (y - x) =
        image qf (maskOf (S i)) (qf y - qf x) := by
    have hz (x y : Fin 8) :
        eFin (qf y - qf x) = e (eFin y) - e (eFin x) := by
      calc
        eFin (qf y - qf x) = eFin (qf y) - eFin (qf x) := map_sub eFin _ _
        _ = q (eFin y) - q (eFin x) := by rw [hq_conj, hq_conj]
        _ = e (eFin y) - e (eFin x) := hq_diff _ _
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hs
      have hs' : eFin (y - x) ∈ S i := (hmaskS i (y - x)).mpr hs
      have ht : e (eFin y) - e (eFin x) ∈ T i :=
        (hrel i (eFin x) (eFin y)).mp (by simpa using hs')
      have ht' : eFin (qf y - qf x) ∈ T i := by
        rw [hz]
        exact ht
      exact (hTmask i (qf y - qf x)).mp ht'
    · intro ht
      have ht' : eFin (qf y - qf x) ∈ T i :=
        (hTmask i (qf y - qf x)).mpr ht
      have ht'' : e (eFin y) - e (eFin x) ∈ T i := by
        rw [← hz]
        exact ht'
      have hs' : eFin (y - x) ∈ S i :=
        (hrel i (eFin x) (eFin y)).mpr ht''
      exact (hmaskS i (y - x)).mp hs'
  obtain ⟨u, hu⟩ := finiteCore qf hqf0
  refine ⟨alpha u, ?_⟩
  have he3z : eFin (3 : Fin 8) = (3 : ZMod 8) := by native_decide
  have he5z : eFin (5 : Fin 8) = (5 : ZMod 8) := by native_decide
  have he7z : eFin (7 : Fin 8) = (7 : ZMod 8) := by native_decide
  have halpha (x : Fin 8) : alpha u (eFin x) = eFin (unit u * x) := by
    fin_cases u <;> simp [alpha, zunit, unit, he3z, he5z, he7z]
  intro i x
  let z : Fin 8 := eFin.symm x
  have hz : eFin z = x := by simp [z]
  rw [← hz, halpha z]
  rw [hmaskS i z, hTmask i (unit u * z)]
  have ht := hu (maskOf (S i)) (hrelFin i) z
  exact Bool.eq_iff_iff.mp (by simpa [image] using ht)

end MathlibPlus.GraphTheory
