import Mathlib

namespace MathlibPlus.Open.GraphTheory

/-- There is a valency-28 undirected Cayley-isomorphism defect on the binary
rank-six vector group.  The source connection set contains the seven nonzero
points of an order-eight subgroup, whereas the target contains no such subgroup. -/
def binaryRankSixValencyTwentyEightCIDefect : Prop :=
  let V := Fin 6 → ZMod 2
  ∃ (S T : Set V) (q : V ≃ V),
    q 0 = 0 ∧
    0 ∉ S ∧ 0 ∉ T ∧
    Set.ncard S = 28 ∧ Set.ncard T = 28 ∧
    (∀ x, x ∈ S ↔ -x ∈ S) ∧
    (∀ x, x ∈ T ↔ -x ∈ T) ∧
    (∀ x y, y - x ∈ S ↔ q y - q x ∈ T) ∧
    (∃ W : AddSubgroup V,
      Nat.card W = 8 ∧ ∀ x ∈ W, x ≠ 0 → x ∈ S) ∧
    (∀ W : AddSubgroup V, Nat.card W = 8 →
      ∃ x ∈ W, x ≠ 0 ∧ x ∉ T) ∧
    ¬ ∃ α : V ≃+ V, α '' S = T

end MathlibPlus.Open.GraphTheory



namespace MathlibPlus.GraphTheory

noncomputable section

open scoped BigOperators

private abbrev BinaryRankSixV := Fin 6 → ZMod 2

private def binaryCode (x : BinaryRankSixV) : Nat :=
  ∑ i : Fin 6, (x i).val * 2 ^ i.val

private def binaryVector (n : Nat) : BinaryRankSixV :=
  fun i => if n.testBit i.val then 1 else 0

private def binarySourceCodes : Finset Nat :=
  {1,2,3,4,5,6,7,9,10,11,17,20,21,25,30,31,
   34,36,38,42,45,47,51,52,55,59,61,62}

private def binaryTargetCodes : Finset Nat :=
  {1,2,3,4,5,6,8,9,10,12,16,17,18,20,24,31,
   32,33,34,36,40,47,48,55,59,61,62,63}

private def binarySFin : Finset BinaryRankSixV :=
  Finset.univ.filter (fun x => binaryCode x ∈ binarySourceCodes)

private def binaryTFin : Finset BinaryRankSixV :=
  Finset.univ.filter (fun x => binaryCode x ∈ binaryTargetCodes)

private def binaryQFun (x : BinaryRankSixV) : BinaryRankSixV :=
  ![
    x 0 + x 1 + x 0 * x 1 + x 2 + x 0 * x 2 + x 1 * x 2 + x 3 + x 4 + x 5,
    x 0 + x 0 * x 1 + x 0 * x 2 + x 3 + x 4,
    x 1 + x 0 * x 1 + x 1 * x 2 + x 3 + x 5,
    x 0 * x 1 + x 3,
    x 2 + x 0 * x 2 + x 1 * x 2 + x 4 + x 5,
    x 0 * x 2 + x 4]

private def binaryQ : BinaryRankSixV ≃ BinaryRankSixV :=
  Equiv.ofBijective binaryQFun (by native_decide)

private def binaryW : AddSubgroup BinaryRankSixV :=
  { carrier := {x | x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0}
    zero_mem' := by simp
    add_mem' := by
      intro a b ha hb
      simp only [Set.mem_setOf_eq] at ha hb ⊢
      simp [ha.1, ha.2.1, ha.2.2, hb.1, hb.2.1, hb.2.2]
    neg_mem' := by
      intro a ha
      simp only [Set.mem_setOf_eq] at ha ⊢
      simp [ha.1, ha.2.1, ha.2.2] }

private lemma binaryNoBadTriple :
    ¬ ∃ a b c : BinaryRankSixV,
      binaryCode a ∈ binaryTargetCodes ∧
      binaryCode b ∈ binaryTargetCodes ∧
      binaryCode c ∈ binaryTargetCodes ∧
      binaryCode (a + b) ∈ binaryTargetCodes ∧
      binaryCode (a + c) ∈ binaryTargetCodes ∧
      binaryCode (b + c) ∈ binaryTargetCodes ∧
      binaryCode (a + b + c) ∈ binaryTargetCodes := by
  native_decide

private lemma binaryNoAdditiveTransporter
    (α : BinaryRankSixV ≃+ BinaryRankSixV)
    (hα : α '' (binarySFin : Set BinaryRankSixV) =
      (binaryTFin : Set BinaryRankSixV)) :
    False := by
  have hmem (n : Nat) (hn : binaryVector n ∈ binarySFin) :
      α (binaryVector n) ∈ (binaryTFin : Set BinaryRankSixV) := by
    rw [← hα]
    exact ⟨binaryVector n, hn, rfl⟩
  let a := α (binaryVector 1)
  let b := α (binaryVector 2)
  let c := α (binaryVector 4)
  have h1 : a ∈ (binaryTFin : Set BinaryRankSixV) := by
    exact hmem 1 (by native_decide)
  have h2 : b ∈ (binaryTFin : Set BinaryRankSixV) := by
    exact hmem 2 (by native_decide)
  have h4 : c ∈ (binaryTFin : Set BinaryRankSixV) := by
    exact hmem 4 (by native_decide)
  have h3 : a + b ∈ (binaryTFin : Set BinaryRankSixV) := by
    have hv : binaryVector 3 = binaryVector 1 + binaryVector 2 := by
      native_decide
    have hab : α (binaryVector 3) = a + b := by
      dsimp [a, b]
      rw [hv, map_add]
    rw [← hab]
    exact hmem 3 (by native_decide)
  have h5 : a + c ∈ (binaryTFin : Set BinaryRankSixV) := by
    have hv : binaryVector 5 = binaryVector 1 + binaryVector 4 := by
      native_decide
    have hac : α (binaryVector 5) = a + c := by
      dsimp [a, c]
      rw [hv, map_add]
    rw [← hac]
    exact hmem 5 (by native_decide)
  have h6 : b + c ∈ (binaryTFin : Set BinaryRankSixV) := by
    have hv : binaryVector 6 = binaryVector 2 + binaryVector 4 := by
      native_decide
    have hbc : α (binaryVector 6) = b + c := by
      dsimp [b, c]
      rw [hv, map_add]
    rw [← hbc]
    exact hmem 6 (by native_decide)
  have h7 : a + b + c ∈ (binaryTFin : Set BinaryRankSixV) := by
    have hv : binaryVector 7 = binaryVector 1 + binaryVector 2 + binaryVector 4 := by
      native_decide
    have habc : α (binaryVector 7) = a + b + c := by
      dsimp [a, b, c]
      rw [hv, map_add, map_add]
    rw [← habc]
    exact hmem 7 (by native_decide)
  have hbad : ¬ ∃ a b c : BinaryRankSixV,
      a ∈ (binaryTFin : Set BinaryRankSixV) ∧
      b ∈ (binaryTFin : Set BinaryRankSixV) ∧
      c ∈ (binaryTFin : Set BinaryRankSixV) ∧
      a + b ∈ (binaryTFin : Set BinaryRankSixV) ∧
      a + c ∈ (binaryTFin : Set BinaryRankSixV) ∧
      b + c ∈ (binaryTFin : Set BinaryRankSixV) ∧
      a + b + c ∈ (binaryTFin : Set BinaryRankSixV) := by
    native_decide
  exact hbad ⟨a, b, c, h1, h2, h4, h3, h5, h6, h7⟩

theorem binaryRankSixValencyTwentyEightCIDefect_proof :
    MathlibPlus.Open.GraphTheory.binaryRankSixValencyTwentyEightCIDefect := by
  refine ⟨(binarySFin : Set BinaryRankSixV),
    (binaryTFin : Set BinaryRankSixV), binaryQ, ?_⟩
  have hq0 : binaryQ 0 = 0 := by
    change binaryQFun 0 = 0
    native_decide
  have hS0 : (0 : BinaryRankSixV) ∉ binarySFin := by
    native_decide
  have hT0 : (0 : BinaryRankSixV) ∉ binaryTFin := by
    native_decide
  have hScard : Set.ncard (binarySFin : Set BinaryRankSixV) = 28 := by
    rw [Set.ncard_coe_finset]
    native_decide
  have hTcard : Set.ncard (binaryTFin : Set BinaryRankSixV) = 28 := by
    rw [Set.ncard_coe_finset]
    native_decide
  have hSinv : ∀ x, x ∈ binarySFin ↔ -x ∈ binarySFin := by
    native_decide
  have hTinv : ∀ x, x ∈ binaryTFin ↔ -x ∈ binaryTFin := by
    native_decide
  have hinc : ∀ x y, y - x ∈ binarySFin ↔
      binaryQ y - binaryQ x ∈ binaryTFin := by
    change ∀ x y, y - x ∈ binarySFin ↔
      binaryQFun y - binaryQFun x ∈ binaryTFin
    native_decide
  have hWcard : Nat.card binaryW = 8 := by
    let toW : binaryW → (Fin 3 → ZMod 2) := fun x =>
      ![x.1 0, x.1 1, x.1 2]
    let fromW : (Fin 3 → ZMod 2) → binaryW := fun u =>
      ⟨![u 0, u 1, u 2, 0, 0, 0], by simp [binaryW]⟩
    have hleft : Function.LeftInverse fromW toW := by
      intro x
      apply Subtype.ext
      funext i
      fin_cases i <;> simp [fromW, toW, binaryW]
      · exact x.property.1.symm
      · exact x.property.2.1.symm
      · exact x.property.2.2.symm
    have hright : Function.RightInverse fromW toW := by
      intro u
      funext i
      fin_cases i <;> simp [fromW, toW]
    let e : binaryW ≃ (Fin 3 → ZMod 2) := Equiv.ofBijective toW
      ⟨hleft.injective, hright.surjective⟩
    rw [Nat.card_congr e]
    simp
  have hWsource : ∀ x ∈ binaryW, x ≠ 0 → x ∈ binarySFin := by
    intro x hx hne
    change x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0 at hx
    have hcode : ∀ x : BinaryRankSixV,
        x 3 = 0 ∧ x 4 = 0 ∧ x 5 = 0 → x ≠ 0 →
          binaryCode x ∈ binarySourceCodes := by
      native_decide
    have hcode' := hcode x hx hne
    simpa [binarySFin] using hcode'
  have hWtarget : ∀ H : AddSubgroup BinaryRankSixV, Nat.card H = 8 →
      ∃ x ∈ H, x ≠ 0 ∧ x ∉ (binaryTFin : Set BinaryRankSixV) := by
    intro H hcard
    by_contra hNo
    have hallT : ∀ x : BinaryRankSixV, x ∈ H → x ≠ 0 →
        binaryCode x ∈ binaryTargetCodes := by
      intro x hx hne
      have hxT : x ∈ (binaryTFin : Set BinaryRankSixV) := by
        by_contra hxnot
        exact hNo ⟨x, hx, hne, hxnot⟩
      simpa [binaryTFin] using hxT
    have hpow : (2 : Nat) ^ 3 = 2 ^ Module.finrank (ZMod 2) H := by
      calc
        (2 : Nat) ^ 3 = 8 := by norm_num
        _ = Nat.card H := hcard.symm
        _ = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) H :=
          Module.natCard_eq_pow_finrank
        _ = 2 ^ Module.finrank (ZMod 2) H := by simp
    have hfin : Module.finrank (ZMod 2) H = 3 := by
      exact (Nat.pow_right_injective (by decide) hpow).symm
    let B0 := Module.Basis.ofVectorSpace (ZMod 2) H
    let I := Module.Basis.ofVectorSpaceIndex (ZMod 2) H
    have hI : Fintype.card I = 3 := by
      calc
        Fintype.card I = Module.finrank (ZMod 2) H :=
          (Module.finrank_eq_card_basis B0).symm
        _ = 3 := hfin
    let e : I ≃ Fin 3 := (Fintype.equivFin I).trans (finCongr hI)
    let B : Module.Basis (Fin 3) (ZMod 2) H := B0.reindex e
    have hne (i : Fin 3) : B i ≠ 0 := B.linearIndependent.ne_zero i
    have h01 : B 0 + B 1 ≠ 0 := by
      intro h
      have h' := congrArg (fun z : H => B.equivFun z 0) h
      simp only [map_add, map_zero, Module.Basis.equivFun_self, Pi.add_apply,
        Finsupp.single_apply] at h'
      have hne : (2 : Fin 3) ≠ 0 := by decide
      simp [hne] at h'
    have h02 : B 0 + B 2 ≠ 0 := by
      intro h
      have h' := congrArg (fun z : H => B.equivFun z 0) h
      simp only [map_add, map_zero, Module.Basis.equivFun_self, Pi.add_apply,
        Finsupp.single_apply] at h'
      have hne : (2 : Fin 3) ≠ 0 := by decide
      simp [hne] at h'
    have h12 : B 1 + B 2 ≠ 0 := by
      intro h
      have h' := congrArg (fun z : H => B.equivFun z 1) h
      simp only [map_add, map_zero, Module.Basis.equivFun_self, Pi.add_apply,
        Finsupp.single_apply] at h'
      have hne : (2 : Fin 3) ≠ 1 := by decide
      simp [hne] at h'
    have h012 : B 0 + B 1 + B 2 ≠ 0 := by
      intro h
      have h' := congrArg (fun z : H => B.equivFun z 0) h
      simp only [map_add, map_zero, Module.Basis.equivFun_self, Pi.add_apply,
        Finsupp.single_apply] at h'
      have hne : (2 : Fin 3) ≠ 0 := by decide
      simp [hne] at h'
    have hB0 : binaryCode (B 0 : BinaryRankSixV) ∈ binaryTargetCodes :=
      hallT _ (B 0).property (by intro h; exact hne 0 (Subtype.ext h))
    have hB1 : binaryCode (B 1 : BinaryRankSixV) ∈ binaryTargetCodes :=
      hallT _ (B 1).property (by intro h; exact hne 1 (Subtype.ext h))
    have hB2 : binaryCode (B 2 : BinaryRankSixV) ∈ binaryTargetCodes :=
      hallT _ (B 2).property (by intro h; exact hne 2 (Subtype.ext h))
    have hB01 : binaryCode ((B 0 : BinaryRankSixV) + B 1) ∈ binaryTargetCodes :=
      hallT _ (B 0 + B 1).property (by intro h; exact h01 (Subtype.ext h))
    have hB02 : binaryCode ((B 0 : BinaryRankSixV) + B 2) ∈ binaryTargetCodes :=
      hallT _ (B 0 + B 2).property (by intro h; exact h02 (Subtype.ext h))
    have hB12 : binaryCode ((B 1 : BinaryRankSixV) + B 2) ∈ binaryTargetCodes :=
      hallT _ (B 1 + B 2).property (by intro h; exact h12 (Subtype.ext h))
    have hB012 : binaryCode ((B 0 : BinaryRankSixV) + B 1 + B 2) ∈
        binaryTargetCodes :=
      hallT _ (B 0 + B 1 + B 2).property
        (by intro h; exact h012 (Subtype.ext h))
    exact binaryNoBadTriple ⟨B 0, B 1, B 2, hB0, hB1, hB2, hB01, hB02, hB12,
      hB012⟩
  exact ⟨hq0, hS0, hT0, hScard, hTcard, hSinv, hTinv, hinc,
    ⟨binaryW, hWcard, hWsource⟩, hWtarget,
    (by
      rintro ⟨α, hα⟩
      exact binaryNoAdditiveTransporter α hα)⟩

end
end MathlibPlus.GraphTheory
