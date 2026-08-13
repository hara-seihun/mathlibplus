import Mathlib

namespace MathlibPlus.GraphTheory.BinaryRankSix

abbrev BinaryRankSixV := Fin 6 → ZMod 2

/-- Little-endian bit-vector encoding used by the frontier witness. -/
def binaryVector (n : Nat) : BinaryRankSixV :=
  fun i => if n.testBit i then 1 else 0

def binaryS : Finset BinaryRankSixV :=
  {binaryVector 1, binaryVector 2, binaryVector 3, binaryVector 4,
   binaryVector 5, binaryVector 6, binaryVector 7, binaryVector 9,
   binaryVector 10, binaryVector 11, binaryVector 17, binaryVector 20,
   binaryVector 21, binaryVector 25, binaryVector 30, binaryVector 31,
   binaryVector 34, binaryVector 36, binaryVector 38, binaryVector 42,
   binaryVector 45, binaryVector 47, binaryVector 51, binaryVector 52,
   binaryVector 55, binaryVector 59, binaryVector 61, binaryVector 62}

def binaryT : Finset BinaryRankSixV :=
  {binaryVector 1, binaryVector 2, binaryVector 3, binaryVector 4,
   binaryVector 5, binaryVector 6, binaryVector 8, binaryVector 9,
   binaryVector 10, binaryVector 12, binaryVector 16, binaryVector 17,
   binaryVector 18, binaryVector 20, binaryVector 24, binaryVector 31,
   binaryVector 32, binaryVector 33, binaryVector 34, binaryVector 36,
   binaryVector 40, binaryVector 47, binaryVector 48, binaryVector 55,
   binaryVector 59, binaryVector 61, binaryVector 62, binaryVector 63}

/-- The quadratic permutation from the frontier handoff. -/
def binaryQFun (x : BinaryRankSixV) : BinaryRankSixV :=
  ![
    x 0 + x 1 + x 0 * x 1 + x 2 + x 0 * x 2 + x 1 * x 2 + x 3 + x 4 + x 5,
    x 0 + x 0 * x 1 + x 0 * x 2 + x 3 + x 4,
    x 1 + x 0 * x 1 + x 1 * x 2 + x 3 + x 5,
    x 0 * x 1 + x 3,
    x 2 + x 0 * x 2 + x 1 * x 2 + x 4 + x 5,
    x 0 * x 2 + x 4]

def binaryQ : BinaryRankSixV ≃ BinaryRankSixV :=
  { toFun := binaryQFun
    invFun := binaryQFun
    left_inv := by native_decide
    right_inv := by native_decide }

example : binaryQ 0 = 0 := by native_decide

example : binaryS.card = 28 := by native_decide
example : binaryT.card = 28 := by native_decide
example : (0 : BinaryRankSixV) ∉ binaryS := by native_decide
example : (0 : BinaryRankSixV) ∉ binaryT := by native_decide

example : ∀ x : BinaryRankSixV, x ∈ binaryS ↔ -x ∈ binaryS := by
  native_decide

example : ∀ x : BinaryRankSixV, x ∈ binaryT ↔ -x ∈ binaryT := by
  native_decide

example : ∀ (x y : BinaryRankSixV),
    y - x ∈ (binaryS : Set BinaryRankSixV) ↔
      binaryQ y - binaryQ x ∈ (binaryT : Set BinaryRankSixV) := by
  native_decide

lemma binaryNoBadTriple :
    ¬ ∃ a b c : BinaryRankSixV,
      a ∈ (binaryT : Set BinaryRankSixV) ∧
      b ∈ (binaryT : Set BinaryRankSixV) ∧
      c ∈ (binaryT : Set BinaryRankSixV) ∧
      a + b ∈ (binaryT : Set BinaryRankSixV) ∧
      a + c ∈ (binaryT : Set BinaryRankSixV) ∧
      b + c ∈ (binaryT : Set BinaryRankSixV) ∧
      a + b + c ∈ (binaryT : Set BinaryRankSixV) := by
  native_decide

lemma binaryNoAdditiveTransporter
    (α : BinaryRankSixV ≃+ BinaryRankSixV)
    (hα : α '' (binaryS : Set BinaryRankSixV) = (binaryT : Set BinaryRankSixV)) :
    False := by
  have hmem (n : Nat) (hn : binaryVector n ∈ binaryS) :
      α (binaryVector n) ∈ (binaryT : Set BinaryRankSixV) := by
    rw [← hα]
    exact ⟨binaryVector n, hn, rfl⟩
  let a := α (binaryVector 1)
  let b := α (binaryVector 2)
  let c := α (binaryVector 4)
  have h1 : a ∈ (binaryT : Set BinaryRankSixV) := by
    exact hmem 1 (by native_decide)
  have h2 : b ∈ (binaryT : Set BinaryRankSixV) := by
    exact hmem 2 (by native_decide)
  have h4 : c ∈ (binaryT : Set BinaryRankSixV) := by
    exact hmem 4 (by native_decide)
  have h3 : a + b ∈ (binaryT : Set BinaryRankSixV) := by
    have hv : binaryVector 3 = binaryVector 1 + binaryVector 2 := by native_decide
    have hab : α (binaryVector 3) = a + b := by
      dsimp [a, b]
      rw [hv, map_add]
    rw [← hab]
    exact hmem 3 (by native_decide)
  have h5 : a + c ∈ (binaryT : Set BinaryRankSixV) := by
    have hv : binaryVector 5 = binaryVector 1 + binaryVector 4 := by native_decide
    have hac : α (binaryVector 5) = a + c := by
      dsimp [a, c]
      rw [hv, map_add]
    rw [← hac]
    exact hmem 5 (by native_decide)
  have h6 : b + c ∈ (binaryT : Set BinaryRankSixV) := by
    have hv : binaryVector 6 = binaryVector 2 + binaryVector 4 := by native_decide
    have hbc : α (binaryVector 6) = b + c := by
      dsimp [b, c]
      rw [hv, map_add]
    rw [← hbc]
    exact hmem 6 (by native_decide)
  have h7 : a + b + c ∈ (binaryT : Set BinaryRankSixV) := by
    have hv : binaryVector 7 = binaryVector 1 + binaryVector 2 + binaryVector 4 := by
      native_decide
    have habc : α (binaryVector 7) = a + b + c := by
      dsimp [a, b, c]
      rw [hv, map_add, map_add]
    rw [← habc]
    exact hmem 7 (by native_decide)
  exact binaryNoBadTriple ⟨a, b, c, h1, h2, h4, h3, h5, h6, h7⟩

end MathlibPlus.GraphTheory.BinaryRankSix

namespace MathlibPlus.Open.GraphTheory

/--
An explicit normalized non-linear Cayley isomorphism between two inverse-closed
28-element connection sets on `F₂⁶`, with no additive-equivalence transporter.
The displayed sets are the exact frontier witness; no stronger hypothesis is
used in this registry statement.
-/
def binaryRankSixValencyTwentyEightCIDefect : Prop :=
  ∃ (S T : Set (Fin 6 → ZMod 2)) (q : (Fin 6 → ZMod 2) ≃ (Fin 6 → ZMod 2)),
    (0 : Fin 6 → ZMod 2) ∉ S ∧
    (0 : Fin 6 → ZMod 2) ∉ T ∧
    (∀ x, x ∈ S ↔ -x ∈ S) ∧
    (∀ x, x ∈ T ↔ -x ∈ T) ∧
    Set.ncard S = 28 ∧
    Set.ncard T = 28 ∧
    q 0 = 0 ∧
    (∀ x y, y - x ∈ S ↔ q y - q x ∈ T) ∧
    ¬ ∃ α : (Fin 6 → ZMod 2) ≃+ (Fin 6 → ZMod 2), α '' S = T

end MathlibPlus.Open.GraphTheory

namespace MathlibPlus.GraphTheory.BinaryRankSix

theorem binaryRankSixValencyTwentyEightCIDefect_proved :
    MathlibPlus.Open.GraphTheory.binaryRankSixValencyTwentyEightCIDefect := by
  refine ⟨(binaryS : Set BinaryRankSixV), (binaryT : Set BinaryRankSixV), binaryQ, ?_⟩
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · rw [Set.ncard_coe_finset]
    native_decide
  constructor
  · rw [Set.ncard_coe_finset]
    native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  · intro h
    obtain ⟨α, hα⟩ := h
    exact binaryNoAdditiveTransporter α hα

end MathlibPlus.GraphTheory.BinaryRankSix
