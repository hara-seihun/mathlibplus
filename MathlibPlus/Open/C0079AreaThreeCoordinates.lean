import MathlibPlus.Open.C0079NeighboringMinor

namespace MathlibPlus.Open.C0079

open scoped BigOperators

noncomputable section

/-- The finite row carrier for a row value below `d`. -/
def rowBelow1181 (d : ℕ) : Fin d → Fin (2 * d) :=
  fun i => Fin.cast (Nat.two_mul d).symm (Fin.castAdd d i)

/-- Finite row carriers for the boundary values used by the six padded shapes. -/
def rowDMinusOne1181 (d : ℕ) (hd : 1 ≤ d) : Fin (2 * d) :=
  Fin.castLE (Nat.le_mul_of_pos_left d (Nat.zero_lt_succ 1))
    (Fin.castLE ((Nat.succ_le_iff).2
      (Nat.sub_lt (Nat.zero_lt_of_lt hd) (Nat.zero_lt_succ 0)))
      (Fin.last (d - 1)))

def rowDMinusTwo1181 (d : ℕ) (hd : 2 ≤ d) : Fin (2 * d) :=
  Fin.castLE (Nat.le_mul_of_pos_left d (Nat.zero_lt_succ 1))
    (Fin.castLE ((Nat.succ_le_iff).2
      (Nat.sub_lt (Nat.zero_lt_of_lt hd) (Nat.zero_lt_succ 1)))
      (Fin.last (d - 2)))

def rowD1181 (d : ℕ) (hd : 1 ≤ d) : Fin (2 * d) :=
  Fin.cast (Nat.two_mul d).symm
    (Fin.castLE (Nat.add_le_add_left hd d) (Fin.last d))

def rowDPlusOne1181 (d : ℕ) (hd : 2 ≤ d) : Fin (2 * d) :=
  Fin.cast (Nat.two_mul d).symm
    (Fin.castLE (Nat.add_le_add_left hd d) (Fin.last (d + 1)))

def rowDPlusTwo1181 (d : ℕ) (hd : 3 ≤ d) : Fin (2 * d) :=
  Fin.cast (Nat.two_mul d).symm
    (Fin.castLE (Nat.add_le_add_left hd d) (Fin.last (d + 2)))

def oneRows1181 (d : ℕ) (hd : 1 ≤ d) : Fin d → Fin (2 * d) :=
  fun i => if i.1 = d - 1 then rowD1181 d hd else rowBelow1181 d i

def twoRows1181 (d : ℕ) (hd : 2 ≤ d) : Fin d → Fin (2 * d) :=
  fun i => if i.1 = d - 1 then rowDPlusOne1181 d hd else rowBelow1181 d i

def oneOneRows1181 (d : ℕ) (hd : 2 ≤ d) : Fin d → Fin (2 * d) :=
  fun i =>
    if i.1 = d - 2 then rowDMinusOne1181 d (Nat.le_trans
      (Nat.succ_le_succ (Nat.zero_le 1)) hd)
    else if i.1 = d - 1 then rowD1181 d (Nat.le_trans
      (Nat.succ_le_succ (Nat.zero_le 1)) hd)
    else rowBelow1181 d i

def twoOneRows1181 (d : ℕ) (hd : 2 ≤ d) : Fin d → Fin (2 * d) :=
  fun i =>
    if i.1 = d - 2 then rowDMinusOne1181 d (Nat.le_trans
      (Nat.succ_le_succ (Nat.zero_le 1)) hd)
    else if i.1 = d - 1 then rowDPlusOne1181 d hd
    else rowBelow1181 d i

def oneOneOneRows1181 (d : ℕ) (hd : 3 ≤ d) : Fin d → Fin (2 * d) :=
  fun i =>
    if i.1 = d - 3 then rowDMinusTwo1181 d (Nat.le_trans
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))) hd)
    else if i.1 = d - 2 then rowDMinusOne1181 d (Nat.le_trans
      (Nat.succ_le_succ (Nat.zero_le 1))
        (Nat.le_trans
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))) hd))
    else if i.1 = d - 1 then rowD1181 d (Nat.le_trans
      (Nat.succ_le_succ (Nat.zero_le 1))
        (Nat.le_trans
          (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))) hd))
    else rowBelow1181 d i

/-- A flagged maximal minor on a finite row map. -/
def flaggedMinorRows1181 (d : ℕ) (a : ℝ)
    (rows : Fin d → Fin (2 * d)) : ℝ :=
  Matrix.det ((flaggedArray d a).submatrix rows (fun j => j))

/-- The three area-three cup coordinates in the signed minor carrier. -/
def alphaThree1181 (d : ℕ) (hd : 3 ≤ d) (a : ℝ) : ℝ :=
  let hd2 : 2 ≤ d := Nat.le_trans
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))) hd
  let hd1 : 1 ≤ d := Nat.le_trans
    (Nat.succ_le_succ (Nat.zero_le 1)) hd2
  emptyMinor d a - flaggedMinorRows1181 d a (oneRows1181 d hd1) +
      flaggedMinorRows1181 d a (twoRows1181 d hd2) - threeMinor d hd a

def alphaOneOneOne1181 (d : ℕ) (hd : 3 ≤ d) (a : ℝ) : ℝ :=
  let hd2 : 2 ≤ d := Nat.le_trans
    (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le 1))) hd
  let hd1 : 1 ≤ d := Nat.le_trans
    (Nat.succ_le_succ (Nat.zero_le 1)) hd2
  emptyMinor d a - flaggedMinorRows1181 d a (oneRows1181 d hd1) +
      flaggedMinorRows1181 d a (oneOneRows1181 d hd2) -
        flaggedMinorRows1181 d a (oneOneOneRows1181 d hd)

/-- The pair-sum product `P_d(b)`. -/
def principalProduct1181 (d : ℕ) (b : ℝ) : ℝ :=
  (Nat.factorial d : ℝ) *
    ∏ p ∈ Finset.range (d + 1),
      ∏ q ∈ Finset.range (d + 1),
        if p < q then 2 * b + (p : ℝ) + (q : ℝ) + 1 else 1

/-- The shifted variable `X=2b+d+1`. -/
def x1181 (d : ℕ) (b : ℝ) : ℝ :=
  2 * b + (d : ℝ) + 1

/-- The exact numerator for the `(3)` coordinate. -/
def numeratorThree1181 (d : ℕ) (b : ℝ) : ℝ :=
  24 * b ^ 3 +
    12 * (2 * (d : ℝ) + 5) * b ^ 2 +
    3 * ((d : ℝ) + 2) * (3 * (d : ℝ) + 5) * b +
    ((d : ℝ) - 1) * ((d : ℝ) + 3) * ((d : ℝ) + 4)

/-- The exact numerator for the `(1,1,1)` coordinate. -/
def numeratorOneOneOne1181 (d : ℕ) (b : ℝ) : ℝ :=
  24 * b ^ 3 +
    12 * (2 * (d : ℝ) - 1) * b ^ 2 +
    3 * (3 * (d : ℝ) ^ 2 + (d : ℝ) + 2) * b +
    ((d : ℝ) - 3) * ((d : ℝ) + 1) * ((d : ℝ) + 2)

/-- Claim 1181: the `(3)` cup coordinate has the displayed rational form,
with its cross-multiplied identity retained at denominator zeros. -/
def claim1181 : Prop :=
  ∀ (d : ℕ) (hd : 3 ≤ d) (a : ℝ),
    let b : ℝ := a - 1 / 2
    let x : ℝ := x1181 d b
    let numerator : ℝ := numeratorThree1181 d b * principalProduct1181 d b
    let denominator : ℝ := 3 * x * (x + 1) * (x + 2)
    (denominator ≠ 0 → alphaThree1181 d hd a = numerator / denominator) ∧
      denominator * alphaThree1181 d hd a = numerator

/-- Claim 1183: the `(1,1,1)` cup coordinate has the displayed rational
form, with its cross-multiplied identity retained at denominator zeros. -/
def claim1183 : Prop :=
  ∀ (d : ℕ) (hd : 3 ≤ d) (a : ℝ),
    let b : ℝ := a - 1 / 2
    let x : ℝ := x1181 d b
    let numerator : ℝ := numeratorOneOneOne1181 d b * principalProduct1181 d b
    let denominator : ℝ := 3 * (x - 2) * (x - 1) * x
    (denominator ≠ 0 → alphaOneOneOne1181 d hd a = numerator / denominator) ∧
      denominator * alphaOneOneOne1181 d hd a = numerator

end

end MathlibPlus.Open.C0079
