import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1182.Claim31942

abbrev Q12 := ZMod 3 × ZMod 4
abbrev Axis := {h : Q12 // h.1 = 0 ∧ h ≠ (0, 0)}
abbrev Outer := {h : Q12 // h.1 ≠ 0}
abbrev Nonidentity := {h : Q12 // h.1 = 0 ∧ h ≠ (0, 0) ∨ h.1 ≠ 0}
abbrev C4Axis := {h : Q12 // h.1 = 0}

def q12Parity (i : ZMod 4) : ZMod 3 :=
  (-1 : ZMod 3) ^ i.val

def q12Mul (x y : Q12) : Q12 :=
  (x.1 + q12Parity x.2 * y.1, x.2 + y.2)

def q12One : Q12 := (0, 0)

def q12Inv (x : Q12) : Q12 :=
  (-q12Parity x.2 * x.1, -x.2)

def q12Sigma (x : Q12) : Q12 :=
  if x = ((1, 1) : Q12) then (1, 3)
  else if x = ((1, 3) : Q12) then (2, 2)
  else if x = ((2, 2) : Q12) then (1, 1)
  else if x = ((2, 1) : Q12) then (1, 2)
  else if x = ((1, 2) : Q12) then (2, 3)
  else if x = ((2, 3) : Q12) then (2, 1)
  else x

def q12SigmaInv (x : Q12) : Q12 :=
  if x = ((1, 1) : Q12) then (2, 2)
  else if x = ((1, 3) : Q12) then (1, 1)
  else if x = ((2, 2) : Q12) then (1, 3)
  else if x = ((2, 1) : Q12) then (2, 3)
  else if x = ((1, 2) : Q12) then (2, 1)
  else if x = ((2, 3) : Q12) then (1, 2)
  else x

def q12Sign (h : Q12) : ℤ :=
  if h.2.val % 2 = 0 then 1 else -1

def q12Relative (h k : Q12) : Q12 :=
  q12SigmaInv (q12Mul (q12Sigma (q12Mul h k)) (q12Inv (q12Sigma k)))

def q12Scalar (h : Q12) : ℤ :=
  q12Sign (q12Sigma h) * q12Sign h

def fullVoltageEntry {S : Set Q12} [Fintype S]
    (row : Unit ⊕ (S × Q12)) (col : Q12 ⊕ S) : ℤ :=
  match row with
  | Sum.inl _ =>
      match col with
      | Sum.inl h => if h = q12One then 1 else 0
      | Sum.inr _ => 0
  | Sum.inr data =>
      let c := data.1.1
      let k := data.2
      let product := q12Mul c k
      let target := q12Relative c k
      match col with
      | Sum.inl h =>
          (if h = product then 1 else 0) -
            (if h = k then
              q12Sign (q12Sigma product) * q12Sign (q12Sigma k)
             else 0) -
            (if h = target then 1 else 0)
      | Sum.inr s =>
          (if s.1 = c then q12Scalar product else 0) -
            (if s.1 = target then q12Scalar target else 0)

noncomputable def fullVoltageMatrix {S : Set Q12} [Fintype S] :
    Matrix (Unit ⊕ (S × Q12)) (Q12 ⊕ S) ℤ :=
  fun row col => fullVoltageEntry row col

def expectedVoltage (c : Q12) : ℤ :=
  1 - q12Sign (q12Sigma c)

def differenceEntry {S : Set Q12} [Fintype S]
    (c : S) (col : Q12 ⊕ S) : ℤ :=
  match col with
  | Sum.inl h => if h = c.1 then 1 else 0
  | Sum.inr s =>
      (if s.1 = c.1 then q12Scalar c.1 else 0) -
        (if s.1 = q12Sigma c.1 then 1 else 0)

noncomputable def fullAugmentedMatrix {S : Set Q12} [Fintype S] :
    Matrix ((Unit ⊕ (S × Q12)) ⊕ (S × S)) (Q12 ⊕ S) ℤ :=
  fun row col =>
    match row with
    | Sum.inl base => fullVoltageEntry base col
    | Sum.inr pair =>
        expectedVoltage pair.1.1 * differenceEntry pair.2 col -
          expectedVoltage pair.2.1 * differenceEntry pair.1 col

def axisVoltageEntry (row : Unit ⊕ (Axis × C4Axis)) (col : Q12) : ℤ :=
  match row with
  | Sum.inl _ => if col = q12One then 1 else 0
  | Sum.inr data =>
      let c := data.1.1
      let k := data.2.1
      let product := q12Mul c k
      (if col = product then 1 else 0) -
        (if col = k then q12Sign c else 0) -
        (if col = c then 1 else 0)

noncomputable def axisVoltageMatrix :
    Matrix (Unit ⊕ (Axis × C4Axis)) Q12 ℤ :=
  fun row col => axisVoltageEntry row col

def axisDifferenceEntry (c : Axis) (col : Q12) : ℤ :=
  if col = c.1 then 1 else 0

noncomputable def axisAugmentedMatrix :
    Matrix ((Unit ⊕ (Axis × C4Axis)) ⊕ (Axis × Axis)) Q12 ℤ :=
  fun row col =>
    match row with
    | Sum.inl base => axisVoltageEntry base col
    | Sum.inr pair =>
        expectedVoltage pair.1.1 * axisDifferenceEntry pair.2 col -
          expectedVoltage pair.2.1 * axisDifferenceEntry pair.1 col

def rationalMatrix {I J : Type*} (M : Matrix I J ℤ) : Matrix I J ℚ :=
  fun i j => M i j

def modularMatrix {I J : Type*} (p : ℕ) (M : Matrix I J ℤ) : Matrix I J (ZMod p) :=
  fun i j => M i j

def smithPrimeSupport {I J : Type*} [Fintype J]
    (M : Matrix I J ℤ) : Set ℕ :=
  {p | Nat.Prime p ∧
    Matrix.rank (modularMatrix p M) < Matrix.rank (rationalMatrix M)}

def voltageWitness {I J : Type*} [Fintype J]
    (M : Matrix I J ℤ) (r : ℕ) (d : ℤ) : Prop :=
  ∃ rows : Fin r → I, ∃ cols : Fin r → J,
    Function.Injective rows ∧ Function.Injective cols ∧
      Matrix.det (M.submatrix rows cols) = d

def voltageRankCertificate {I J K : Type*} [Fintype J] [Fintype K]
    (M : Matrix I J ℤ) (Aug : Matrix K J ℤ) (r : ℕ) (d : ℤ) : Prop :=
  Matrix.rank (rationalMatrix M) = r ∧
    voltageWitness M r d ∧
    Matrix.rank (rationalMatrix Aug) = r ∧
    smithPrimeSupport M ⊆ ({2, 3} : Set ℕ) ∧
    smithPrimeSupport Aug ⊆ ({2, 3} : Set ℕ) ∧
    ∀ p : ℕ, Nat.Prime p → 3 < p →
      Matrix.rank (modularMatrix p M) = r ∧
        Matrix.rank (modularMatrix p Aug) = r

noncomputable def claim31942 : Prop :=
  letI : Fintype Axis := Fintype.ofFinite Axis
  letI : Fintype Outer := Fintype.ofFinite Outer
  letI : Fintype Nonidentity := Fintype.ofFinite Nonidentity
  letI : Fintype C4Axis := Fintype.ofFinite C4Axis
  voltageRankCertificate axisVoltageMatrix axisAugmentedMatrix 3 1 ∧
    voltageRankCertificate (fullVoltageMatrix (S := {h : Q12 | h.1 = 0 ∧ h ≠ (0, 0)}))
      (fullAugmentedMatrix (S := {h : Q12 | h.1 = 0 ∧ h ≠ (0, 0)})) 11 (-2) ∧
    voltageRankCertificate (fullVoltageMatrix (S := {h : Q12 | h.1 ≠ 0}))
      (fullAugmentedMatrix (S := {h : Q12 | h.1 ≠ 0})) 17 18 ∧
    voltageRankCertificate (fullVoltageMatrix (S := {h : Q12 | h.1 = 0 ∧ h ≠ (0, 0) ∨ h.1 ≠ 0}))
      (fullAugmentedMatrix (S := {h : Q12 | h.1 = 0 ∧ h ≠ (0, 0) ∨ h.1 ≠ 0})) 20 12

end MathlibPlus.Open.ResearchFormalization.R1182.Claim31942
