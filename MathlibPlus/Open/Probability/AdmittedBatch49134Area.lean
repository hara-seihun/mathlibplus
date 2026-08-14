import Mathlib

open scoped BigOperators Classical

namespace MathlibPlus.Open.Probability.AdmittedBatch49134

noncomputable section

abbrev Cube (n : ℕ) := Fin n → Bool
abbrev RealTable (n : ℕ) := Cube n → ℝ
abbrev SignedTable (n : ℕ) := Cube n → ℝ

def insertBit {n : ℕ} (i : Fin (n + 1)) (b : Bool)
    (x : Cube n) (j : Fin (n + 1)) : Bool :=
  if h : j.val < i.val then
    x ⟨j.val, by omega⟩
  else if h : j.val = i.val then
    b
  else
    x ⟨j.val - 1, by omega⟩

def restrictTable {n : ℕ} (f : RealTable (n + 1))
    (i : Fin (n + 1)) (b : Bool) : RealTable n :=
  fun x => f (insertBit i b x)

def meanValue {n : ℕ} (f : RealTable n) : ℝ :=
  (1 / (2 ^ n : ℝ)) * ∑ x : Cube n, f x

def variance {n : ℕ} (f : RealTable n) : ℝ :=
  (1 / (2 ^ n : ℝ)) * ∑ x : Cube n, (f x - meanValue f) ^ 2

/-- The recursive area functional used by R-3888. -/
noncomputable def area : (n : ℕ) → RealTable n → ℝ
  | 0, f => variance f
  | n + 1, f =>
      variance f +
        sInf {z : ℝ | ∃ i : Fin (n + 1),
          z = (area n (restrictTable f i false) +
            area n (restrictTable f i true)) / 2}

def signedTable {n : ℕ} (f : Cube n → Bool) : SignedTable n :=
  fun x => if f x then 1 else -1

def freeDecrement {n : ℕ} (f : RealTable (n + 1)) (i : Fin (n + 1)) : ℝ :=
  area (n + 1) f -
    (area n (restrictTable f i false) +
      area n (restrictTable f i true)) / 2

/-- R-3888 S1: the recursive area definition and the established Boolean facts. -/
def areaDecrementFacts : Prop :=
  (∀ (n : ℕ) (f : RealTable n),
    n = 0 → area n f = variance f) ∧
  (∀ (n : ℕ) (f : RealTable (n + 1)),
    area (n + 1) f = variance f +
      sInf {z : ℝ | ∃ i : Fin (n + 1),
        z = (area n (restrictTable f i false) +
          area n (restrictTable f i true)) / 2}) ∧
  (∀ (n : ℕ), ∀ f : Cube (n + 1) → Bool,
    (∀ i : Fin (n + 1), 0 ≤ freeDecrement (signedTable f) i) ∧
      ∃ i : Fin (n + 1), ∀ j : Fin (n + 1),
        freeDecrement (signedTable f) j ≤ freeDecrement (signedTable f) i ∧
        freeDecrement (signedTable f) i = variance (signedTable f))

def pointwiseProduct {n : ℕ} (f g : SignedTable n) : SignedTable n :=
  fun x => f x * g x

def truthTableCount (n : ℕ) : ℕ := 2 ^ (2 ^ n)

def unorderedPairCount (n : ℕ) : ℕ :=
  Nat.choose (truthTableCount n + 1) 2

/-- R-3888 S2: the exhaustive three-bit-or-fewer subadditivity assertion. -/
def smallDimensionalSubadditivity : Prop :=
  unorderedPairCount 1 = 10 ∧
    unorderedPairCount 2 = 136 ∧
    unorderedPairCount 3 = 32896 ∧
    (∀ (n : ℕ), (n = 1 ∨ n = 2 ∨ n = 3) →
      ∀ h k : Cube n → Bool,
        area n (pointwiseProduct (signedTable h) (signedTable k)) ≤
          area n (signedTable h) + area n (signedTable k)) ∧
    (∀ (n : ℕ), n < 4 →
      ∀ h k : Cube n → Bool,
        area n (pointwiseProduct (signedTable h) (signedTable k)) ≤
          area n (signedTable h) + area n (signedTable k))

def fourBitH : Cube 4 → Bool :=
  fun x => x 0 && x 1

def fourBitK : Cube 4 → Bool :=
  fun x => x 2 && x 3

def cubeIndex {n : ℕ} (x : Cube n) : ℕ :=
  ∑ i : Fin n, if x i then 2 ^ i.val else 0

def positiveMask {n : ℕ} (f : SignedTable n) : ℕ :=
  ∑ x : Cube n, if f x = 1 then 2 ^ cubeIndex x else 0

def maskTable (n m : ℕ) : SignedTable n :=
  fun x =>
    if (m / (2 ^ cubeIndex x)) % 2 = 1 then 1 else -1

/-- R-3888 S3: the four-sign product counterexample with its masks. -/
def fourBitProductCounterexample : Prop :=
  let h := signedTable fourBitH
  let k := signedTable fourBitK
  let hk := pointwiseProduct h k
  variance h = (3 / 4 : ℝ) ∧
    variance k = (3 / 4 : ℝ) ∧
    variance hk = (15 / 16 : ℝ) ∧
    area 4 h = (5 / 4 : ℝ) ∧
    area 4 k = (5 / 4 : ℝ) ∧
    area 4 hk = (43 / 16 : ℝ) ∧
    area 4 hk - area 4 h - area 4 k = (3 / 16 : ℝ) ∧
    positiveMask h = 34952 ∧ positiveMask k = 61440 ∧
    positiveMask hk = 34679

/-- R-3888 S5: the three-bit free-coordinate pruning counterexample. -/
def threeBitFreeDecrementCounterexample : Prop :=
  let h := maskTable 3 3
  let k := maskTable 3 6
  let hk := pointwiseProduct h k
  positiveMask h = 3 ∧ positiveMask k = 6 ∧ positiveMask hk = 250 ∧
    freeDecrement (n := 2) hk 0 = (3 / 4 : ℝ) ∧
    freeDecrement (n := 2) h 0 = 0 ∧
    freeDecrement (n := 2) k 0 = (1 / 2 : ℝ) ∧
    freeDecrement (n := 2) hk 0 - freeDecrement (n := 2) h 0 -
        freeDecrement (n := 2) k 0 =
      (1 / 4 : ℝ)

end

end MathlibPlus.Open.Probability.AdmittedBatch49134
