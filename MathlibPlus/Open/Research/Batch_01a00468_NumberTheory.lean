import Mathlib

namespace MathlibPlus.Open.Research.Batch_01a00468_NumberTheory

noncomputable section
open scoped BigOperators

/-- The endpoint function used by the order-n prime intervals. -/
def primeIntervalEndpoint (n : ℕ) (B x : ℝ) : ℝ :=
  x * (1 + B / (Real.log x) ^ n)

def orderFourCoefficient : ℝ :=
  (34 : ℝ) / 1327 * (Real.log (1327 : ℝ)) ^ 4

def orderFiveCoefficient : ℝ :=
  (252969215940000000000 : ℝ) / 1999999999996903

def orderFourWitness (B x : ℝ) : Prop :=
  ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧
    (p : ℝ) ≤ primeIntervalEndpoint 4 B x

def validOrderFourCoefficient (B : ℝ) : Prop :=
  ∀ x : ℝ, 2 ≤ x → orderFourWitness B x

/-- Claim 945: the active order-four gap is globally sharp. -/
def claim945 : Prop :=
  primeIntervalEndpoint 4 orderFourCoefficient 1327 = 1361 ∧
  (∀ B : ℝ, B < orderFourCoefficient →
    primeIntervalEndpoint 4 B 1327 < 1361) ∧
  (∀ p : ℕ, Nat.Prime p →
    ¬ (1327 < (p : ℝ) ∧ (p : ℝ) < 1361)) ∧
  (∀ B : ℝ, B < orderFourCoefficient →
    ¬ orderFourWitness B 1327) ∧
  validOrderFourCoefficient orderFourCoefficient ∧
  (∀ B : ℝ, validOrderFourCoefficient B → orderFourCoefficient ≤ B)

/-- Claim 949: the order-four interval gives the initial order-five range. -/
def claim949 : Prop :=
  (∀ x : ℝ, 2 ≤ x →
    Real.log x ≤ orderFiveCoefficient / orderFourCoefficient →
    primeIntervalEndpoint 4 orderFourCoefficient x ≤
      primeIntervalEndpoint 5 orderFiveCoefficient x) ∧
  (∀ x : ℝ, 2 ≤ x →
    Real.log x ≤ orderFiveCoefficient / orderFourCoefficient →
    ∃ p : ℕ, Nat.Prime p ∧ x < (p : ℝ) ∧
      (p : ℝ) ≤ primeIntervalEndpoint 5 orderFiveCoefficient x)

def normalizedPsiError (x : ℝ) : ℝ :=
  ‖Chebyshev.psi x - x‖ / x

/-- Claim 1029: the low-range square-root-exponential FKS envelope. -/
def claim1029 : Prop :=
  ∀ x : ℝ, 0 < Real.log x → Real.log x ≤ 2100 →
    normalizedPsiError x ≤
      2 * Real.rpow (Real.log x) (3 / 2 : ℝ) *
        Real.exp (-(0.8476836 : ℝ) * Real.sqrt (Real.log x))

def lowRangeRewriteCoefficient (L : ℝ) : ℝ :=
  2 * Real.exp ((0.88178 - 0.8476836 : ℝ) * Real.sqrt L)

/-- Claim 1030: the low-range coefficient conversion and its endpoint margin. -/
def claim1030 : Prop :=
  (∀ L : ℝ, 0 < L → L ≤ 2008 →
    2 * Real.exp (-(0.8476836 : ℝ) * Real.sqrt L) =
      lowRangeRewriteCoefficient L *
        Real.exp (-(0.88178 : ℝ) * Real.sqrt L)) ∧
  StrictMonoOn lowRangeRewriteCoefficient (Set.Ioc (0 : ℝ) 2008) ∧
  lowRangeRewriteCoefficient 2008 < 9.2202181 ∧
  9.2202181 - lowRangeRewriteCoefficient 2008 > 0.0033

end
end MathlibPlus.Open.Research.Batch_01a00468_NumberTheory
