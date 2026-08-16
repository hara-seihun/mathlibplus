import Mathlib

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.EndpointPlueckerClaims

/-- The ordered Toeplitz minor associated with a coefficient sequence. -/
def orderedToeplitzMinor (a : ℕ → ℝ) (r : ℕ)
    (rows cols : Fin r → ℕ) : ℝ :=
  Matrix.det (fun i j =>
    if rows i ≤ cols j then a (cols j - rows i) else 0)

/-- PF-infinity uses increasing, not arbitrary, row and column selections. -/
def allToeplitzMinorsNonnegative (a : ℕ → ℝ) : Prop :=
  ∀ (r : ℕ) (rows cols : Fin r → ℕ),
    StrictMono rows → StrictMono cols →
      0 ≤ orderedToeplitzMinor a r rows cols

def schurLogConcave (a : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 0 < n → a n ^ 2 ≥ a (n - 1) * a (n + 1)

def endpointChain (alpha delta0 delta1 delta2 : ℝ) : Prop :=
  alpha * delta1 < delta0 ∧ alpha * delta2 < delta1

def cofactorLogConcave (delta0 delta1 delta2 : ℝ) : Prop :=
  delta1 ^ 2 ≥ delta0 * delta2

def endpointPFPolynomial : Polynomial ℝ :=
  Polynomial.C (1 : ℝ) +
      Polynomial.C (43 / 3 : ℝ) * Polynomial.X +
      Polynomial.C (191 / 3 : ℝ) * Polynomial.X ^ 2 +
      Polynomial.C (269 / 3 : ℝ) * Polynomial.X ^ 3 +
      Polynomial.C (70 / 3 : ℝ) * Polynomial.X ^ 4

def endpointPFSequence : ℕ → ℝ :=
  fun n => endpointPFPolynomial.coeff n

def tailCoefficient (a : ℕ → ℝ) (alpha : ℝ) (n : ℕ) : ℝ :=
  ∑' j : ℕ, a (n + 1 + j) * alpha ^ j

def endpointExteriorCoefficient (a : ℕ → ℝ) (alpha b : ℝ) (n : ℤ) : ℝ :=
  if 0 ≤ n then
    tailCoefficient a alpha n.toNat
  else
    b * alpha ^ (Int.toNat (-n) - 1)

def twoByTwoDet (x00 x01 x10 x11 : ℝ) : ℝ :=
  Matrix.det (fun i j : Fin 2 =>
    if i.1 = 0 then
      if j.1 = 0 then x00 else x01
    else
      if j.1 = 0 then x10 else x11)

def hardEdgeDeltaZero (d : ℤ → ℝ) : ℝ :=
  twoByTwoDet (d 0) (d 1) (d (-1)) (d 0)

def hardEdgeDeltaOne (d : ℤ → ℝ) : ℝ :=
  twoByTwoDet (d 1) (d 2) (d (-1)) (d 0)

def hardEdgeDeltaTwo (d : ℤ → ℝ) : ℝ :=
  twoByTwoDet (d 1) (d 2) (d 0) (d 1)

/-- The fixed PF-infinity witness has opposite endpoint gap orientations. -/
def claim12042 : Prop :=
  let alpha : ℝ := 1 / 4
  let b : ℝ := Polynomial.eval alpha endpointPFPolynomial
  let d : ℤ → ℝ := endpointExteriorCoefficient endpointPFSequence alpha b
  let delta0 : ℝ := hardEdgeDeltaZero d
  let delta1 : ℝ := hardEdgeDeltaOne d
  let delta2 : ℝ := hardEdgeDeltaTwo d
  allToeplitzMinorsNonnegative endpointPFSequence ∧
    endpointPFPolynomial =
      (Polynomial.C (1 : ℝ) + Polynomial.C (1 / 3 : ℝ) * Polynomial.X) *
        (Polynomial.C (1 : ℝ) + Polynomial.C (2 : ℝ) * Polynomial.X) *
        (Polynomial.C (1 : ℝ) + Polynomial.C (5 : ℝ) * Polynomial.X) *
        (Polynomial.C (1 : ℝ) + Polynomial.C (7 : ℝ) * Polynomial.X) ∧
    (∀ n : Fin 5, 0 < endpointPFSequence n.1) ∧
    schurLogConcave endpointPFSequence ∧
    Polynomial.eval (-3 : ℝ) endpointPFPolynomial = 0 ∧
    Polynomial.eval (-1 / 2 : ℝ) endpointPFPolynomial = 0 ∧
    Polynomial.eval (-1 / 5 : ℝ) endpointPFPolynomial = 0 ∧
    Polynomial.eval (-1 / 7 : ℝ) endpointPFPolynomial = 0 ∧
    d (-1) = 1287 / 128 ∧
    d 0 = 1159 / 32 ∧
    d 1 = 2101 / 24 ∧
    d 2 = 191 / 2 ∧
    delta0 = 13811 / 32 ∧
    delta1 = 212201 / 96 ∧
    delta2 = 302735 / 72 ∧
    delta0 - alpha * delta1 = -46469 / 384 ∧
    delta0 - alpha * delta1 < 0 ∧
    delta1 - alpha * delta2 = 83467 / 72 ∧
    delta1 - alpha * delta2 > 0 ∧
    ¬ endpointChain alpha delta0 delta1 delta2

/-- Complete ordered total positivity and cofactor log-concavity do not orient
adjacent endpoint gaps after multiplication by alpha. -/
def claim12043 : Prop :=
  let alpha : ℝ := 1 / 4
  let b : ℝ := Polynomial.eval alpha endpointPFPolynomial
  let d : ℤ → ℝ := endpointExteriorCoefficient endpointPFSequence alpha b
  let delta0 : ℝ := hardEdgeDeltaZero d
  let delta1 : ℝ := hardEdgeDeltaOne d
  let delta2 : ℝ := hardEdgeDeltaTwo d
  allToeplitzMinorsNonnegative endpointPFSequence ∧
    cofactorLogConcave delta0 delta1 delta2 ∧
    d (-1) = 1287 / 128 ∧
    d 0 = 1159 / 32 ∧
    d 1 = 2101 / 24 ∧
    d 2 = 191 / 2 ∧
    delta0 = 13811 / 32 ∧
    delta1 = 212201 / 96 ∧
    delta2 = 302735 / 72 ∧
    delta0 - alpha * delta1 = -46469 / 384 ∧
    delta0 - alpha * delta1 < 0 ∧
    delta1 - alpha * delta2 = 83467 / 72 ∧
    delta1 - alpha * delta2 > 0 ∧
    ¬ endpointChain alpha delta0 delta1 delta2

end MathlibPlus.Open.ResearchFormalization.EndpointPlueckerClaims
