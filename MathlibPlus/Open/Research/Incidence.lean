import Mathlib

noncomputable section

open scoped BigOperators

namespace MathlibPlus.Open.Research.Incidence

/-- Finite positive divisor-closed sets, the carrier used by the incidence claims. -/
def positiveDivisorClosed (S : Finset ℕ) : Prop :=
  (∀ n ∈ S, 0 < n) ∧
  (∀ n ∈ S, ∀ d : ℕ, d ∣ n → d ∈ S)

/-- The divisor-incidence matrix on a finite set. -/
def incidenceMatrix (S : Finset ℕ) : Matrix S S ℚ :=
  fun d n => if (d : ℕ) ∣ (n : ℕ) then 1 else 0

def incidenceLogTerm (S : Finset ℕ) (r : ℕ) : Matrix S S ℚ :=
  (((-1 : ℚ) ^ (r + 1)) / (r : ℚ)) •
    (incidenceMatrix S - (1 : Matrix S S ℚ)) ^ r

/-- The exact finite incidence logarithm. -/
def incidenceLogFinite (S : Finset ℕ) : Matrix S S ℚ :=
  Finset.sum (Finset.Icc 1 S.card) (fun r => incidenceLogTerm S r)

/-- The same logarithm written as the (eventually zero) infinite series. -/
def incidenceLogInfinite (S : Finset ℕ) : Matrix S S ℚ :=
  tsum (fun r : ℕ => incidenceLogTerm S r)

/-- Claim 11438: nilpotence makes the incidence logarithm a finite exact sum. -/
def claim11438 : Prop :=
  ∀ S : Finset ℕ,
    positiveDivisorClosed S →
      (incidenceMatrix S - (1 : Matrix S S ℚ)) ^ S.card = 0 ∧
      incidenceLogInfinite S = incidenceLogFinite S

/-- The prime-power part of a rational divisor-incidence logarithm entry. -/
def primePowerEntry (d n : ℕ) : ℚ :=
  Finset.sum (Finset.Icc 2 n) (fun p =>
    Finset.sum (Finset.Icc 1 n) (fun k =>
      if Nat.Prime p ∧ n = d * p ^ k then (k : ℚ)⁻¹ else 0))

/-- Claim 11439: the incidence logarithm has exactly prime-power support. -/
def claim11439 : Prop :=
  ∀ (S : Finset ℕ),
    positiveDivisorClosed S →
      ∀ d n : S,
        incidenceLogFinite S d n = primePowerEntry (d : ℕ) (n : ℕ)

/-- The concrete divisor-closed set used for the mixed-composite check. -/
def mixedCompositeSet : Finset ℕ := {1, 2, 3, 4, 6, 8, 9, 12}

/-- Claim 11440: quotients six and twelve vanish in the explicit example. -/
def claim11440 : Prop :=
  ∀ (d n : mixedCompositeSet),
    ((n : ℕ) = 6 * (d : ℕ) ∨ (n : ℕ) = 12 * (d : ℕ)) →
      incidenceLogFinite mixedCompositeSet d n = 0

/-- The strictly upper-triangular divisor-incidence current. -/
def incidenceCurrent (S : Finset ℕ) : Matrix S S ℝ :=
  fun i j => if (i : ℕ) ∣ (j : ℕ) ∧ (i : ℕ) < j then 1 else 0

def scalarExpectation (S : Finset ℕ) (A : Matrix S S ℝ) : Matrix S S ℝ :=
  (Matrix.trace A / (S.card : ℝ)) • (1 : Matrix S S ℝ)

def sourceVariance (S : Finset ℕ) (A : Matrix S S ℝ) : ℝ :=
  Matrix.trace (Matrix.transpose A * A) / (S.card : ℝ)

/-- Claim 11444: scalar expectation sees a universal positive source variance. -/
def claim11444 : Prop :=
  ∀ (S : Finset ℕ),
    S.Nonempty →
    (∃ i j : S, (i : ℕ) ∣ (j : ℕ) ∧ (i : ℕ) < j) →
      scalarExpectation S (incidenceCurrent S) = 0 ∧
      0 < sourceVariance S (incidenceCurrent S)

end MathlibPlus.Open.Research.Incidence

end
