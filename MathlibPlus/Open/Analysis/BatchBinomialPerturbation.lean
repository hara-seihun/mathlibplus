import Mathlib

namespace MathlibPlus.Open.Analysis

open Polynomial

noncomputable section

/-- The polynomial `1 + x` used in the admitted binomial statement. -/
def onePlusX : Polynomial ℤ := 1 + Polynomial.X

/-- The binomial factor with a nonnegative integer exponent. -/
def binomialFactor (r : ℤ) : Polynomial ℤ := onePlusX ^ r.toNat

/-- The star independence polynomial occurring in the factorization. -/
def starIndependencePolynomial (r : ℤ) : Polynomial ℤ :=
  binomialFactor r + Polynomial.X

/-- The three-term polynomial in the admitted statement. -/
def F (n a b : ℤ) : Polynomial ℤ :=
  onePlusX ^ n.toNat + Polynomial.X * onePlusX ^ a.toNat +
    Polynomial.X * onePlusX ^ b.toNat

/-- The reduced polynomial in the admitted statement. -/
def G (s h : ℤ) : Polynomial ℤ :=
  onePlusX ^ s.toNat + Polynomial.X * onePlusX ^ h.toNat + Polynomial.X

/-- The polynomial before the final `+ x` perturbation. -/
def H (s h : ℤ) : Polynomial ℤ :=
  onePlusX ^ s.toNat + Polynomial.X * onePlusX ^ h.toNat

/-- Log-concavity of the nonnegative coefficient sequence of an integer polynomial. -/
def coefficientLogConcave (p : Polynomial ℤ) : Prop :=
  (∀ k : ℕ, 0 ≤ p.coeff k) ∧
    (∀ k : ℕ, 0 < k →
      p.coeff (k - 1) * p.coeff (k + 1) ≤ p.coeff k ^ 2)

/-- The slack in the coefficient log-concavity inequality at one rank. -/
def logConcavitySlack (p : Polynomial ℤ) (k : ℕ) : ℤ :=
  p.coeff k ^ 2 - p.coeff (k - 1) * p.coeff (k + 1)

/-- The coefficient changes and rank-wise effects of adding the final `+ x`. -/
def finalXEffects (s h : ℤ) : Prop :=
  G s h = H s h + Polynomial.X ∧
    (G s h).coeff 1 = (H s h).coeff 1 + 1 ∧
    (∀ k : ℕ, k ≠ 1 → (G s h).coeff k = (H s h).coeff k) ∧
    (∀ k : ℕ, 3 ≤ k →
      logConcavitySlack (H s h) k = logConcavitySlack (G s h) k) ∧
    logConcavitySlack (G s h) 1 =
      logConcavitySlack (H s h) 1 + 2 * (H s h).coeff 1 + 1 ∧
    logConcavitySlack (H s h) 1 ≤ logConcavitySlack (G s h) 1 ∧
    0 ≤ logConcavitySlack (G s h) 2

/-- The three coefficient expressions used for the rank-two slack. -/
def g₁ (s : ℤ) : ℤ := s + 2

def g₂ (s h : ℤ) : ℤ := (Nat.choose s.toNat 2 : ℤ) + h

def g₃ (s h : ℤ) : ℤ :=
  (Nat.choose s.toNat 3 : ℤ) + (Nat.choose h.toNat 2 : ℤ)

/-- The rank-two slack written using the displayed `g₁`, `g₂`, and `g₃`. -/
def D (s h : ℤ) : ℤ := g₂ s h ^ 2 - g₁ s * g₃ s h

/-- The polynomial expression asserted to equal `12 D`. -/
def DPolynomial (s h : ℤ) : ℤ :=
  s ^ 4 - 4 * s ^ 3 + 11 * s ^ 2 - 8 * s +
    (12 * s ^ 2 - 6 * s + 12) * h - 6 * s * h ^ 2

/-- Concavity on the interval from zero to a nonnegative endpoint. -/
def concaveOnZeroTo (f : ℝ → ℝ) (u : ℝ) : Prop :=
  ∀ x y t : ℝ,
    x ∈ Set.Icc 0 u →
    y ∈ Set.Icc 0 u →
    t ∈ Set.Icc 0 1 →
    f (t * x + (1 - t) * y) ≥ t * f x + (1 - t) * f y

/-- The real polynomial in `h` whose integer values are `DPolynomial`. -/
def DPolynomialReal (s h : ℝ) : ℝ :=
  s ^ 4 - 4 * s ^ 3 + 11 * s ^ 2 - 8 * s +
    (12 * s ^ 2 - 6 * s + 12) * h - 6 * s * h ^ 2

/--
The exact admitted binomial-reduction and perturbation statement, including
its coefficient effects, rank-two identity, concavity, endpoint values, and
nonnegativity conclusion.
-/
def binomialPerturbationClaim : Prop :=
  (∀ n a b : ℤ,
    0 ≤ b → b ≤ a → a ≤ n →
      F n a b = binomialFactor b * G (n - b) (a - b)) ∧
  (∀ s h : ℤ,
    0 ≤ h → h ≤ s →
      H s h = binomialFactor h * starIndependencePolynomial (s - h) ∧
      coefficientLogConcave (H s h) ∧
      finalXEffects s h ∧
      (G s h).coeff 1 = g₁ s ∧
      (G s h).coeff 2 = g₂ s h ∧
      (G s h).coeff 3 = g₃ s h ∧
      logConcavitySlack (G s h) 2 = D s h) ∧
  (∀ s : ℤ, 0 ≤ s →
    12 * D s 0 = s * (s - 1) * (s ^ 2 - 3 * s + 8) ∧
    0 ≤ s * (s - 1) * (s ^ 2 - 3 * s + 8) ∧
    12 * D s s = s * (s + 1) * (s ^ 2 + s + 4) ∧
    0 ≤ s * (s + 1) * (s ^ 2 + s + 4) ∧
    concaveOnZeroTo
      (fun h : ℝ => DPolynomialReal (s : ℝ) h) (s : ℝ)) ∧
  (∀ s h : ℤ, 0 ≤ h → h ≤ s →
    12 * D s h = DPolynomial s h ∧
    0 ≤ D s h)

end

end MathlibPlus.Open.Analysis
