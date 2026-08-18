import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.C0003

noncomputable section
open Classical
open scoped BigOperators

/-- The factorial anchor ratio field. -/
def factorialAnchor (k : ℕ) : ℝ :=
  ((k : ℝ) + 1)⁻¹ ^ 2

/-- The exponential ratio-field perturbation of the factorial anchor. -/
def ratioPerturbation (f : ℕ → ℝ) (ε : ℝ) (k : ℕ) : ℝ :=
  factorialAnchor k * Real.exp (ε * f k)

/-- The logarithmic derivative carried from a ratio-field direction. -/
def logarithmicRatioDirection (f : ℕ → ℝ) : Prop :=
  ∀ k : ℕ,
    HasDerivAt (fun ε : ℝ => Real.log (ratioPerturbation f ε k)) (f k) 0

/-- The polynomial ratio jet f_k = k^p. -/
def polynomialRatioJet (p : ℕ) (k : ℕ) : ℝ :=
  (k : ℝ) ^ p

/-- Claim 49: the factorial anchor and exponential ratio-field coordinate have
logarithmic direction f, with the listed low polynomial jets included. -/
def claim49 : Prop :=
  (∀ f : ℕ → ℝ, logarithmicRatioDirection f) ∧
    ∀ p : Fin 4,
      logarithmicRatioDirection (polynomialRatioJet p.1)

/-- The product coordinate obtained from a ratio field through level m. -/
noncomputable def productCoordinate (ρ : ℕ → ℝ) (m : ℕ) : ℝ :=
  Finset.prod (Finset.range m) (fun k => ρ k)

/-- The product coordinate along a polynomial ratio jet. -/
def polynomialProductCoordinate (p m : ℕ) (ε : ℝ) : ℝ :=
  productCoordinate (fun k => ratioPerturbation (polynomialRatioJet p) ε k) m

/-- Claim 50: the logarithmic derivative of the m-th product coordinate is
exactly the finite power sum induced from the polynomial ratio jet. -/
def claim50 : Prop :=
  ∀ (p m : ℕ),
    HasDerivAt
      (fun ε : ℝ => Real.log (polynomialProductCoordinate p m ε))
      (Finset.sum (Finset.range m) (fun k => (k : ℝ) ^ p)) 0

/-- Evaluation of a finitely supported response distribution on a scalar
function of the index. -/
def responseEvaluation (D : ℕ →₀ ℝ) (f : ℕ → ℝ) : ℝ :=
  D.sum (fun k coefficient => coefficient * f k)

/-- The centered moment of order r about the terminal index n-1. -/
def centeredMoment (n r : ℕ) (D : ℕ →₀ ℝ) : ℝ :=
  D.sum (fun k coefficient =>
    coefficient * ((k : ℝ) - (n : ℝ) + 1) ^ r)

/-- A quadratic polynomial evaluated at a real coordinate. -/
def quadraticEvaluation (a b c x : ℝ) : ℝ :=
  a + b * x + c * x ^ 2

/-- Claim 57: terminal evaluation on every quadratic is equivalent to the
three centered moment identities. -/
def claim57 : Prop :=
  ∀ (n : ℕ) (D : ℕ →₀ ℝ),
    ((∀ a b c : ℝ,
        responseEvaluation D
            (fun k => quadraticEvaluation a b c (k : ℝ)) =
          quadraticEvaluation a b c ((n : ℝ) - 1)) ↔
      (centeredMoment n 0 D = 1 ∧
        centeredMoment n 1 D = 0 ∧
        centeredMoment n 2 D = 0))

end
end MathlibPlus.Open.ResearchFormalization.C0003
