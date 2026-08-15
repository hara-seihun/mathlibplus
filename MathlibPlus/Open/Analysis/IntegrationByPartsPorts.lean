import Mathlib

noncomputable section

open MeasureTheory

namespace MathlibPlus.Open.Analysis.IntegrationByPartsPorts

/-- The Bernoulli polynomial `B₅`. -/
def bernoulli5 (x : ℝ) : ℝ :=
  x ^ 5 - (5 / 2 : ℝ) * x ^ 4 + (5 / 3 : ℝ) * x ^ 3 - (1 / 6 : ℝ) * x

/-- The Bernoulli polynomial `B₆`. -/
def bernoulli6 (x : ℝ) : ℝ :=
  x ^ 6 - 3 * x ^ 5 + (5 / 2 : ℝ) * x ^ 4 - (1 / 2 : ℝ) * x ^ 2 + (1 / 42 : ℝ)

/-- The Bernoulli polynomial `B₇`. -/
def bernoulli7 (x : ℝ) : ℝ :=
  x ^ 7 - (7 / 2 : ℝ) * x ^ 6 + (7 / 2 : ℝ) * x ^ 5 - (7 / 6 : ℝ) * x ^ 3 + (1 / 6 : ℝ) * x

/-- The Bernoulli polynomial `B₈`. -/
def bernoulli8 (x : ℝ) : ℝ :=
  x ^ 8 - 4 * x ^ 7 + (14 / 3 : ℝ) * x ^ 6 - (7 / 3 : ℝ) * x ^ 4 +
    (2 / 3 : ℝ) * x ^ 2 - (1 / 30 : ℝ)

/-- The Bernoulli polynomial `B₉`. -/
def bernoulli9 (x : ℝ) : ℝ :=
  x ^ 9 - (9 / 2 : ℝ) * x ^ 8 + 6 * x ^ 7 - (21 / 5 : ℝ) * x ^ 5 +
    2 * x ^ 3 - (3 / 10 : ℝ) * x

/-- The Bernoulli polynomial `B₁₀`. -/
def bernoulli10 (x : ℝ) : ℝ :=
  x ^ 10 - 5 * x ^ 9 + (15 / 2 : ℝ) * x ^ 8 - 7 * x ^ 6 + 5 * x ^ 4 -
    (1 / 2 : ℝ) * x ^ 2 + (5 / 66 : ℝ)

/-- The Bernoulli polynomial `B₁₁`. -/
def bernoulli11 (x : ℝ) : ℝ :=
  x ^ 11 - (11 / 2 : ℝ) * x ^ 10 + (55 / 6 : ℝ) * x ^ 9 - 11 * x ^ 7 +
    11 * x ^ 5 - (11 / 2 : ℝ) * x ^ 3 + (5 / 6 : ℝ) * x

/-- The centered discrepancy carrier from the admitted Bernoulli formula. -/
def beta6 (u : ℝ) : ℝ := by
  let x := Real.exp u
  let θ := Int.fract x
  exact
    -(4 / 15 : ℝ) * bernoulli5 θ / x ^ 4 +
      (8 / 9 : ℝ) * bernoulli6 θ / x ^ 5 -
      (26 / 21 : ℝ) * bernoulli7 θ / x ^ 6 +
      (11 / 12 : ℝ) * bernoulli8 θ / x ^ 7 -
      (41 / 108 : ℝ) * bernoulli9 θ / x ^ 8 +
      (1 / 12 : ℝ) * bernoulli10 θ / x ^ 9 -
      (1 / 132 : ℝ) * bernoulli11 θ / x ^ 10

/-- The discrepancy derivative carrier `h₆ = (∂ᵤ - 1) β₆`. -/
def h6 (u : ℝ) : ℝ := deriv beta6 u - beta6 u

def c6 : ℝ := 32 / 10395

def discrepancyPortIntegrand (s : ℂ) (P : Polynomial ℂ) (u : ℝ) : ℂ :=
  P.eval (u : ℂ) * (h6 u : ℂ) * Complex.exp (-(s * (u : ℂ)))

def discrepancyPort (s : ℂ) (P : Polynomial ℂ) : ℂ :=
  ∫ u in Set.Ici (0 : ℝ), discrepancyPortIntegrand s P u

def discrepancyByPartsIntegrand (s : ℂ) (P : Polynomial ℂ) (u : ℝ) : ℂ :=
  ((s - 1) * P.eval (u : ℂ) - (P.derivative).eval (u : ℂ)) *
    (beta6 u : ℂ) * Complex.exp (-(s * (u : ℂ)))

/--
Integration-by-parts discrepancy ports: for every complex polynomial `P`, the
port is the boundary term plus the discrepancy integral, and that integral is
absolutely convergent in the stated half-plane.
-/
def integrationByPartsDiscrepancyPorts : Prop :=
  ∀ (P : Polynomial ℂ) (s : ℂ),
    -4 < s.re →
      (discrepancyPort s P =
          (c6 : ℂ) * P.eval 0 +
            ∫ u in Set.Ici (0 : ℝ), discrepancyByPartsIntegrand s P u) ∧
        IntegrableOn (discrepancyByPartsIntegrand s P) (Set.Ici (0 : ℝ))

end MathlibPlus.Open.Analysis.IntegrationByPartsPorts
