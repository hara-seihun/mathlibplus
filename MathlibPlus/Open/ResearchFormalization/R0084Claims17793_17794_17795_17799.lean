import Mathlib
import MathlibPlus.Open.ResearchFormalization.ReciprocalCells

open scoped BigOperators
open MeasureTheory Set

namespace MathlibPlus.Open.ResearchFormalization.R0084Claims17793_17794_17795_17799

noncomputable section

def cellIntegralComplex (n : ℕ) (s : ℂ) : ℂ :=
  ∫ x in (n : ℝ)..(n + 1 : ℝ),
    ((x - (n : ℝ) : ℝ) : ℂ) *
      (x : ℂ) ^ (-s - 1)

def cellIntegralReal (n : ℕ) (s : ℝ) : ℝ :=
  ∫ x in (n : ℝ)..(n + 1 : ℝ),
    (x - (n : ℝ)) * Real.rpow x (-s - 1)

def cellIntegralComplexDerivativeIntegrand
    (n k : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  ((x - (n : ℝ) : ℝ) : ℂ) *
    (-Complex.log (x : ℂ)) ^ k *
      (x : ℂ) ^ (-s - 1)

/-- Claim 17793: each positive cell gives an entire function of the complex
Mellin parameter, with differentiation under the cell integral at every order. -/
def claim17793 : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    Differentiable ℂ (cellIntegralComplex n) ∧
      (∀ (k : ℕ) (s : ℂ),
        iteratedDeriv k (cellIntegralComplex n) s =
          ∫ x in (n : ℝ)..(n + 1 : ℝ),
            cellIntegralComplexDerivativeIntegrand n k s x)

def strictPositiveCellMellinMinors : Prop :=
  ∀ (r : ℕ) (n : Fin r → ℕ) (s : Fin r → ℝ),
    1 ≤ r →
      (∀ i : Fin r, 1 ≤ n i) →
        StrictMono n →
          StrictMono s →
            (-1 : ℝ) ^ (r * (r - 1) / 2) *
                Matrix.det (fun i j => cellIntegralReal (n i) (s j)) > 0

/-- Claim 17794: the checkerboard determinant sign holds for every finite
strictly ordered positive-cell row set and every strictly ordered real column
parameter tuple. -/
def claim17794 : Prop :=
  strictPositiveCellMellinMinors

/-- Claim 17795: the positive-cell Mellin scattering matrix is strictly
sign-regular at every finite order, including nonconsecutive rows. -/
def claim17795 : Prop :=
  strictPositiveCellMellinMinors

def reciprocalVacuumIntegrand (s : ℂ) (y : ℝ) : ℂ :=
  ((Int.fract (1 / y) : ℝ) : ℂ) * (y : ℂ) ^ (-s)

/-- Claim 17799: under absolute convergence of both sides, summing the
reciprocal positive cells gives the fractional-part vacuum integral. -/
def claim17799 : Prop :=
  ∀ s : ℂ,
    Summable (fun n : {n : ℕ // 1 ≤ n} =>
      ‖cellIntegralComplex n (1 - s)‖) →
      IntegrableOn (reciprocalVacuumIntegrand s)
        (Set.Ioc (0 : ℝ) 1) →
        ∑' n : {n : ℕ // 1 ≤ n}, cellIntegralComplex n (1 - s) =
          ∫ y in Set.Ioc (0 : ℝ) 1,
            reciprocalVacuumIntegrand s y

end

end MathlibPlus.Open.ResearchFormalization.R0084Claims17793_17794_17795_17799
