import Mathlib
import MathlibPlus.Analysis.Claim7421

namespace MathlibPlus.Analysis.BernoulliSheetLaw

noncomputable section

inductive Epsilon
  | neg
  | pos
deriving DecidableEq

def epsilonValue : Epsilon → ℝ
  | Epsilon.neg => -1
  | Epsilon.pos => 1

/-- The two positive summands of the K-0010 reciprocal kernel, indexed by the
same sign used in `A_ε = ε (a - q exp (ε t))`. -/
def sheetSummand (a q t : ℝ) (ε : Epsilon) : ℝ :=
  Real.exp (epsilonValue ε * (a * t) - q * Real.exp (epsilonValue ε * t))

def sheetKernel (a q t : ℝ) : ℝ :=
  sheetSummand a q t Epsilon.neg + sheetSummand a q t Epsilon.pos

/-- The signed derivative summand named in the admitted statement. -/
def Aepsilon (a q t : ℝ) (ε : Epsilon) : ℝ :=
  epsilonValue ε * (a - q * Real.exp (epsilonValue ε * t))

def posteriorWeight (a q t : ℝ) (ε : Epsilon) : ℝ :=
  sheetSummand a q t ε / sheetKernel a q t

/-- Claim 7422: after imposing `s = sinh t`, the hyperbolic weights are the
actual posterior probabilities of the two positive summands of `K`; the
signed `A_ε` carrier is indexed by the same two-sheet sign. -/
def positiveBernoulliSheetLaw : Prop :=
  ∀ (a q t : ℝ),
    a = (5 / 4 : ℝ) →
    let s := Real.sinh t
    let z := a * t - q * s
    let K := sheetKernel a q t
    let _A := fun ε => Aepsilon a q t ε
    0 < Real.exp z / (2 * Real.cosh z) ∧
      0 < Real.exp (-z) / (2 * Real.cosh z) ∧
      Real.exp z / (2 * Real.cosh z) +
          Real.exp (-z) / (2 * Real.cosh z) = 1 ∧
      posteriorWeight a q t Epsilon.pos =
        Real.exp z / (2 * Real.cosh z) ∧
      posteriorWeight a q t Epsilon.neg =
        Real.exp (-z) / (2 * Real.cosh z) ∧
      K = Real.exp (-a * t - q * Real.exp (-t)) +
        Real.exp (a * t - q * Real.exp t)

end

end MathlibPlus.Analysis.BernoulliSheetLaw
