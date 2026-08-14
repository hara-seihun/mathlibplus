import Mathlib

namespace MathlibPlus.Open.NumberTheory.AdmittedIntervalCovariance

open scoped BigOperators Topology
noncomputable section

/-- The terminal residue interval of length N modulo d. -/
def terminalIndicator (d N t : ℕ) : ℝ :=
  if t % d ≥ d - N % d then 1 else 0

def multipleCount (d N t : ℕ) : ℕ :=
  ((Finset.Icc (t + 1) (t + N)).filter (fun m => m % d = 0)).card

def centeredRemainder (d N t : ℕ) : ℝ :=
  (multipleCount d N t : ℝ) - (N : ℝ) / (d : ℝ)

def terminalResidueSet (d N : ℕ) : Finset (Fin d) :=
  Finset.univ.filter (fun r => r.val ≥ d - N % d)

def terminalClassCount (d N g : ℕ) (c : Fin g) : ℕ :=
  (terminalResidueSet d N).filter (fun r => r.val % g = c.val) |>.card

def intervalDeviation (d N g : ℕ) (c : Fin g) : ℝ :=
  (terminalClassCount d N g c : ℝ) - (N % d : ℝ) / (g : ℝ)

def commonPeriodAverage (d e N : ℕ) : ℝ :=
  let L := Nat.lcm d e
  (∑ t : Fin L, centeredRemainder d N t.val * centeredRemainder e N t.val) /
    (L : ℝ)

def realHarmonic (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun k => 1 / ((k + 1 : ℕ) : ℝ))

def zetaThree : ℝ :=
  ∑' n : ℕ, 1 / (((n + 1 : ℕ) : ℝ) ^ 3)

/-- Claim 35917: the interval count has its floor value or its floor value
plus one, and its centered error is the terminal residue indicator minus the
fractional part b_d/d. -/
def centeredTerminalIntervalRepresentation_claim35917 : Prop :=
  ∀ (d N t : ℕ), 0 < d →
    let b := N % d
    (multipleCount d N t = N / d ∨ multipleCount d N t = N / d + 1) ∧
      centeredRemainder d N t =
        terminalIndicator d N t - (b : ℝ) / (d : ℝ)

/-- Claim 35919: the exact gcd covariance formula, including the zero-sum and
unit-bound properties of the class deviations. -/
def exactCovarianceKernel_claim35919 : Prop :=
  ∀ (d e N : ℕ), 0 < d → 0 < e →
    let g := Nat.gcd d e
    (∑ c : Fin g, intervalDeviation d N g c = 0) ∧
    (∑ c : Fin g, intervalDeviation e N g c = 0) ∧
    (∀ c : Fin g, |intervalDeviation d N g c| < 1 ∧
      |intervalDeviation e N g c| < 1) ∧
    commonPeriodAverage d e N =
      ((g : ℝ) / ((d : ℝ) * (e : ℝ))) *
        ∑ c : Fin g, intervalDeviation d N g c * intervalDeviation e N g c ∧
    |commonPeriodAverage d e N| ≤
      (g : ℝ) ^ 2 / ((d : ℝ) * (e : ℝ))

/-- Claim 35920: coprime moduli are exactly orthogonal under the common-period
average. -/
def coprimeModuliOrthogonality_claim35920 : Prop :=
  ∀ (d e N : ℕ), 0 < d → 0 < e → Nat.Coprime d e →
    commonPeriodAverage d e N = 0

/-- Claim 35922: the gcd-kernel sum and its harmonic-number evaluation, with
all sums indexed by positive integers through the displayed n+1 reindexing. -/
def harmonicGcdKernelEvaluation_claim35922 : Prop :=
  (∑' a : ℕ, ∑' b : ℕ,
      (1 : ℝ) /
        (((a + 1 : ℕ) : ℝ) * ((b + 1 : ℕ) : ℝ) *
          ((max (a + 1) (b + 1) : ℕ) : ℝ))) =
      3 * zetaThree ∧
    (∑' n : ℕ, realHarmonic (n + 1) /
      (((n + 1 : ℕ) : ℝ) ^ 2)) = 2 * zetaThree ∧
    2 * (∑' n : ℕ, realHarmonic (n + 1) /
      (((n + 1 : ℕ) : ℝ) ^ 2)) - zetaThree = 3 * zetaThree

end
end MathlibPlus.Open.NumberTheory.AdmittedIntervalCovariance
