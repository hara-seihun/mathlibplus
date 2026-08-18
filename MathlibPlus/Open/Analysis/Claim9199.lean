import MathlibPlus.Open.Analysis.LocalKernelAsymptotic

namespace MathlibPlus.Open.Analysis.Claim9199

noncomputable section

/-- The first displayed equation in the admitted next-prime threshold claim. -/
def thetaThresholdFirstEquation (q : ℕ) (t : ℝ) : Prop :=
  Real.log (q : ℝ) =
    t * (Real.exp (Real.log t / ((q : ℝ) - 1)) - 1)

/-- The logarithmic equivalent form in the admitted next-prime threshold claim. -/
def thetaThresholdEquivalentEquation (q : ℕ) (t : ℝ) : Prop :=
  Real.log (t + Real.log (q : ℝ)) / Real.log t =
    (q : ℝ) / ((q : ℝ) - 1)

/-- Claim 9199: the positive solution of the first equation is unique, and
that equation is equivalent to the displayed logarithmic form on positive
arguments. -/
def claim9199 : Prop :=
  ∀ q : ℕ, Nat.Prime q →
    let T : ℝ := MathlibPlus.Open.thetaThreshold q
    0 < T ∧
      thetaThresholdFirstEquation q T ∧
      (∀ t : ℝ, 0 < t → thetaThresholdFirstEquation q t → t = T) ∧
      (∀ t : ℝ, 0 < t →
        (thetaThresholdFirstEquation q t ↔ thetaThresholdEquivalentEquation q t))

end

end MathlibPlus.Open.Analysis.Claim9199
