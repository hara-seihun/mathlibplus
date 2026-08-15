import Mathlib

namespace MathlibPlus.Open

noncomputable section

/-- The local kernel appearing in the admitted asymptotic claim. -/
def localKernel (q v : ℝ) : ℝ :=
  1 / (v * Real.log v) - 1 / ((v + Real.log q) * Real.log (v + Real.log q))

/-- The defining equation for the positive theta threshold at a prime argument. -/
def thetaThresholdEquation (q : ℕ) (t : ℝ) : Prop :=
  0 < t ∧
    Real.log (q : ℝ) =
      t * (Real.exp (Real.log t / ((q : ℝ) - 1)) - 1)

/-- The unique positive threshold supplied by the admitted threshold statement. -/
noncomputable def thetaThreshold (q : ℕ) : ℝ :=
  sInf {t : ℝ | thetaThresholdEquation q t}

/-- Big-O along the increasing prime arguments. -/
def isBigOAlongPrimes (f g : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∃ q₀ : ℕ,
      ∀ q : ℕ, Nat.Prime q → q₀ ≤ q →
        |f q| ≤ C * |g q|

/--
The local kernel asymptotic:
κ_q(T(q)) = (log q + 1) / (q² log q) + O((log q)² / q³),
as q tends to infinity through the relevant prime arguments.
-/
def localKernelAsymptotic : Prop :=
  isBigOAlongPrimes
    (fun q : ℕ =>
      localKernel (q : ℝ) (thetaThreshold q) -
        (Real.log (q : ℝ) + 1) /
          ((q : ℝ) ^ 2 * Real.log (q : ℝ)))
    (fun q : ℕ =>
      (Real.log (q : ℝ)) ^ 2 / (q : ℝ) ^ 3)

end

end MathlibPlus.Open
