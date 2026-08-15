import Mathlib

namespace MathlibPlus.Open.Analysis

noncomputable section

/--
The exact saddle equation and the two asymptotic assertions for the positive
saddle sequence.  The local definition of `W0` is the principal real branch,
characterized on the nonnegative inputs used here as the nonnegative solution
of `y * exp y = x`.
-/
def exactSaddleEquationAndLambertAsymptotic_claim9034 : Prop :=
  ∀ (u : ℕ → ℝ),
    (∀ n : ℕ, 0 < n →
      0 < u n ∧
        2 * (n : ℝ) / u n + (1 / 2 : ℝ) =
          2 * Real.pi * Real.exp (2 * u n)) →
      let W0 : ℝ → ℝ :=
        fun x => sInf {y : ℝ | 0 ≤ y ∧ y * Real.exp y = x}
      let wtilde : ℕ → ℝ := fun n => 2 * u n
      (∀ n : ℕ, 0 < n →
        Real.pi * wtilde n * Real.exp (wtilde n) =
          2 * (n : ℝ) + wtilde n / 4) ∧
        Asymptotics.IsLittleO Filter.atTop
          (fun n => wtilde n - W0 (2 * (n : ℝ) / Real.pi))
          (fun _ => (1 : ℝ)) ∧
        Asymptotics.IsLittleO Filter.atTop
          (fun n =>
            u n / ((1 / 2 : ℝ) * W0 (2 * (n : ℝ) / Real.pi)) - 1)
          (fun _ => (1 : ℝ))

end
end MathlibPlus.Open.Analysis
