import MathlibPlus.Open.Analysis.GammaReadout

namespace MathlibPlus.Open.Analysis

open scoped Interval BigOperators

noncomputable def gammaRemainder50167 (m : ℕ) (q L : ℝ) : ℂ :=
  iteratedDeriv m (gammaG q) 0 -
    ∫ v in Set.Ioc (0 : ℝ) L,
      (Real.exp (-v) : ℂ) * gammaPhi m q (v : ℂ)

noncomputable def gammaCellWeight50167 (n : ℕ) (x : ℝ) : ℝ :=
  (x - (n : ℝ)) * Real.rpow x (-(3 / 2 : ℝ))

noncomputable def gammaCellCutoff50167 (n : ℕ) (M : ℝ) : ℝ :=
  M * Real.pi * ((n : ℝ) + 1) ^ 2

/-- Claim 50167: the cell weights are summable and the remainder sum has the
stated order in the real cutoff parameter. -/
def claim50167 : Prop :=
  ∀ j : ℕ,
    (∀ n : {n : ℕ // 1 ≤ n},
      ∫ x in Set.Ioc (n.1 : ℝ) ((n.1 : ℝ) + 1),
          gammaCellWeight50167 n.1 x ≤
            (1 / 2 : ℝ) * Real.rpow (n.1 : ℝ) (-(3 / 2 : ℝ))) ∧
    Summable (fun n : {n : ℕ // 1 ≤ n} =>
      Real.rpow (n.1 : ℝ) (-(3 / 2 : ℝ)) *
        (1 + Real.log (n.1 : ℝ)) ^ (2 * j)) ∧
    Asymptotics.IsBigO Filter.atTop
      (fun M : ℝ =>
        ∑' n : {n : ℕ // 1 ≤ n},
          ∫ x in Set.Ioc (n.1 : ℝ) ((n.1 : ℝ) + 1),
            gammaCellWeight50167 n.1 x *
              ‖gammaRemainder50167 (2 * j)
                  ((Real.pi * x ^ 2)⁻¹) (gammaCellCutoff50167 n.1 M)‖)
      (fun M : ℝ =>
        Real.rpow M (-(5 / 4 : ℝ)) *
          (1 + Real.log M) ^ (2 * j))

end MathlibPlus.Open.Analysis
