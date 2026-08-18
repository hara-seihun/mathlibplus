import MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias15424

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias15418

open MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias

/-- Claim 15418: the exact rescaling data and the resulting Poisson kernel
identity, including its finite-support vanishing range. -/
def claim15418_exactRescaledPoissonIdentity : Prop :=
  ∀ (L : ℝ) (q : ℝ → ℝ),
    let lam : ℝ := Real.exp L
    (Function.Even q ∧
        (∫ t : ℝ, q t) = 0 ∧
        Function.support q ⊆ Set.Icc (-lam) lam ∧
        q (-lam) = 0 ∧
        q lam = 0) →
      let p : ℝ → ℝ := fun u => Real.sqrt lam * q (lam * u)
      let c : ℝ := lam
      (∀ u : ℝ, p u = Real.sqrt lam * q (lam * u)) ∧
        c = lam ∧
        (∀ x : ℝ,
          poissonKernel q x =
            -((q 0 / 2 : ℝ) : ℂ) * Complex.exp (x / 2) +
              Complex.exp (-x / 2) *
                ∑' n : {n : ℕ // 1 ≤ n},
                  poissonFourierTransform q
                    ((n.1 : ℝ) * Real.exp (-x))) ∧
        (∀ x : ℝ, L ≤ x → poissonKernel q x = 0)

end MathlibPlus.Open.ResearchFormalization.O0326PoissonAlias15418
