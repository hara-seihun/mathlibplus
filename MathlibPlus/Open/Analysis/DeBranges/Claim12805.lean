import MathlibPlus.Open.Analysis.DeBranges.FiniteRealRootedVariation

namespace MathlibPlus.Open.Analysis.DeBranges.Claim12805

noncomputable section

/-- The Gram-inverse kernel reproduces every polynomial in the finite
real-rooted shifted-polynomial de Branges model. -/
def claim12805 : Prop :=
  ∀ (n : ℕ) (c : ℂ) (roots : Fin n → ℝ),
    0 < n → c ≠ 0 →
      ∀ ω : ℝ, 0 < ω →
        ∀ (a : Fin n → ℂ) (w : ℂ),
          let f : ℂ → ℂ := fun z =>
            ∑ i : Fin n, a i *
              MathlibPlus.Open.Analysis.DeBranges.finiteComplexVector n z i
          (∫ x : ℝ,
              f (x : ℂ) *
                star (MathlibPlus.Open.Analysis.DeBranges.finiteKernel
                  n c roots ω w (x : ℂ)) *
                (MathlibPlus.Open.Analysis.DeBranges.finiteWeight
                  n c roots ω x : ℂ)) =
            f w

end

end MathlibPlus.Open.Analysis.DeBranges.Claim12805
