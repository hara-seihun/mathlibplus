import MathlibPlus.NumberTheory.CompletedZetaRadial

namespace MathlibPlus.Open.NumberTheory.OffModularZerosClaim17169

open MathlibPlus.NumberTheory.CompletedZetaRadial

/-- Claim 17169: once the source-specific base boundary function is tied to
xi on the negative-axis parametrization, every non-modular affine shift has
only finitely many negative-real zeros. -/
def offModularNegativeAxisZeros_claim17169 (Hhalf : ℂ → ℂ) : Prop :=
  (∀ t : ℝ,
    Hhalf (-(t : ℂ)^2) =
      riemannXi ((1 / 2 : ℂ) + (t : ℂ) * Complex.I)) →
    ∀ c : ℝ, c ≠ 1 / 2 →
      let Hc : ℂ → ℂ :=
        fun w => Hhalf w + ((c : ℂ) - (1 / 2 : ℂ))
      Set.Finite {w : ℂ |
        Hc w = 0 ∧ w.im = 0 ∧ w.re < 0}

end MathlibPlus.Open.NumberTheory.OffModularZerosClaim17169
