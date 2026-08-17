import MathlibPlus.Open.NewResearch2.O0328

namespace MathlibPlus.Open.NewResearch2.O0328

noncomputable section

/-- The arithmetic source completion `A_q(s) = ζ(s) M_q(s)`. -/
noncomputable def arithmeticCarrier (q : ℝ → ℝ) (s : ℂ) : ℂ :=
  riemannZeta s * mellinTransform q s

/-- Claim 15468: the common vanishing orders of the arithmetic source
completions in the open critical strip are exactly those of zeta. -/
def claim15468 : Prop :=
  ∀ (s₀ : ℂ),
    0 < s₀.re →
    s₀.re < 1 →
      ∀ (a R : ℝ),
        0 < a →
        a < R →
          ∀ (n : ℕ),
            ((∀ q : ℝ → ℝ,
                q ∈
                    MathlibPlus.Open.Analysis.CenterFlatCompactSourceClaim15459.centerFlatSourceClass
                      a R →
                  vanishesToOrderAtLeast (arithmeticCarrier q) s₀ n) ↔
              vanishesToOrderAtLeast riemannZeta s₀ n)

end

end MathlibPlus.Open.NewResearch2.O0328
