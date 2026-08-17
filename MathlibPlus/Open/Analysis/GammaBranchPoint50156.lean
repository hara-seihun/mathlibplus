import MathlibPlus.Open.Analysis.GammaReadout

namespace MathlibPlus.Open.Analysis

noncomputable section

open Filter MeasureTheory

/-- The positive-axis parameter `q=(pi*x^2)^(-1)` in Claim 50156. -/
def gammaQOfX50156 (x : ℝ) : ℝ :=
  (Real.pi * x ^ 2)⁻¹

/-- The affine branch point of the closed moment EGF. -/
def gammaFirstBranchPoint50156 (q : ℝ) : ℝ :=
  -q⁻¹

/-- The moment EGF (7), with its principal `Complex.cpow` branch supplied by
`gammaNhatClosed`. -/
def gammaMomentEgf50156 (q : ℝ) (u : ℂ) : ℂ :=
  gammaNhatClosed q u

/-- The principal upper boundary value of the negative-cut power. -/
def gammaPrincipalUpper50156 (s : ℝ) : ℂ :=
  (Real.rpow s (-5 / 4 : ℝ) : ℂ) *
    Complex.exp (((-(5 : ℝ) * Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- The principal lower boundary value of the negative-cut power. -/
def gammaPrincipalLower50156 (s : ℝ) : ℂ :=
  (Real.rpow s (-5 / 4 : ℝ) : ℂ) *
    Complex.exp ((((5 : ℝ) * Real.pi / 4 : ℝ) : ℂ) * Complex.I)

/-- The principal branch factor in the moment EGF. -/
def gammaBranchPower50156 (q : ℝ) (u : ℂ) : ℂ :=
  Complex.cpow (1 + (q : ℂ) * u) (-(gammaShape : ℂ))

/-- The primitive appearing in the displayed derivative identity (16). -/
def gammaBranchPrimitive50156 (q : ℝ) (u : ℂ) : ℂ :=
  Complex.cpow (1 + (q : ℂ) * u) ((-1 / 4 : ℝ) : ℂ)

/-- Claim 50156: the first branch point of the moment EGF, its negative-cut
boundary jump and non-integrability, and the principal-branch derivative
identity are all retained. -/
def claim50156 : Prop :=
  ∀ (x : ℝ) (n : ℕ),
    (n : ℝ) < x → x < (n : ℝ) + 1 →
      let q : ℝ := gammaQOfX50156 x
      let uStar : ℝ := gammaFirstBranchPoint50156 q
      uStar = -1 / q ∧
        uStar = -Real.pi * x ^ 2 ∧
        (1 : ℂ) + (q : ℂ) * (uStar : ℂ) = 0 ∧
        uStar ∈
          Set.Ioo (-Real.pi * ((n : ℝ) + 1) ^ 2)
            (-Real.pi * (n : ℝ) ^ 2) ∧
        (∀ (u : ℝ), u < -q⁻¹ →
          let s : ℝ := -(1 + q * u)
          0 < s ∧
            Filter.Tendsto
              (fun ε : ℝ =>
                Complex.cpow ((-s : ℂ) + (ε : ℂ) * Complex.I)
                  (-(gammaShape : ℂ)))
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (gammaPrincipalUpper50156 s)) ∧
            Filter.Tendsto
              (fun ε : ℝ =>
                Complex.cpow ((-s : ℂ) - (ε : ℂ) * Complex.I)
                  (-(gammaShape : ℂ)))
              (nhdsWithin 0 (Set.Ioi 0))
              (nhds (gammaPrincipalLower50156 s)) ∧
            ‖gammaPrincipalUpper50156 s - gammaPrincipalLower50156 s‖ =
              Real.sqrt 2 * Real.rpow s (-5 / 4 : ℝ)) ∧
        ¬ IntegrableOn
          (fun s : ℝ =>
            ‖gammaPrincipalUpper50156 s - gammaPrincipalLower50156 s‖)
          (Set.Ioo (0 : ℝ) 1) ∧
        (∀ (u : ℂ),
          (1 : ℂ) + (q : ℂ) * u ∈ Complex.slitPlane →
            gammaBranchPower50156 q u =
              ((-4 : ℂ) / (q : ℂ)) *
                deriv (gammaBranchPrimitive50156 q) u)

end

end MathlibPlus.Open.Analysis
