import Mathlib
import MathlibPlus.Open.Analysis.HigherPrimePowerEndpoint

open scoped BigOperators

namespace MathlibPlus.Open.Analysis

/-- The disk boundary and the positive-length boundary slit used by O-0315.
The displayed minimum data and the arc parametrization are retained explicitly. -/
def slitBoundarySetup (c : ℂ) (r σ ell : ℝ) (a b : ℂ) : Prop :=
  0 < r ∧
    0 < ell ∧
    (1 / 2 : ℝ) < σ ∧
    let D := Metric.closedBall c r
    let Γ := Metric.sphere c r
    IsCompact D ∧
      IsSimplyConnected D ∧
      D ⊆ {s : ℂ | (1 / 2 : ℝ) < s.re ∧ s.re < 1} ∧
      (∀ s ∈ Γ, riemannZeta s ≠ 0) ∧
      (∀ s ∈ Γ, σ ≤ s.re) ∧
      (∃ s ∈ Γ, s.re = σ) ∧
      (∃ (J I K : Set ℂ) (γ : ℝ → ℂ),
        ContDiffOn ℝ 1 γ (Set.Icc (0 : ℝ) 1) ∧
          Set.InjOn γ (Set.Icc (0 : ℝ) 1) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1, γ t ∈ Γ) ∧
          (∀ t ∈ Set.Icc (0 : ℝ) 1, σ ≤ (γ t).re) ∧
          J = γ '' Set.Ioo (0 : ℝ) 1 ∧
          I = closure J ∧
          K = Γ \ J ∧
          I ⊆ Γ ∧
          a ∈ Γ ∧
          b ∈ Γ ∧
          a = γ 0 ∧
          b = γ 1 ∧
          ell = ∫ t in (0 : ℝ)..1, ‖deriv γ t‖) ∧
      shortArcInHalfPlane σ ell a b

abbrev SlitPrimeLogH :=
  {g : PrimeIndex → ℂ // Summable (fun p => ‖g p‖ ^ 2)}

noncomputable def slitPrimeEndpointLambda
    (a b : ℂ) (g : SlitPrimeLogH) : ℂ :=
  ∑' p : PrimeIndex,
    g.1 p * ((p.1 : ℂ) ^ (-b) - (p.1 : ℂ) ^ (-a))

noncomputable def slitPrimeLogNorm (g : SlitPrimeLogH) : ℝ :=
  Real.sqrt (∑' p : PrimeIndex, ‖g.1 p‖ ^ 2)

noncomputable def slitPrimeEndpointVariance (a b : ℂ) : ℝ :=
  ∑' p : PrimeIndex,
    ‖(p.1 : ℂ) ^ (-b) - (p.1 : ℂ) ^ (-a)‖ ^ 2

noncomputable def slitPrimeEndpointDualNorm (a b : ℂ) : ℝ :=
  sSup {q : ℝ |
    ∃ g : SlitPrimeLogH,
      slitPrimeLogNorm g ≤ 1 ∧
        q = ‖slitPrimeEndpointLambda a b g‖}

noncomputable def slitPrimeLogInner
    (g h : SlitPrimeLogH) : ℂ :=
  ∑' p : PrimeIndex,
    g.1 p * starRingEnd ℂ (h.1 p)

/-- A Riesz representer is specified by its prime-log inner-product equation. -/
def slitPrimeIsRieszRepresenter
    (Λ : SlitPrimeLogH → ℂ) (r : SlitPrimeLogH) : Prop :=
  ∀ g : SlitPrimeLogH, Λ g = slitPrimeLogInner g r

/-- Claim 14114: the actual supremum dual norm of the endpoint functional has
quadratic size along the admitted boundary slit. -/
def claim14114EndpointVariance : Prop :=
  ∀ (c : ℂ) (r σ ell : ℝ) (a b : ℂ),
    slitBoundarySetup c r σ ell a b →
      let Γ := Metric.sphere c r
      let V_D : ℝ :=
        ∑' p : PrimeIndex,
          (Real.log (p.1 : ℝ)) ^ 2 *
            Real.rpow (p.1 : ℝ) (-2 * σ)
      Summable (fun p : PrimeIndex =>
          (Real.log (p.1 : ℝ)) ^ 2 *
            Real.rpow (p.1 : ℝ) (-2 * σ)) ∧
        (∀ p : PrimeIndex,
          ‖(p.1 : ℂ) ^ (-b) - (p.1 : ℂ) ^ (-a)‖ ≤
            ell * Real.log (p.1 : ℝ) *
              Real.rpow (p.1 : ℝ) (-σ)) ∧
        slitPrimeEndpointDualNorm a b ^ 2 =
          slitPrimeEndpointVariance a b ∧
        slitPrimeEndpointDualNorm a b ^ 2 ≤ V_D * ell ^ 2 ∧
        (∃ s ∈ Γ, s.re = σ) ∧
        (∀ s ∈ Γ, σ ≤ s.re)

/-- Claim 14116: the constrained prime-log minimum is attained by the
Riesz-representer solution, and the endpoint-debt consequence retains the
variance and `V_D` conclusions. -/
def claim14116CameronMartinCost : Prop :=
  ∀ (c : ℂ) (r σ ell c_D : ℝ) (a b : ℂ) (Δ : ℂ),
    0 < c_D →
      slitBoundarySetup c r σ ell a b →
        let V_D : ℝ :=
          ∑' p : PrimeIndex,
            (Real.log (p.1 : ℝ)) ^ 2 *
              Real.rpow (p.1 : ℝ) (-2 * σ)
        let Λ : SlitPrimeLogH → ℂ := slitPrimeEndpointLambda a b
        let variance : ℝ := slitPrimeEndpointVariance a b
        (Summable (fun p : PrimeIndex =>
            (Real.log (p.1 : ℝ)) ^ 2 *
              Real.rpow (p.1 : ℝ) (-2 * σ)) ∧
          0 < variance ∧
          0 < V_D ∧
          variance ≤ V_D * ell ^ 2 ∧
          ∃ g₀ : SlitPrimeLogH,
            (∃ representer : SlitPrimeLogH,
              slitPrimeIsRieszRepresenter Λ representer ∧
                (∀ p : PrimeIndex,
                  g₀.1 p =
                    (Δ / (variance : ℂ)) * representer.1 p)) ∧
            Λ g₀ = Δ ∧
              slitPrimeLogNorm g₀ ^ 2 = ‖Δ‖ ^ 2 / variance ∧
              (∀ g : SlitPrimeLogH, Λ g = Δ →
                ‖Δ‖ ^ 2 / variance ≤ slitPrimeLogNorm g ^ 2) ∧
          (∀ g : SlitPrimeLogH,
            c_D ≤ ‖Λ g‖ →
              c_D ^ 2 / (V_D * ell ^ 2) ≤ slitPrimeLogNorm g ^ 2))

/-- Claim 14117: the higher-prime-power remainder has the asserted uniform
linear endpoint variation on the admitted boundary slit. -/
def claim14117HigherPrimePowerEndpointBound : Prop :=
  ∀ (c : ℂ) (r σ ell : ℝ) (a b : ℂ),
    slitBoundarySetup c r σ ell a b →
      let W_D := higherPrimePowerWeight σ
      Summable (fun p : PrimeIndex => higherPrimePowerWeightTerm σ p) ∧
        ∀ ω : PrimeIndex → UnitPhase,
          ‖higherPrimePowerRemainder ω b -
              higherPrimePowerRemainder ω a‖ ≤ W_D * ell

end MathlibPlus.Open.Analysis
