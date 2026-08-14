import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

open Filter MeasureTheory Set

noncomputable section

/-- The open critical strip used by the self-approximation formulation. -/
def openCriticalStrip : Set ℂ :=
  {s | 0 < s.re ∧ s.re < 1}

/-- Real shifts that uniformly self-approximate `riemannZeta` on `K`. -/
def zetaSelfApproximationSet (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {τ | ∀ s, s ∈ K →
    ‖riemannZeta (s + Complex.I * (τ : ℂ)) - riemannZeta s‖ < ε}

/-- Positive lower density, fixed here as a positive liminf of normalized Lebesgue measure
on initial nonnegative intervals. -/
def hasPositiveLowerDensity (A : Set ℝ) : Prop :=
  0 < liminf (fun T : ℝ => ENNReal.toReal (volume (A ∩ Icc 0 T)) / T) atTop

/-- The compact sets admitted by the formal self-approximation interface. -/
def admissibleZetaCompact (K : Set ℂ) : Prop :=
  IsCompact K ∧ IsConnected Kᶜ ∧ K ⊆ openCriticalStrip

/-- Riemann's hypothesis in the nontrivial-zero formulation. -/
def riemannHypothesis : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → s ∈ openCriticalStrip → s.re = (1 / 2 : ℝ)

/-- Claim 45010: RH is equivalent to positive-lower-density self-approximation of ζ on
all admissible compact subsets of the open critical strip. -/
def rh_iff_positive_lower_density_self_approximation : Prop :=
  riemannHypothesis ↔
    ∀ K : Set ℂ, admissibleZetaCompact K →
      ∀ ε : ℝ, 0 < ε →
        hasPositiveLowerDensity (zetaSelfApproximationSet K ε)

end

end MathlibPlus.Open.ResearchFormalization
