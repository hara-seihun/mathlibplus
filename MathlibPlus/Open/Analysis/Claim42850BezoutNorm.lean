import Mathlib

namespace MathlibPlus.Open.Analysis.Claim42850

/-- Exact pointwise two-channel Bézout norm bound. -/
def claim42850_twoChannelBezoutNorm : Prop :=
  ∀ (A B H J : ℂ),
    A * H + B * J = 1 →
    1 ≤ max ‖A‖ ‖B‖ * (‖H‖ + ‖J‖)

end MathlibPlus.Open.Analysis.Claim42850
