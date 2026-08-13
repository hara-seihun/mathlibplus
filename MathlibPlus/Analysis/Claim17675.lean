import Mathlib

namespace MathlibPlus.Analysis.Claim17675

/-!
# Strict positivity of oriented edge weights

The packet's phrase "in the orientation used by the triangular sum" is
represented by the explicit hypotheses `θ s < θ r` and positive endpoint
weights.  The conclusion is the displayed edge-weight positivity; no further
triangular-kernel or boundary-weight assertion is added.
-/

/-- Claim 17675: an oriented edge weight
`w_{r,s} = d_r d_s (θ_r - θ_s)` is strictly positive. -/
theorem orientedEdgeWeight_pos
    {m : ℕ} (d θ : Fin m → ℝ) (r s : Fin m)
    (hd_r : 0 < d r) (hd_s : 0 < d s) (hθ : θ s < θ r) :
    let w_rs := d r * d s * (θ r - θ s)
    0 < w_rs := by
  dsimp
  have hdiff : 0 < θ r - θ s := sub_pos.mpr hθ
  positivity

end MathlibPlus.Analysis.Claim17675
