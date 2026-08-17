import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0295WebSpan

noncomputable section

open Set

/-- The two fixed rank-two web vectors from Claim 19506. -/
def wA : Fin 6 → ℝ := ![0, 1, -1, -1, 1, 0]

def wB : Fin 6 → ℝ := ![1, -1, 0, 0, -1, 1]

/-- The proposed cup/web subspace `span(w_A,w_B)`. -/
def webSpan : Submodule ℝ (Fin 6 → ℝ) :=
  Submodule.span ℝ ({wA, wB} : Set (Fin 6 → ℝ))

/-- The displayed `T₃(z)` chip image of `w_A`. -/
def tImage (z : ℝ) : Fin 6 → ℝ :=
  ![0, 1, z - 1, z - 1, (z - 1) ^ 2, z - z ^ 2]

/-- Claim 19510: the displayed chip image leaves the proposed web span for
every positive parameter. -/
def tImageNotInWebSpan_claim19510 : Prop :=
  ∀ z : ℝ, 0 < z → tImage z ∉ webSpan

end

end MathlibPlus.Open.ResearchFormalization.R0295WebSpan
