import Mathlib

namespace MathlibPlus.Open.Research.PochhammerCompactUniformDecay

noncomputable section

/-- The Newton/Pochhammer basis polynomial `P_k(z) = ∏_{r=1}^k (1 - z/r)`. -/
def pochhammer (k : ℕ) (z : ℂ) : ℂ :=
  Finset.prod (Finset.range k) (fun r =>
    (1 - z / ((r + 1 : ℕ) : ℂ)))

/-- On every compact set, the Pochhammer decay estimate has one implied
constant, uniformly for all points of that set. -/
def compactUniformPochhammerDecay : Prop :=
  ∀ K : Set ℂ, IsCompact K →
    ∃ C : ℝ, 0 < C ∧
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        ∀ s : ℂ, s ∈ K →
          ‖pochhammer k (s / 2)‖ ≤ C * Real.rpow (k : ℝ) (-s.re / 2)

end

end MathlibPlus.Open.Research.PochhammerCompactUniformDecay
