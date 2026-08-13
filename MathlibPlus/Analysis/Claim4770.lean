import Mathlib

namespace MathlibPlus.Analysis.Claim4770

/-- The affine Stokes-amplitude pencil from claim 4770. -/
def amplitudePencil (KPlus A : ℕ → ℝ) (N : ℕ) (τ : ℝ) : ℝ :=
  KPlus N - τ * A N

/-- The flat-cap endpoint of the amplitude pencil is the plus endpoint. -/
theorem amplitudePencil_zero_claim4770 (KPlus A : ℕ → ℝ) (N : ℕ) :
    amplitudePencil KPlus A N 0 = KPlus N := by
  simp [amplitudePencil]

/-- With `A_N = K_N⁺ - K_N`, the modular endpoint of the pencil is `K_N`. -/
theorem amplitudePencil_one_claim4770 (KPlus K A : ℕ → ℝ) (N : ℕ)
    (hA : ∀ N, A N = KPlus N - K N) :
    amplitudePencil KPlus A N 1 = K N := by
  simp [amplitudePencil, hA]

end MathlibPlus.Analysis.Claim4770
