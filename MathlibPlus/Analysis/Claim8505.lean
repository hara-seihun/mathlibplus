import MathlibPlus.Basic

namespace MathlibPlus.Analysis

/-- The square-root moment lift in claim 8505, with odd indices sent to zero. -/
def symmetricSquareRootMomentLift_claim8505 {R : Type*} [Zero R]
    (μ : ℕ → R) (n : ℕ) : R :=
  if n % 2 = 0 then μ (n / 2) else 0

theorem symmetricSquareRootMomentLift_even_claim8505
    {R : Type*} [Zero R] (μ : ℕ → R) (k : ℕ) :
    symmetricSquareRootMomentLift_claim8505 μ (2 * k) = μ k := by
  simp [symmetricSquareRootMomentLift_claim8505]

theorem symmetricSquareRootMomentLift_odd_claim8505
    {R : Type*} [Zero R] (μ : ℕ → R) (k : ℕ) :
    symmetricSquareRootMomentLift_claim8505 μ (2 * k + 1) = 0 := by
  simp [symmetricSquareRootMomentLift_claim8505]

end MathlibPlus.Analysis
