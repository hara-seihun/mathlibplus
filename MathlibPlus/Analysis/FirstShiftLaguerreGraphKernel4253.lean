import MathlibPlus.Open.Analysis.BatchC0304

open scoped BigOperators

namespace MathlibPlus.Analysis.FirstShiftLaguerreGraphKernel4253

noncomputable section

private def associatedLaguerreTwo4253 (d : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (d + 1),
    (-1 : ℝ) ^ k * (Nat.choose (d + 2) (d - k) : ℝ) * t ^ k /
      (Nat.factorial k : ℝ)

private def firstShiftLaguerreVector4253 (n : ℕ) (t : ℝ) : ℝ :=
  if 2 ≤ n then associatedLaguerreTwo4253 (n - 2) t else 0

private def poissonWeight4253 (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-x) * x ^ n / (Nat.factorial n : ℝ)

/-- Claim 4253: the first-shift Laguerre graph Gram kernel. -/
noncomputable def firstShiftGraphKernel4253 (x t s : ℝ) : ℝ :=
  ∑' n : ℕ, poissonWeight4253 x n *
    (firstShiftLaguerreVector4253 n t * firstShiftLaguerreVector4253 n s +
      firstShiftLaguerreVector4253 (n + 1) t * firstShiftLaguerreVector4253 (n + 1) s)

end

end MathlibPlus.Analysis.FirstShiftLaguerreGraphKernel4253
