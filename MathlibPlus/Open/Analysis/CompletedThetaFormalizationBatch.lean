import Mathlib

namespace MathlibPlus.Open.Analysis.CompletedThetaFormalizationBatch

noncomputable def completedThetaKernel (u : ℝ) : ℝ :=
  ∑' n : {n : ℕ // 0 < n},
    (4 * Real.pi ^ 2 * (n.1 : ℝ) ^ 4 * Real.exp ((9 / 2 : ℝ) * u)
      - 6 * Real.pi * (n.1 : ℝ) ^ 2 * Real.exp ((5 / 2 : ℝ) * u)) *
      Real.exp (-Real.pi * (n.1 : ℝ) ^ 2 * Real.exp (2 * u))

noncomputable def completedThetaCoefficient (m : ℤ) : ℝ :=
  if m < 0 then
    0
  else
    (2 : ℝ) / (Nat.factorial (2 * Int.toNat m) : ℝ) *
      ∫ u in Set.Ioi (0 : ℝ),
        completedThetaKernel u * u ^ (2 * Int.toNat m)

open scoped Interval

def integrationByPartsShiftAndStructuralZeros : Prop :=
  (∀ m : ℤ, m < 0 → completedThetaCoefficient m = 0) ∧
  (∀ N i : ℕ,
    completedThetaCoefficient (Int.ofNat N - Int.ofNat i) =
      (2 : ℝ) / (Nat.factorial (2 * N) : ℝ) *
        ∫ u in Set.Ioi (0 : ℝ),
          iteratedDeriv (2 * i) completedThetaKernel u * u ^ (2 * N)) ∧
  (∀ N : ℕ, ∀ u : ℝ,
    iteratedDeriv (2 * N + 1) (fun x : ℝ => x ^ (2 * N)) u = 0) ∧
  Even completedThetaKernel ∧
  (∀ N i : ℕ, N < i →
    iteratedDeriv (2 * i - 2 * N - 1) completedThetaKernel 0 = 0)

end MathlibPlus.Open.Analysis.CompletedThetaFormalizationBatch
