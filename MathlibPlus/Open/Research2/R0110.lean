import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.Research2.R0110

private noncomputable def mellinIntervalTerm (n : ℕ) (s : ℂ) : ℂ :=
  (Complex.cpow ((n + 1 : ℕ) : ℂ) (1 - s) -
      Complex.cpow (n : ℂ) (1 - s)) / (1 - s) +
    (n : ℂ) / s *
      (Complex.cpow ((n + 1 : ℕ) : ℂ) (-s) -
        Complex.cpow (n : ℂ) (-s))

/-- The Hurwitz value at the integer successor `M+1`, written using the
standard meromorphic Hurwitz/Riemann zeta and its exact finite prefix. -/
private noncomputable def hurwitzZetaSuccessor (M : ℕ) (s : ℂ) : ℂ :=
  HurwitzZeta.hurwitzZeta (0 : UnitAddCircle) s -
    ∑ k ∈ Finset.range M,
      Complex.cpow ((k + 1 : ℕ) : ℂ) (-s)

/-- Exact Hurwitz-zeta tail on the stated conditional convergence domain. -/
def exact_hurwitz_zeta_tail : Prop :=
  ∀ (M : ℕ) (s : ℂ),
    1 ≤ M →
    s ≠ 0 →
    s ≠ 1 →
    Summable (fun n : ℕ =>
      if M ≤ n then mellinIntervalTerm n s else 0) →
    (∑' n : ℕ, if M ≤ n then mellinIntervalTerm n s else 0) =
      Complex.cpow (M : ℂ) (1 - s) / (s * (s - 1)) -
        hurwitzZetaSuccessor M s / s

end MathlibPlus.Open.Research2.R0110
