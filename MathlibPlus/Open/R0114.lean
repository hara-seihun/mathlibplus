import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.R0114

private noncomputable def mellinIntervalTerm (n : ℕ) (s : ℝ) : ℝ :=
  (Real.rpow ((n + 1 : ℕ) : ℝ) (1 - s) -
      Real.rpow (n : ℝ) (1 - s)) / (1 - s) +
    (n : ℝ) / s *
      (Real.rpow ((n + 1 : ℕ) : ℝ) (-s) -
        Real.rpow (n : ℝ) (-s))

private noncomputable def hurwitzZetaSuccessor (M : ℕ) (s : ℝ) : ℝ :=
  (HurwitzZeta.hurwitzZeta (0 : UnitAddCircle) (s : ℂ)).re -
    ∑ k ∈ Finset.range M,
      Real.rpow ((k + 1 : ℕ) : ℝ) (-s)

private noncomputable def tailFunction (M : ℕ) (s : ℝ) : ℝ :=
  Real.rpow (M : ℝ) (1 - s) / (s * (s - 1)) -
    hurwitzZetaSuccessor M s / s

private noncomputable def completionFactor (s : ℝ) : ℝ :=
  s * (1 - s) * Real.rpow Real.pi (-s / 2) * Real.Gamma (1 + s / 2)

private noncomputable def tailJet {r : ℕ}
    (rows : Fin r → ℕ) (s₀ : ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j =>
    iteratedDeriv j.1 (tailFunction (rows i)) s₀

private noncomputable def completedTailJet {r : ℕ}
    (rows : Fin r → ℕ) (s₀ : ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun i j =>
    iteratedDeriv j.1
      (fun s : ℝ => completionFactor s * tailFunction (rows i) s) s₀

private noncomputable def orientedMinor {r : ℕ}
    (rows : Fin r → ℕ) (s₀ : ℝ) : ℝ :=
  ((-1 : ℝ) ^ Nat.choose r 2) * Matrix.det (tailJet rows s₀)

private noncomputable def orientedCompletedMinor {r : ℕ}
    (rows : Fin r → ℕ) (s₀ : ℝ) : ℝ :=
  ((-1 : ℝ) ^ Nat.choose r 2) * Matrix.det (completedTailJet rows s₀)

/-- Completion preserves every strict orientation of an exact confluent tail
minor at the midpoint.  The `ContDiffAt` and summability clauses are the
analytic domain of the osculating tail, rather than an unconstrained jet. -/
def claim_18047 : Prop :=
  0 < completionFactor (1 / 2 : ℝ) ∧
    ∀ (r : ℕ) (rows : Fin r → ℕ),
      StrictMono rows →
      (∀ i, 1 ≤ rows i) →
      (∀ i, Summable (fun n : ℕ =>
        if rows i ≤ n then mellinIntervalTerm n (1 / 2 : ℝ) else 0)) →
      (∀ i, ContDiffAt ℝ r (tailFunction (rows i)) (1 / 2 : ℝ)) →
      0 < orientedMinor rows (1 / 2 : ℝ) →
      0 < orientedCompletedMinor rows (1 / 2 : ℝ)

end MathlibPlus.Open.R0114
