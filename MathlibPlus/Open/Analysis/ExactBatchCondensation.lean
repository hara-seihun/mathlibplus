import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

def factorialScaled (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  (k.factorial : ℝ) * b k

def firstTuran (b : ℕ → ℝ) (k : ℕ) : ℝ :=
  b k ^ 2 - ((k + 1 : ℝ) / (k : ℝ)) * b (k - 1) * b (k + 1)

def factorialToeplitz3 (b : ℕ → ℝ) (k : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => factorialScaled b ((k + j.val) - i.val)

/-- Claim 11754: exact normalized double-Turán condensation, for every sequence. -/
def exactDoubleTuranCondensationClaim : Prop :=
  (∀ (b : ℕ → ℝ) (k : ℕ), 2 ≤ k →
    factorialScaled b k * Matrix.det (factorialToeplitz3 b k) =
      (k.factorial : ℝ) ^ 4 *
        (firstTuran b k ^ 2 -
          ((k + 1 : ℝ) / (k : ℝ)) ^ 2 * firstTuran b (k - 1) *
            firstTuran b (k + 1))) ∧
  (¬ (∀ (b : ℕ → ℝ) (k : ℕ), 2 ≤ k →
    factorialScaled b k * Matrix.det (factorialToeplitz3 b k) =
      (k.factorial : ℝ) ^ 4 *
        (firstTuran b k ^ 2 - firstTuran b (k - 1) * firstTuran b (k + 1))))

end MathlibPlus.Open.Analysis
