import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0031

def firstEdgeSaddleEquation (n : ℕ) (u : ℝ) : Prop :=
  0 < u ∧ 2 * (n : ℝ) / u + 1 / 2 = 2 * Real.pi * Real.exp (2 * u)

def claim_17334_uniqueFirstEdgeSaddle : Prop :=
  ∀ n : ℕ, 0 < n → ∃! u : ℝ, firstEdgeSaddleEquation n u

noncomputable def firstEdgeSaddle (n : ℕ) : ℝ := by
  classical
  exact if h : ∃! u : ℝ, firstEdgeSaddleEquation n u then Classical.choose h else 0

noncomputable def positiveLambertW (x : ℝ) : ℝ :=
  sInf {w : ℝ | 0 ≤ w ∧ w * Real.exp w = x}

def claim_17335_lambertWSaddleAsymptotic : Prop :=
  (∀ n : ℕ, 0 < n → ∃! u : ℝ, firstEdgeSaddleEquation n u) ∧
    Asymptotics.IsEquivalent Filter.atTop firstEdgeSaddle
      (fun n : ℕ => (1 / 2 : ℝ) * positiveLambertW (2 * (n : ℝ) / Real.pi))

end MathlibPlus.Open.ResearchFormalization.R0031
