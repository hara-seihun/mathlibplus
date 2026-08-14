import Mathlib

namespace MathlibPlus.Open.ResearchFormalizationBatch_01a00154

/-- R-5609 S1: balanced 3+3 constant-slope rigidity. -/
def balancedThreePlusThreeConstantSlopeRigidity : Prop :=
  ∀ (p : ℕ) [Fact p.Prime],
    5 ≤ p →
      ∀ (A B : Type*)
        [AddCommGroup A] [AddCommGroup B]
        [Module (ZMod p) A] [Module (ZMod p) B]
        [Module.Finite (ZMod p) A] [Module.Finite (ZMod p) B],
        Module.finrank (ZMod p) A = 3 →
          Module.finrank (ZMod p) B = 3 →
            ∀ (n : ℕ)
              (d : Fin n → B)
              (u : Fin n → A →ₗ[ZMod p] ZMod p)
              (lambda : Fin n → ZMod p),
              (∀ i, d i ≠ 0 ∧ u i ≠ 0) →
                ∀ (s : B → A),
                  s 0 = 0 →
                    (∀ (i : Fin n) (x : B),
                      u i (s (x + d i) - s x) = lambda i) →
                      ∃ L : B →ₗ[ZMod p] A,
                        ∀ i, u i (L (d i)) = lambda i

/-- The divisor-counting function used in the candidate count. -/
def divisorCount (m : ℕ) : ℕ := (Nat.divisors m).card

/-- R-5717 S1: the candidate counting function. -/
noncomputable def candidateCount (X : ℝ) : ℕ :=
  Set.ncard {n : ℕ |
    24 < n ∧
      (n : ℝ) ≤ X ∧
        ∀ k : ℕ, 1 ≤ k → k < n → divisorCount (n - k) ≤ k + 2}

noncomputable def candidateGamma : ℝ := Real.log 2 / (1 + Real.log 2)

/-- R-5717 S1: collective medium-prime sieve bound. -/
def collectiveMediumPrimeSieveBound : Prop :=
  ∀ c : ℝ,
    0 < c →
      c < candidateGamma →
        ∃ κ : ℝ, 0 < κ ∧
          ∃ Xc : ℝ, ∀ X : ℝ, Xc ≤ X →
            (candidateCount X : ℝ) ≤
              X * Real.exp (-(κ * Real.rpow (Real.log X) c * Real.log (Real.log X)))

/-- Cubic evaluation matrix at the five specified points over F₇. -/
def cubicEvaluationMatrix : Matrix (Fin 5) (Fin 4) (ZMod 7) :=
  fun t j => (t.val : ZMod 7) ^ j.val

/-- The cubic evaluation matrix with the additional section 3 t⁴. -/
def quarticEvaluationMatrix : Matrix (Fin 5) (Fin 5) (ZMod 7) :=
  fun t j =>
    if h : j.val < 4 then
      (t.val : ZMod 7) ^ j.val
    else
      3 * (t.val : ZMod 7) ^ 4

/-- R-5760 S6: local quartic interpolation rank check. -/
def localQuarticInterpolationCheck : Prop :=
  Matrix.rank cubicEvaluationMatrix = 4 ∧
    Matrix.rank quarticEvaluationMatrix = 5 ∧
      ∀ r : Fin 5,
        Matrix.rank (quarticEvaluationMatrix.submatrix (Fin.succAbove r) id) = 4

end MathlibPlus.Open.ResearchFormalizationBatch_01a00154
