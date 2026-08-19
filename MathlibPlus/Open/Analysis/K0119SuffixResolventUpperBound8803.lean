import MathlibPlus.Open.Analysis.JacobiChain

namespace MathlibPlus.Open.Analysis.K0119

/-- The Catalan upper bound for a suffix endpoint resolvent. -/
def suffixDiagonalResolventUpperBound8803 : Prop :=
  ∀ (N : ℕ) (a : Fin (N + 1) → ℝ) (lam : ℝ) (j : ℕ)
    (H : Matrix (Fin (N - j)) (Fin (N - j)) ℝ)
    (A : Fin (N + 1) → ℝ),
    ∀ (h₁ : 1 ≤ j) (hj : j < N),
      a 0 = 0 →
      a (Fin.last N) = 0 →
      (∀ q : Fin (N + 1), 1 ≤ q.1 → q.1 < N → 0 < a q) →
      H = suffixBlock N a j hj →
      A ⟨j + 1, Nat.succ_lt_succ hj⟩ =
        edgeEnvelope N a ⟨j + 1, Nat.succ_lt_succ hj⟩ →
      A (Fin.last N) = 0 →
      0 < lam →
      lam > 2 * A ⟨j + 1, Nat.succ_lt_succ hj⟩ →
      ∃ R : Matrix (Fin (N - j)) (Fin (N - j)) ℝ,
        isTwoSidedInverse
            (lam • (1 : Matrix (Fin (N - j)) (Fin (N - j)) ℝ) - H) R ∧
        0 < endpointPairing (Nat.sub_pos_of_lt hj) R ∧
        endpointPairing (Nat.sub_pos_of_lt hj) R ≤
          2 /
            (lam + Real.sqrt
              (lam ^ 2 - 4 * (A ⟨j + 1, Nat.succ_lt_succ hj⟩) ^ 2))

end MathlibPlus.Open.Analysis.K0119
