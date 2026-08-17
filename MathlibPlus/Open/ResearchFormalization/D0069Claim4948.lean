import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.D0069Claim4948

noncomputable section

noncomputable def cellularZeroPackingNumber_claim4948 (F : ℝ → ℝ) : ℕ∞ :=
  sSup {m : ℕ∞ | ∃ k : ℕ, m = (k : ℕ∞) ∧
    ∃ n : Fin k → ℤ,
      StrictMono n ∧
        ∃ x : Fin k → ℝ,
          ∀ i : Fin k,
            (n i : ℝ) < x i ∧
              x i < ((n i + 1 : ℤ) : ℝ) ∧
                F (x i) = 0}

end
end MathlibPlus.Open.ResearchFormalization.D0069Claim4948
