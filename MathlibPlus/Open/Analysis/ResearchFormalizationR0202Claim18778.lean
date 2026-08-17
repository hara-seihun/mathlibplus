import MathlibPlus.Analysis.ThetaMellin

namespace MathlibPlus.Open.Analysis.ResearchFormalizationR0202

open MathlibPlus.Analysis.ThetaMellin

/-- Claim 18778: a finitely supported nonzero positive-index shell
combination cannot have every odd jet of its shell deformation vanish at the
origin.  The shell family is the source-defined completed-theta family. -/
noncomputable def claim18778_finiteShellCombinationRigidity : Prop :=
  ∀ c : ℕ → ℝ,
    (∃ N : ℕ, ∀ n : ℕ, N < n → c n = 0) →
      (∃ n : ℕ, 0 < n ∧ c n ≠ 0) →
        ¬ (let Φc : ℝ → ℝ := fun u ↦
            ∑' n : ℕ, c n * thetaShell n u
          ∀ j : ℕ, iteratedDeriv (2 * j + 1) Φc 0 = 0)

end MathlibPlus.Open.Analysis.ResearchFormalizationR0202
