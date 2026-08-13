import Mathlib

namespace MathlibPlus.Analysis.Claim18023

/-- Moving the lower cutoff of a summable natural-indexed tail by one removes
exactly the first omitted term.  This is the algebraic cutoff-coboundary core
of the Hurwitz--Mellin tail identity in claim 18023. -/
theorem cutoff_coboundary_claim18023
    (I : ℕ → ℝ) (hI : Summable I) (M : ℕ) :
    (∑' n, if M ≤ n then I n else 0) -
        (∑' n, if M + 1 ≤ n then I n else 0) = I M := by
  have hM : Summable (fun n => if M ≤ n then I n else 0) := by
    have h := hI.indicator (Set.Ici M)
    exact h.congr (fun n => by simp [Set.indicator])
  have hM1 : Summable (fun n => if M + 1 ≤ n then I n else 0) := by
    have h := hI.indicator (Set.Ici (M + 1))
    exact h.congr (fun n => by simp [Set.indicator])
  rw [← hM.tsum_sub hM1]
  calc
    (∑' n : ℕ, ((if M ≤ n then I n else 0) - (if M + 1 ≤ n then I n else 0))) =
        (∑' n : ℕ, (if n = M then I n else 0)) := by
      apply tsum_congr
      intro n
      by_cases hn : n = M
      · subst n
        simp
      · by_cases hMn : M ≤ n
        · have hM1n : M + 1 ≤ n := by omega
          simp [hMn, hM1n, hn]
        · have hM1n : ¬ M + 1 ≤ n := by omega
          simp [hMn, hM1n, hn]
    _ = I M := tsum_ite_eq M I

end MathlibPlus.Analysis.Claim18023
