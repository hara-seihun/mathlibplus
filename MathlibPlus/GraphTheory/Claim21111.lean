import Mathlib

open scoped symmDiff

namespace MathlibPlus.GraphTheory.Claim21111

/-- If two simple graphs on at least two vertices each have an isolated vertex,
then their edgewise symmetric difference is not complete. -/
theorem completeGraph_ne_symmDiff_of_isIsolated_claim21111
    {n : ℕ} (hn : 2 ≤ n) (A B : SimpleGraph (Fin n))
    {u v : Fin n} (hu : A.IsIsolated u) (hv : B.IsIsolated v) :
    A ∆ B ≠ (⊤ : SimpleGraph (Fin n)) := by
  intro htop
  by_cases huv : u = v
  · subst v
    have hn' : 1 < n := lt_of_lt_of_le (by decide) hn
    obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card (α := Fin n) (by simpa using hn') u
    have hnot : ¬ (A ∆ B).Adj u w := by
      simp [symmDiff_def, hu w, hv w]
    apply hnot
    rw [htop]
    exact hw.symm
  · have hA : ¬ A.Adj u v := hu v
    have hB : ¬ B.Adj u v := by
      intro h
      exact hv u h.symm
    have hnot : ¬ (A ∆ B).Adj u v := by
      simp [symmDiff_def, hA, hB]
    apply hnot
    rw [htop]
    simp [huv]

end MathlibPlus.GraphTheory.Claim21111
