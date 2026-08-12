import Mathlib

namespace MathlibPlus.Combinatorics.Claim49067

/-- A positive radius class with at least five points remains a positive radius
class with at least four points after deleting any one point of the finite set. -/
theorem deletionRobustPositiveRadiusClass
    {α : Type*} [DecidableEq α]
    (dist : α → α → ℕ) (P : Finset α) (c : α)
    (hlarge : ∃ r : ℕ, 0 < r ∧ 5 ≤ (P.filter (fun y => dist c y = r)).card) :
    ∀ x ∈ P, ∃ r : ℕ, 0 < r ∧
      4 ≤ ((P.erase x).filter (fun y => dist c y = r)).card := by
  classical
  obtain ⟨r, hrpos, hr⟩ := hlarge
  intro x hx
  let S := P.filter (fun y => dist c y = r)
  have hS : 5 ≤ S.card := hr
  by_cases hxin : x ∈ S
  · refine ⟨r, hrpos, ?_⟩
    have hfilter : (P.erase x).filter (fun y => dist c y = r) = S.erase x := by
      ext y
      simp [S, and_assoc, and_left_comm, and_comm]
    rw [hfilter, Finset.card_erase_of_mem hxin]
    omega
  · refine ⟨r, hrpos, ?_⟩
    have hfilter : (P.erase x).filter (fun y => dist c y = r) = S := by
      ext y
      by_cases hy : y = x
      · subst y
        simp [S, hxin]
      · simp [S, hy]
    rw [hfilter]
    exact le_trans (by omega) hS

end MathlibPlus.Combinatorics.Claim49067
