import Mathlib

namespace MathlibPlus.Analysis.Claim8478

/-- The removable branch of the all-channel classifier. -/
def removable (f degree : ℕ) (rhoHat e_jet tau_rem : ℝ) : Prop :=
  degree ≤ f ∧ rhoHat + e_jet ≤ tau_rem

/-- The genuine branch of the all-channel classifier. -/
def genuine (rhoHat e_jet tau_true : ℝ) : Prop :=
  tau_true ≤ rhoHat - e_jet

/-- The unresolved branch is the complement of both named branches. -/
def unresolved (f degree : ℕ) (rhoHat e_jet tau_rem tau_true : ℝ) : Prop :=
  ¬ removable f degree rhoHat e_jet tau_rem ∧
    ¬ genuine rhoHat e_jet tau_true

/-- Under the displayed error bound, a candidate whose removal deletes a
minimal mode cannot be classified as removable. -/
theorem noFalseRemovals_claim8478
    {ι : Type _} (f degree : ι → ℕ) (rho rhoHat : ι → ℝ)
    (deletesMinimal : ι → Prop) (e_jet tau_rem tau_true : ℝ)
    (_htau_rem_nonneg : 0 ≤ tau_rem) (htau : tau_rem < tau_true)
    (herr : ∀ S, |rhoHat S - rho S| ≤ e_jet)
    (hmin : ∀ S, deletesMinimal S → tau_true ≤ rho S) :
    ∀ S, deletesMinimal S →
      ¬ removable (f S) (degree S) (rhoHat S) e_jet tau_rem := by
  intro S hdelete hremove
  have hparts :
      -e_jet ≤ rhoHat S - rho S ∧ rhoHat S - rho S ≤ e_jet :=
    (abs_le.mp (herr S))
  have hupper : rho S ≤ rhoHat S + e_jet := by
    linarith [hparts.2]
  have hminimal : tau_true ≤ rho S := hmin S hdelete
  rcases hremove with ⟨_, hremove⟩
  linarith

end MathlibPlus.Analysis.Claim8478
