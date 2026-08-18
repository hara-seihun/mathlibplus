import Mathlib
import MathlibPlus.LinearAlgebra.Claim17770

namespace MathlibPlus.Open.ResearchFormalization.R0081Claim17769

/-- The distinguished even-jet vector on the exact finite coordinate carrier. -/
noncomputable def distinguishedEvenJet (N : ℕ) : Fin N → ℝ :=
  fun n => 1 /
    ((2 : ℝ) ^ (2 * n.1) *
      (Nat.factorial (2 * n.1) : ℝ))

/-- Claim 17769: every coordinate of the distinguished even-jet vector has
its displayed factorial normalization. -/
def claim17769_distinguishedEvenJetCoefficients : Prop :=
  ∀ (N : ℕ) (n : Fin N),
    distinguishedEvenJet N n =
      1 /
        ((2 : ℝ) ^ (2 * n.1) *
          (Nat.factorial (2 * n.1) : ℝ))

end MathlibPlus.Open.ResearchFormalization.R0081Claim17769
