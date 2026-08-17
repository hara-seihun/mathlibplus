import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.SharpenedRREFColourCountClaim35100

noncomputable section

abbrev F2 := ZMod 2
abbrev BinarySpace (m : ℕ) := Fin m → F2

/-- The number of subspaces of the exact `m`-dimensional binary space. -/
noncomputable def binarySubspaceCount (m : ℕ) : ℕ :=
  Fintype.card (Submodule F2 (BinarySpace m))

/-- Exact coarse pair colours: two quotient dimensions, two displacement
values, and one pair-image subspace. -/
noncomputable def coarsePairColourCount (d : ℕ) : ℕ :=
  ∑ r : Fin (d + 1), ∑ s : Fin (d + 1),
    Fintype.card (BinarySpace r.1 × BinarySpace s.1) *
      Fintype.card
        (Submodule F2 (BinarySpace r.1 × BinarySpace s.1))

/-- Claim 35100: the RREF subspace count and the resulting exact coarse
pair-colour bound. -/
def claim35100 : Prop :=
  ∀ (M d : ℕ), 1 ≤ M → d = Nat.log 2 M →
    (∀ m : ℕ,
      (binarySubspaceCount m : ℝ) ≤
        (2 : ℝ) ^ ((m : ℝ) ^ 2 / 4 + 2 * m)) ∧
    (∀ m : ℕ, m ≤ 2 * d →
      (binarySubspaceCount m : ℝ) ≤
        (2 : ℝ) ^ ((d : ℝ) ^ 2 + 4 * d)) ∧
    (coarsePairColourCount d : ℝ) ≤
      (2 : ℝ) ^ ((d : ℝ) ^ 2 + 8 * d + 1)

end
end MathlibPlus.Open.ResearchFormalization.SharpenedRREFColourCountClaim35100
