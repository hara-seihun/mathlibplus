import Mathlib
import MathlibPlus.Open.ResearchFormalization.R0714.Claim24184

namespace MathlibPlus.Open.ResearchFormalization.R0714Claim24181

noncomputable section

open MathlibPlus.Open.ResearchFormalization.R0714

/-- The cardinality of the actual one-vertex extension fibre. -/
def extensionFiberCard (n : ℕ) (F : GraphType n) : ℕ :=
  Nat.card (ExtensionFiber n F)

/-- Exact maximum size of the one-vertex extension fibres at one card order. -/
def maxFiberAtMostExactly (n m : ℕ) : Prop :=
  (∀ F : GraphType n, extensionFiberCard n F ≤ m) ∧
    ∃ F : GraphType n, extensionFiberCard n F = m

/-- Claim 24181: exact unlabeled card-type counts, their total, and the
corresponding exact maximum one-vertex extension-fibre sizes through order
seven. -/
def claim24181 : Prop :=
  Fintype.card (GraphType 2) = 2 ∧
    Fintype.card (GraphType 3) = 4 ∧
    Fintype.card (GraphType 4) = 11 ∧
    Fintype.card (GraphType 5) = 34 ∧
    Fintype.card (GraphType 6) = 156 ∧
    Fintype.card (GraphType 7) = 1044 ∧
    Fintype.card (GraphType 2) + Fintype.card (GraphType 3) +
        Fintype.card (GraphType 4) + Fintype.card (GraphType 5) +
        Fintype.card (GraphType 6) + Fintype.card (GraphType 7) = 1251 ∧
    maxFiberAtMostExactly 2 3 ∧
    maxFiberAtMostExactly 3 6 ∧
    maxFiberAtMostExactly 4 12 ∧
    maxFiberAtMostExactly 5 24 ∧
    maxFiberAtMostExactly 6 64 ∧
    maxFiberAtMostExactly 7 128

end

end MathlibPlus.Open.ResearchFormalization.R0714Claim24181
