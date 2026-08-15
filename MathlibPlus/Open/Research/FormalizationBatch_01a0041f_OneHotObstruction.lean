import Mathlib

namespace MathlibPlus.Open.Research

noncomputable section

/-- The answer transcript produced by an adaptive deterministic query map. -/
def oneHotTranscript {I : Type*} (Q : List Bool → I) (h : I) :
    ℕ → List Bool
  | 0 => []
  | q + 1 => by
      classical
      let previous := oneHotTranscript Q h q
      exact previous ++ [decide (Q previous = h)]

def oneHotPolicyFails {I : Type*} (q : ℕ) (Q : List Bool → I)
    (G : List Bool → I) (h : I) : Prop :=
  oneHotTranscript Q h q = List.replicate q false ∧
    G (oneHotTranscript Q h q) ≠ h

/-- Deterministic bounded-query policies miss a one-hot coordinate. -/
def claim_59895 : Prop :=
  (∀ (I : Type) [Fintype I] (q : ℕ) (Q : List Bool → I)
      (G : List Bool → I),
      Fintype.card I > q + 1 →
        ∃ h : I, oneHotPolicyFails q Q G h) ∧
    (∀ C : ℕ, ∀ (Q : List Bool → Fin (C + 2))
      (G : List Bool → Fin (C + 2)),
      ∃ h : Fin (C + 2), oneHotPolicyFails C Q G h)

end
end MathlibPlus.Open.Research
