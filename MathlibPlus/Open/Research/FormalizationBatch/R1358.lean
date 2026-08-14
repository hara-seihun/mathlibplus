import Mathlib

namespace MathlibPlus.Open.Research.FormalizationBatch.R1358

private noncomputable instance finiteSubtypeR1358 {α : Type} [Finite α] {p : α → Prop} :
    Finite {x : α // p x} :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- The explicit additive carrier `C₂³ × C₉` used by the connection-set census. -/
abbrev ResearchGroup := (ZMod 2 × ZMod 2 × ZMod 2) × ZMod 9

/-- Inverse-closed connection sets of a prescribed valency on `ResearchGroup`. -/
abbrev InverseClosedConnectionSet (n : ℕ) :=
  {S : Finset ResearchGroup //
    0 ∉ S ∧ S.card = n ∧ ∀ x ∈ S, -x ∈ S}

/-- Claim 38204: the exact valency-16 connection-space size. -/
def claim38204ExactValency16ConnectionSpace : Prop :=
  Nat.card (InverseClosedConnectionSet 16) = 114_327_628

end MathlibPlus.Open.Research.FormalizationBatch.R1358
