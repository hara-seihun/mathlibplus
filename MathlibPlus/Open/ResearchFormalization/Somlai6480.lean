import MathlibPlus.Open.Research.SomlaiBoundaryDefect

open scoped BigOperators TensorProduct

namespace MathlibPlus.Open.ResearchFormalization.Somlai6480

open MathlibPlus.Open.Research.Somlai

noncomputable section

/-- The tensor attached to one labelled direction/coefficient pair in the
explicit Somlai profile. -/
private def labelledTensor (p : ℕ) (hp : p.Prime) (L : SomlaiLabel p) :
    SomlaiV p ⊗[ZMod p] SomlaiB p :=
  @somlaiCoefficient p ⟨hp⟩ L ⊗ₜ[ZMod p] @somlaiDirection p ⟨hp⟩ L

/-- Coefficients of the displayed relation, in the labelled order. -/
private def displayedRelationCoefficient (p : ℕ) : SomlaiLabel p → ZMod p
  | .first _ => 1
  | .second _ => 1
  | .terminal => -1

/-- Claim 6480: the explicit Somlai labels have the displayed unique relation,
with the resulting first-moment defect bounded by its one-dimensional relation
space. -/
def labelledTensorRelation_claim6480 : Prop :=
  ∀ (p : ℕ) (hp : p.Prime), p % 2 = 1 →
    Fintype.card (SomlaiLabel p) = 2 * p + 3 ∧
      (∑ i : Fin (p + 1), labelledTensor p hp (.first i)) +
          (∑ i : Fin (p + 1), labelledTensor p hp (.second i)) -
            labelledTensor p hp .terminal = 0 ∧
      (∀ a : SomlaiLabel p → ZMod p,
        (∑ L : SomlaiLabel p, a L • labelledTensor p hp L) = 0 →
          ∃ c : ZMod p, a = c • displayedRelationCoefficient p) ∧
      @boundaryDefect p ⟨hp⟩ ≤ 1

end

end MathlibPlus.Open.ResearchFormalization.Somlai6480
