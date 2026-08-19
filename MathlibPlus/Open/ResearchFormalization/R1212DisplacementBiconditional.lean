import MathlibPlus.Open.Research.Claim32299

namespace MathlibPlus.Open.ResearchFormalization.R1212DisplacementBiconditional

noncomputable section

open MathlibPlus.Open.Research

/-- Claim 42070: for a permutation of a cyclic prime field, being a
translation is equivalent to constant displacement; the contrapositive gives
the nonzero two-point displacement trigger for every nontranslation. -/
def translationIffConstantDisplacement_claim42070 : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ σ : Equiv.Perm (ZMod p),
      ((∃ a : ZMod p, σ = translation p a) ↔
        ∀ y z : ZMod p, y - σ y = z - σ z) ∧
      ((¬ ∃ a : ZMod p, σ = translation p a) →
        ∃ y z c : ZMod p,
          c ≠ 0 ∧ (y - σ y) - (z - σ z) = c)

end

end MathlibPlus.Open.ResearchFormalization.R1212DisplacementBiconditional
