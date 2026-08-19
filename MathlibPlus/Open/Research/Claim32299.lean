import MathlibPlus.Open.Research.IdentityBasePrimeFiber

namespace MathlibPlus.Open.Research.Claim32299

open MathlibPlus.Open.Research

/-- Claim 32299: a constant displacement on the cyclic prime set is a
translation, and every nontranslation has two displacement values with a
nonzero difference. -/
def claim32299 : Prop :=
  ∀ (p : ℕ), Nat.Prime p →
    ∀ σ : Equiv.Perm (ZMod p),
      ((∀ y z : ZMod p, y - σ y = z - σ z) →
        ∃ a : ZMod p, σ = translation p a) ∧
      ((¬ ∃ a : ZMod p, σ = translation p a) →
        ∃ y z c : ZMod p,
          c ≠ 0 ∧ (y - σ y) - (z - σ z) = c)

end MathlibPlus.Open.Research.Claim32299
