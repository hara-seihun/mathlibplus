import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1643Claim39879

private def isAffineLocal39879
    (q : ℕ) (f : Equiv.Perm (ZMod q)) : Prop :=
  ∃ a : (ZMod q)ˣ, ∃ b : ZMod q,
    ∀ x : ZMod q, f x = (a : ZMod q) * x + b

def claim39879
    (q : ℕ) (sigma tau : Equiv.Perm (ZMod q)) : Prop :=
  Nat.Prime q ∧ (q = 5 ∨ q = 7) ∧
    sigma ≠ 1 ∧ isAffineLocal39879 q sigma ∧
      ¬ isAffineLocal39879 q tau

end MathlibPlus.Open.ResearchFormalization.R1643Claim39879
