import Mathlib

namespace MathlibPlus.Open.Research.FiniteActionBounds

noncomputable section

/-- Exact formal alignment of the faithful elementary-abelian action bound.  The
order and exponent hypotheses are the finite elementary-abelian rank-s data. -/
def claim50462 {E α : Type*} [CommGroup E] [Fintype E] [Fintype α]
    [MulAction E α] [FaithfulSMul E α] : Prop :=
  ∀ (p s : ℕ), Nat.Prime p →
    Fintype.card E = p ^ s →
    (∀ x : E, x ^ p = 1) →
    s * p ≤ Fintype.card α

/-- The p-rank formulation for the symmetric-group consequence, expanded over
all elementary-abelian p-subgroups rather than introducing an unprovided rank
operator. -/
def claim50463 : Prop :=
  ∀ (p a s : ℕ), Nat.Prime p → 1 ≤ a →
    ∀ E : Subgroup (Equiv.Perm (Fin (p ^ a))),
      letI : Fintype E := Fintype.ofFinite E
      (∀ x y : E, x * y = y * x) →
      (∀ x : E, x ^ p = 1) →
      Fintype.card E = p ^ s →
      s ≤ p ^ (a - 1)

end
end MathlibPlus.Open.Research.FiniteActionBounds
