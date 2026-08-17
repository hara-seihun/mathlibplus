import Mathlib
import MathlibPlus.Open.AlgebraicPauli.Orientation

namespace MathlibPlus.Open.AlgebraicPauli.Claim11808

noncomputable section

/-- Weyl reversal in the supplied weight basis `e₀,…,e_k`. -/
def weylReversal (k : ℕ) (b : WeightBasis k) :
    SymPower k →ₗ[ℂ] SymPower k :=
  b.constr ℂ (fun r => b (Fin.rev r))

/-- The untraced mixed coefficient identities on `Sym^k(ℂ²)`. -/
def claim11808 : Prop :=
  ∀ (k : ℕ) (b : WeightBasis k) (z y α : ℂ),
    (weylReversal k b).comp
        ((diagonalAction k b z).comp (weylReversal k b)) =
      diagonalAction k b z⁻¹ ∧
    mixedTrace k b (mixedAction k b y α) =
      character k y * character k α

end

end MathlibPlus.Open.AlgebraicPauli.Claim11808
