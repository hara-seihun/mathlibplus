import MathlibPlus.Open.NumberTheory.LayerGramFactorizationClaim9761
import MathlibPlus.Open.NumberTheory.Claim9756

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace MathlibPlus.Open.NumberTheory.K0165

/-- Claim 9748: the concrete Hilbert-space gcd kernel and Möbius Farey levels. -/
def claim9748 : Prop :=
  let e : ℕ → FareyHilbert := fareyBasisVector
  let w : ℕ → FareyHilbert := fareyLevelVector
  (∀ d e' : ℕ, 0 < d → 0 < e' →
    inner ℝ (e d) (e e') =
      ((Nat.gcd d e' : ℝ) ^ 2) / ((d : ℝ) * (e' : ℝ))) ∧
  (∀ n : ℕ, 0 < n →
    w n =
      ∑ d ∈ n.divisors,
        (((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ)) • e d)

/-- Claim 9750: the local causal prime AR(1) realization. -/
def claim9750 : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (p : ℕ), p.Prime →
    ∀ f : ℕ → H, Claim9756.orthonormalInnovationFamily f →
      ∀ a b : ℕ,
        inner ℝ (Claim9756.localPrimeAR1Vector p f a)
          (Claim9756.localPrimeAR1Vector p f b) =
          ((p : ℝ)⁻¹) ^ Nat.dist a b

end MathlibPlus.Open.NumberTheory.K0165

end
