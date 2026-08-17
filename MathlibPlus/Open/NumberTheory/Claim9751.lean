import MathlibPlus.Open.NumberTheory.Claim9756

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace MathlibPlus.Open.NumberTheory.Claim9751

/-- The local level vectors, with `a = 0` representing `e_1`. -/
def localInnovationDifference {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (p : ℕ) (f : ℕ → H) (a : ℕ) : H :=
  if a = 0 then
    MathlibPlus.Open.NumberTheory.Claim9756.localPrimeAR1Vector p f 0
  else
    MathlibPlus.Open.NumberTheory.Claim9756.localPrimeAR1Vector p f a -
      MathlibPlus.Open.NumberTheory.Claim9756.localPrimeAR1Vector p f (a - 1)

/-- Claim 9751: the local causal inverse, together with its strict previous-level
span formulation of exponent-order preservation. -/
def claim9751 : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (p : ℕ),
    p.Prime →
    ∀ (f : ℕ → H),
      MathlibPlus.Open.NumberTheory.Claim9756.orthonormalInnovationFamily f →
      ∀ a : ℕ, 1 ≤ a →
        let r : ℝ := (p : ℝ)⁻¹
        let y : ℕ → H := localInnovationDifference p f
        (Real.sqrt (1 - r ^ 2) • f a =
            y a + (1 - r) • ∑ j ∈ Finset.range a, y j) ∧
          (Real.sqrt (1 - r ^ 2) • f a - y a ∈
            Submodule.span ℝ (Set.range (fun j : Fin a => y j)))

end MathlibPlus.Open.NumberTheory.Claim9751
