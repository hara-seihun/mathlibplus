import Mathlib

open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace MathlibPlus.Open.NumberTheory.Claim9763

/-- The exact Gram--Schmidt residual and squared norm asserted by Claim 9763. -/
def gramSchmidtResidualExact : Prop :=
  ∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (e : ℕ → H),
    (∀ d f : ℕ, 0 < d → 0 < f →
      ⟪e d, e f⟫ =
        ((Nat.gcd d f : ℝ) ^ 2) / ((d : ℝ) * (f : ℝ))) →
    ∀ n : ℕ, 0 < n →
      letI : DecidableEq H := Classical.decEq H
      let w : ℕ → H := fun k =>
        Finset.sum k.divisors (fun d => (ArithmeticFunction.moebius (k / d) : ℝ) • e d)
      let z : ℕ → H := fun k =>
        Finset.sum k.divisors (fun d =>
          (((d : ℝ) / (k : ℝ)) * (ArithmeticFunction.moebius (k / d) : ℝ)) • e d)
      let R : ℕ → ℝ := fun k =>
        Finset.prod k.primeFactors (fun p => 1 - ((p : ℝ)⁻¹) ^ 2)
      let previous : Submodule ℝ H :=
        Submodule.span ℝ ((Finset.Icc 1 (n - 1)).image w : Set H)
      w n - (↑(previous.orthogonalProjectionOnto (w n)) : H) = z n ∧
        ‖z n‖ ^ 2 = R n

end MathlibPlus.Open.NumberTheory.Claim9763
