import MathlibPlus.NumberTheory.Claim8247
import MathlibPlus.NumberTheory.Claim8254

namespace MathlibPlus.NumberTheory.Claim8248

open scoped BigOperators
open MathlibPlus.NumberTheory.Claim8247
open MathlibPlus.NumberTheory.Claim8254

/-- The summatory function and density constant on the reviewed
prime/parameter/carrier conventions. -/
noncomputable def summatoryFunctionAndDensityConstant_claim8248 : Prop :=
  ∀ q : ℕ, Nat.Prime q →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      (∀ x : ℝ,
        generalizedJordanSummatory q t x =
          Finset.sum (Finset.Icc 1 (Nat.floor x))
            (fun n =>
              ∏ p ∈ n.primeFactors.filter (fun p => p ≠ q),
                (1 - Real.rpow (p : ℝ) (-t)))) ∧
        (0 < t →
          generalizedJordanDensity q t =
            1 / (Complex.re (riemannZeta (1 + (t : ℂ))) *
              (1 - Real.rpow (q : ℝ) (-1 - t)))) ∧
        generalizedJordanDensity q 0 = 0

end MathlibPlus.NumberTheory.Claim8248
