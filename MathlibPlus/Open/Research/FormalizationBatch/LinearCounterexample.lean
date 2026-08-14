import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.FormalizationBatch
namespace LinearCounterexample

/-- The matrices in Claim 11678. -/
def A : Matrix (Fin 2) (Fin 2) ℝ := !![0, -9; 1, -7]

def J : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; -1, 0]

/-- The two roots written in the claim. -/
def root₁ : ℂ := (-7 + (Real.sqrt 13 : ℂ)) / 2

def root₂ : ℂ := (-7 - (Real.sqrt 13 : ℂ)) / 2

def characteristicPolynomial : Polynomial ℂ :=
  Polynomial.X ^ 2 + 7 * Polynomial.X + 9

/-- Claim 11678: symplectic similitude holds for A, while the roots have the
stated moduli and neither has modulus 3. -/
def claim11678 : Prop :=
  A.transpose * J * A = (9 : ℝ) • J ∧
    (∀ z : ℂ,
      characteristicPolynomial.IsRoot z ↔ z = root₁ ∨ z = root₂) ∧
    ({‖root₁‖, ‖root₂‖} : Set ℝ) =
      {(7 + Real.sqrt 13) / 2, (7 - Real.sqrt 13) / 2} ∧
    ‖root₁‖ ≠ 3 ∧ ‖root₂‖ ≠ 3

end LinearCounterexample
end MathlibPlus.Open.Research.FormalizationBatch
