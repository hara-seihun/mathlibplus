import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R5487

open scoped BigOperators

private abbrev RootedMessagePolynomial := MvPolynomial (Fin 3) ℤ

private noncomputable def weight (color : Bool) : RootedMessagePolynomial :=
  if color then MvPolynomial.X 1 else MvPolynomial.X 0

private noncomputable def marker : RootedMessagePolynomial :=
  MvPolynomial.X 2

private noncomputable def pathMessage : Bool → ℕ → RootedMessagePolynomial
  | color, 0 => weight color
  | color, length + 1 =>
      weight color *
        ((1 + marker) * pathMessage color length +
          pathMessage (!color) length)

private noncomputable def branchMessage : Bool → ℕ → RootedMessagePolynomial
  | _, 0 => 1
  | color, length + 1 =>
      (1 + marker) * pathMessage color length +
        pathMessage (!color) length

private noncomputable def spiderMessage
    (color : Bool) (arm₁ arm₂ arm₃ : ℕ) : RootedMessagePolynomial :=
  weight color *
    branchMessage color arm₁ *
      branchMessage color arm₂ * branchMessage color arm₃

private noncomputable def messageA
    (b : ℕ) (color : Bool) : RootedMessagePolynomial :=
  spiderMessage color 1 1 (2 * b)

private noncomputable def messageB
    (b : ℕ) (color : Bool) : RootedMessagePolynomial :=
  spiderMessage color 1 b (b + 1)

private noncomputable def standardResponseDifference
    (b : ℕ) : RootedMessagePolynomial :=
  (messageA b false - messageB b false) -
    (messageA b true - messageB b true)

private def responseN (b : ℕ) : ℕ := 2 * b + 3

private def responseM (b : ℕ) : ℕ := responseN b - 1

private noncomputable def coefficientExponent (b : ℕ) : Fin 3 →₀ ℕ :=
  Finsupp.single (0 : Fin 3) 2 +
    Finsupp.single (1 : Fin 3) (responseN b - 2) +
      Finsupp.single (2 : Fin 3) 2

private noncomputable def standardResponseCoefficient (b : ℕ) : ℤ :=
  MvPolynomial.coeff (coefficientExponent b) (standardResponseDifference b)

private def binomialRow (b s : ℕ) : ℚ :=
  (Nat.choose (responseM b - s) 2 : ℚ)

private def binomialResponseDifference (b : ℕ) : ℚ :=
  binomialRow b 1 - 2 * binomialRow b 3 + binomialRow b 5

/-- Claim 56535: the q=2 centre-conditioned rooted-message standard
coordinate separates the spiders A_b and B_b for every b at least two, and
its displayed binomial coefficient witness is the constant four. -/
def claim56535_rootedMessageStandardResponse : Prop :=
  ∀ b : ℕ, 2 ≤ b →
    responseN b = 2 * b + 3 ∧
      responseM b = responseN b - 1 ∧
      standardResponseDifference b ≠ 0 ∧
      standardResponseCoefficient b = 4 ∧
      binomialResponseDifference b = 4

end MathlibPlus.Open.ResearchFormalization.R5487
