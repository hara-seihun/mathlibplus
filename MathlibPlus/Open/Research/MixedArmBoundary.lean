import Mathlib

namespace MathlibPlus.Open.Research.MixedArmBoundary

noncomputable section
open scoped BigOperators

abbrev ArmPolynomial := Polynomial ℚ

def optionPolynomial (options : List ℕ) : ArmPolynomial :=
  options.foldr (fun d p => Polynomial.X ^ d + p) 0

def armProduct : List (List ℕ) → ArmPolynomial
  | [] => 1
  | options :: rest => optionPolynomial options * armProduct rest

def mixedArmPolynomial (r s : ℕ) : ArmPolynomial :=
  armProduct (List.replicate r [0, 1] ++ List.replicate s [0, 1, 1]) +
    Polynomial.X * armProduct (List.replicate s [0, 1])

def displayedMixedArmPolynomial (r s : ℕ) : ArmPolynomial :=
  (1 + Polynomial.X) ^ r * (1 + 2 * Polynomial.X) ^ s +
    Polynomial.X * (1 + Polynomial.X) ^ s

def centreIncludedIncorrect (r s : ℕ) : ArmPolynomial :=
  Polynomial.X * (1 + Polynomial.X) ^ (r + s)

/-- Claim 49696: the centre-included term excludes the length-one leaves. -/
def claim49696 : Prop :=
  (∀ r s : ℕ,
      mixedArmPolynomial r s = displayedMixedArmPolynomial r s) ∧
    (∀ s : ℕ,
      mixedArmPolynomial 0 s =
        (1 + 2 * Polynomial.X) ^ s +
          Polynomial.X * (1 + Polynomial.X) ^ s) ∧
    (∀ r s : ℕ, 1 ≤ r →
      displayedMixedArmPolynomial r s ≠
        (1 + Polynomial.X) ^ r * (1 + 2 * Polynomial.X) ^ s +
          centreIncludedIncorrect r s)

end

end MathlibPlus.Open.Research.MixedArmBoundary
