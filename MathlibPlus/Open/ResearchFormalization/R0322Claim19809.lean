import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0322Claim19809

noncomputable section

open Classical

abbrev Sym := MvPolynomial ℕ ℚ
abbrev RationalFunction3 := FractionRing (MvPolynomial (Fin 3) ℚ)

def coordinate (i : Fin 3) : RationalFunction3 :=
  algebraMap (MvPolynomial (Fin 3) ℚ) RationalFunction3 (MvPolynomial.X i)

def x : RationalFunction3 := coordinate 0

def y : RationalFunction3 := coordinate 1

def z : RationalFunction3 := coordinate 2

def X : RationalFunction3 := x

def A : RationalFunction3 := x * (y - z)

def W : RationalFunction3 := y - 1

def w₁ : RationalFunction3 := x * (W + 1) / A

def w₂ : RationalFunction3 := (W + 1) / W

def p (m : ℕ) : Sym := MvPolynomial.X m

def algebraicallyIndependentCoordinates : Prop :=
  ∀ P : MvPolynomial (Fin 3) ℚ,
    MvPolynomial.aeval (fun i =>
      if i = 0 then X else if i = 1 then A else W) P = 0 → P = 0

private def sourcePowerSumCharacterization
    (γ : Sym →ₐ[ℚ] RationalFunction3) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    γ (p m) = y * x ^ m * (y - z) ^ (m - 1) +
      y * (y - 1) ^ (m - 1)

private def weightedPowerSumCharacterization
    (γ : Sym →ₐ[ℚ] RationalFunction3) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    γ (p m) = w₁ * A ^ m + w₂ * W ^ m

def nonconstantMultiplicity (a : RationalFunction3) : Prop :=
  ¬ ∃ c : ℚ, a = algebraMap ℚ RationalFunction3 c

def weightedTwoLetterPlethysticEvaluation_claim19809 : Prop :=
  algebraicallyIndependentCoordinates ∧
    ∃ γ : Sym →ₐ[ℚ] RationalFunction3,
      sourcePowerSumCharacterization γ ∧
        (∀ m : ℕ, 1 ≤ m →
          γ (p m) = (1 + W) * (W ^ (m - 1) + X * A ^ (m - 1)) ∧
            γ (p m) = w₁ * A ^ m + w₂ * W ^ m) ∧
        weightedPowerSumCharacterization γ ∧
        nonconstantMultiplicity w₁ ∧
        nonconstantMultiplicity w₂

end

end MathlibPlus.Open.ResearchFormalization.R0322Claim19809
