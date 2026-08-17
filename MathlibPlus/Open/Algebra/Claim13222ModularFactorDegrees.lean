import Mathlib

open scoped Polynomial
open Polynomial

namespace MathlibPlus.Open.Algebra.Claim13222ModularFactorDegrees

/-- Claim 13222: the fixed exterior polynomial has irreducible factor-degree
patterns `6+6` modulo `31` and `4+4+4` modulo `11`. -/
def claim13222 : Prop :=
  let F : ℤ[X] :=
    X ^ 12 + X ^ 11 - C (2 : ℤ) * X ^ 10 - C (2 : ℤ) * X ^ 9 +
      X ^ 8 - C (5 : ℤ) * X ^ 7 - C (11 : ℤ) * X ^ 6 -
      C (5 : ℤ) * X ^ 5 + X ^ 4 - C (2 : ℤ) * X ^ 3 -
      C (2 : ℤ) * X ^ 2 + X + C (1 : ℤ)
  (∃ f₁ f₂ : Polynomial (ZMod 31),
      F.map (Int.castRingHom (ZMod 31)) = f₁ * f₂ ∧
        f₁.Monic ∧ f₂.Monic ∧
        Irreducible f₁ ∧ Irreducible f₂ ∧
        f₁.natDegree = 6 ∧ f₂.natDegree = 6) ∧
    (∃ f₁ f₂ f₃ : Polynomial (ZMod 11),
      F.map (Int.castRingHom (ZMod 11)) = f₁ * f₂ * f₃ ∧
        f₁.Monic ∧ f₂.Monic ∧ f₃.Monic ∧
        Irreducible f₁ ∧ Irreducible f₂ ∧ Irreducible f₃ ∧
        f₁.natDegree = 4 ∧ f₂.natDegree = 4 ∧ f₃.natDegree = 4)

end MathlibPlus.Open.Algebra.Claim13222ModularFactorDegrees
