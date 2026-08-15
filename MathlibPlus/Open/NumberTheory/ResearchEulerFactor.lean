import Mathlib

namespace MathlibPlus.Open.NumberTheory

noncomputable def researchEulerSum (N : ℕ) (χ : DirichletCharacter ℂ N) (w v : ℂ) : ℂ :=
  ∑' x : {qdm : ℕ × ℕ × ℕ //
      1 ≤ qdm.1 ∧
      1 ≤ qdm.2.1 ∧
      1 ≤ qdm.2.2 ∧
      Nat.Coprime (qdm.1 * qdm.2.1 * qdm.2.2) N ∧
      Nat.Coprime qdm.1 qdm.2.1 ∧
      Nat.Coprime qdm.1 qdm.2.2 ∧
      Nat.Coprime qdm.2.1 qdm.2.2},
    let Q := x.1.1
    let d := x.1.2.1
    let m := x.1.2.2
    ((((ArithmeticFunction.moebius Q : ℤ) : ℂ) /
        Complex.cpow (Q : ℂ) (1 + w)) *
      ((((ArithmeticFunction.moebius d : ℤ) : ℂ) ^ 2) /
        Complex.cpow (d : ℂ) (1 + w + v)) *
      ((((ArithmeticFunction.moebius m : ℤ) : ℂ) * χ (m : ZMod N)) /
        Complex.cpow (m : ℂ) (1 + v)))

noncomputable def researchEulerFactor (χ : DirichletCharacter ℂ N) (p : ℕ)
    (w v : ℂ) : ℂ :=
  1 - Complex.cpow (p : ℂ) (-1 - w) +
      Complex.cpow (p : ℂ) (-1 - w - v) -
      χ (p : ZMod N) * Complex.cpow (p : ℂ) (-1 - v)

/-- Exact four-state Euler factor identity from admitted Claim 8268. -/
def researchEulerFactorIdentity : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (w v : ℂ),
    N > 1 →
    DirichletCharacter.Odd χ →
    0 < w.re →
    0 < v.re →
    researchEulerSum N χ w v =
      ∏' p : {p : ℕ // p.Prime ∧ ¬p ∣ N},
        researchEulerFactor χ p.1 w v

end MathlibPlus.Open.NumberTheory
