import MathlibPlus.Open.NumberTheory.ResearchEulerFactor

namespace MathlibPlus.Open.Research.FormalizationBatch.K0078Claim8267

open Classical
open MathlibPlus.Open.NumberTheory
open scoped BigOperators

noncomputable def arithmeticTripleAdmissible8267
    (N : ℕ) (qdm : ℕ × ℕ × ℕ) : Prop :=
  1 ≤ qdm.1 ∧
    1 ≤ qdm.2.1 ∧
    1 ≤ qdm.2.2 ∧
    Nat.Coprime (qdm.1 * qdm.2.1 * qdm.2.2) N ∧
    Nat.Coprime qdm.1 qdm.2.1 ∧
    Nat.Coprime qdm.1 qdm.2.2 ∧
    Nat.Coprime qdm.2.1 qdm.2.2

noncomputable def arithmeticSummand8267
    (N : ℕ) (χ : DirichletCharacter ℂ N) (w v : ℂ)
    (qdm : ℕ × ℕ × ℕ) : ℂ :=
  let Q := qdm.1
  let d := qdm.2.1
  let m := qdm.2.2
  ((((ArithmeticFunction.moebius Q : ℤ) : ℂ) /
      Complex.cpow (Q : ℂ) (1 + w)) *
    ((((ArithmeticFunction.moebius d : ℤ) : ℂ) ^ 2) /
      Complex.cpow (d : ℂ) (1 + w + v)) *
    ((((ArithmeticFunction.moebius m : ℤ) : ℂ) *
        χ (m : ZMod N)) /
      Complex.cpow (m : ℂ) (1 + v)))

/-- The admitted three-variable sum, aligned to the non-definitional
indicator form on the unrestricted triple carrier. -/
def exactThreeVariableArithmeticSum_claim8267 : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (w v : ℂ),
    N > 1 →
    DirichletCharacter.Odd χ →
    0 < w.re →
    0 < v.re →
    researchEulerSum N χ w v =
      ∑' qdm : ℕ × ℕ × ℕ,
        if arithmeticTripleAdmissible8267 N qdm then
          arithmeticSummand8267 N χ w v qdm
        else 0

end MathlibPlus.Open.Research.FormalizationBatch.K0078Claim8267
