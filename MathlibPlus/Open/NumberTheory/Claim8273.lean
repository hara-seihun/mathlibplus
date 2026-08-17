import MathlibPlus.Open.NumberTheory.ResearchEulerFactor
import MathlibPlus.NumberTheory.Claim8276

namespace MathlibPlus.Open.NumberTheory.Claim8273

open MathlibPlus.Open.NumberTheory
open MathlibPlus.NumberTheory.Claim8276

/-- Primewise cancellation on the `v = 0` face, including the Euler product
and the normalized arithmetic-sum identity. -/
def claim8273_primewiseCancellationOnV0 : Prop :=
  ∀ (N : ℕ) (χ : DirichletCharacter ℂ N) (w : ℂ),
    1 < N →
    DirichletCharacter.Odd χ →
    0 < w.re →
    (∀ p : {p : ℕ // p.Prime ∧ ¬p ∣ N},
      researchEulerFactor χ p.1 w 0 =
        1 - χ (p.1 : ZMod N) / (p.1 : ℂ)) ∧
      (∏' p : {p : ℕ // p.Prime ∧ ¬p ∣ N},
        researchEulerFactor χ p.1 w 0) =
        (dirichletL N χ 1)⁻¹ ∧
      dirichletL N χ 1 * researchEulerSum N χ w 0 = 1

end MathlibPlus.Open.NumberTheory.Claim8273
