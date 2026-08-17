import MathlibPlus.Analysis.ThetaShellSummandClaim19068

open MeasureTheory
open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim19070

noncomputable section

/-- The literal positive-half-line source used by the coefficient moments. -/
def literalPhi : ℝ → ℝ := fun u ↦
  ∑' m : {m : ℕ // 0 < m},
    MathlibPlus.Analysis.thetaShellSummand m.1 u

/-- The moment carrier μ_j(t) for the literal heat family. -/
def literalMoment (t : ℝ) (j : ℕ) : ℝ :=
  ∫ u in Set.Ici (0 : ℝ),
    Real.exp (t * u ^ 2) * literalPhi u * u ^ j

/-- The coefficient normalization from the square-variable expansion. -/
def literalGamma (t : ℝ) (k : ℕ) : ℝ :=
  (4 : ℝ) ^ k * (Nat.factorial k : ℝ) * literalMoment t (2 * k) /
    (Nat.factorial (2 * k) : ℝ)

/-- The coefficient vector field induced by backward heat. -/
def coefficientHeatVectorField (a : ℕ → ℝ) (k : ℕ) : ℝ :=
  (((2 * k + 1 : ℕ) : ℝ) / 2) * a (k + 1)

/-- A finite coefficient window is autonomous when its vector field factors
through the coefficients in that finite window. -/
def finiteCoefficientWindowAutonomous (S : Finset ℕ) : Prop :=
  ∃ V : (S → ℝ) → (S → ℝ),
    ∀ a : ℕ → ℝ, ∀ k : S,
      coefficientHeatVectorField a k.1 =
        V (fun j : S => a j.1) k

/-- Claim 19070: every coefficient has the next-layer derivative, and no
nonempty finite coefficient/Jensen window closes under this heat evolution. -/
def coefficientFlowAndNonautonomy_claim19070 : Prop :=
  (∀ t : ℝ, ∀ k : ℕ,
    HasDerivAt (fun s : ℝ => literalGamma s k)
      (coefficientHeatVectorField (literalGamma t) k) t) ∧
    (∀ S : Finset ℕ, S.Nonempty →
      ¬ finiteCoefficientWindowAutonomous S)

end

end MathlibPlus.Open.Analysis.Claim19070
