import Mathlib

open scoped BigOperators
open MeasureTheory

namespace MathlibPlus.Open.Research.FormalizationR0219

noncomputable section

/-- Claim 18927: the finite-difference moment identity for the fixed gamma
Newton function, with the expectation written as its gamma-density integral. -/
def finiteDifferenceMomentIdentity18927 : Prop :=
  ∀ x : ℝ, 0 < x →
    ∀ k : ℕ,
      (let q : ℝ := 1 / (Real.pi * x ^ 2)
       let g : ℝ → ℝ := fun z =>
         Real.Gamma (5 / 4 + z) / Real.Gamma (5 / 4) * q ^ z
       let Δ : ℕ → ℝ := fun j =>
         Finset.sum (Finset.range (j + 1)) (fun a =>
           (-1 : ℝ) ^ (j - a) * (Nat.choose j a : ℝ) * g (a : ℝ))
       Δ k =
         ∫ t in Set.Ioi (0 : ℝ),
           (q * t - 1) ^ k * t ^ (1 / 4 : ℝ) * Real.exp (-t) /
             Real.Gamma (5 / 4 : ℝ) ∂volume)

end

end MathlibPlus.Open.Research.FormalizationR0219
