import Mathlib
import MathlibPlus.Open.Analysis.Claim3326

open scoped BigOperators
open Filter MeasureTheory Topology

namespace MathlibPlus.Open.Analysis.Claim3327

noncomputable section

open MathlibPlus.Open.Analysis.Claim3326

private def validNode (N : ℝ → ℕ) (L : ℝ) (n : ℕ) : Prop :=
  1 ≤ n ∧ n ≤ N L

private noncomputable def trainNode
    (y t : ℝ → ℕ → ℝ) (L : ℝ) (n : ℕ) : ℂ :=
  (y L n : ℂ) - Complex.I * (t L n : ℂ)

private noncomputable def shiftedBlaschke
    (y t : ℝ → ℕ → ℝ) (L : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  Finset.prod (Finset.Icc 1 (n - 1)) (fun k =>
    (w - trainNode y t L k) /
      (w + star (trainNode y t L k)))

private def noCrossedPrecedingPole
    (N : ℝ → ℕ) (y : ℝ → ℕ → ℝ) (theta : ℝ) : Prop :=
  ∀ᶠ L : ℝ in atTop,
    ∀ n : ℕ, validNode N L n →
      ∀ k : ℕ, 1 ≤ k → k < n → theta * y L n < y L k

private def shiftedBlaschkeLogIdentity
    (N : ℝ → ℕ) (y t : ℝ → ℕ → ℝ) (theta : ℝ) : Prop :=
  ∀ᶠ L : ℝ in atTop,
    ∀ n : ℕ, validNode N L n → ∀ xi : ℝ,
      let sigma : ℝ := theta * y L n
      let w : ℂ := -(sigma : ℂ) + Complex.I * (xi : ℂ)
      Real.log (‖shiftedBlaschke y t L n w‖ ^ 2) =
        Finset.sum (Finset.Icc 1 (n - 1)) (fun k =>
          Real.log (((y L k + sigma) ^ 2 + (xi - t L k) ^ 2) /
            ((y L k - sigma) ^ 2 + (xi - t L k) ^ 2)))

private def shiftedBlaschkeEnvelope
    (N : ℝ → ℕ) (y t : ℝ → ℕ → ℝ)
    (d : ℝ → ℝ) (theta : ℝ) : Prop :=
  ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
    ∃ Ctheta : ℝ, 0 ≤ Ctheta ∧
      ∀ᶠ L : ℝ in atTop,
        ∀ n : ℕ, validNode N L n → ∀ xi : ℝ,
          Real.log (‖shiftedBlaschke y t L n
              (-(theta * y L n : ℂ) + Complex.I * (xi : ℂ))‖ ^ 2) ≤
            (4 * Real.pi / d L + error L) *
                (theta * y L n) * L + Ctheta

private def individualCompactTailBound
    (N : ℝ → ℕ) (y : ℝ → ℕ → ℝ) (d : ℝ → ℝ)
    (phi : ℝ → ℕ → ℝ → ℂ) (theta : ℝ) : Prop :=
  ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
    ∃ Ctheta : ℝ, 0 ≤ Ctheta ∧
      ∀ᶠ L : ℝ in atTop,
        ∀ n : ℕ, validNode N L n →
          IntegrableOn (fun x : ℝ => ‖phi L n x‖ ^ 2)
            (Set.Ioi (2 * L)) ∧
          (∫ x in Set.Ioi (2 * L), ‖phi L n x‖ ^ 2) ≤
            Ctheta * Real.exp
              (-(4 - 4 * Real.pi / d L - error L) *
                theta * y L n * L)

/-- Claim 3327: after the weighted Plancherel hypotheses are put on the
actual dense train and its actual Takenaka--Malmquist inverse transforms, the
individual tail past `2 * L` has the stated exponent. -/
def individual_compact_tail_bound_claim3327 : Prop :=
  ∀ (N : ℝ → ℕ) (y t : ℝ → ℕ → ℝ)
    (d eta q R : ℝ → ℝ) (g : ℝ → ℝ → ℝ)
    (p r Y dLimit : ℝ) (phi : ℝ → ℕ → ℝ → ℂ),
    smoothMonotoneDenseTrain N y t d eta q R g p r Y dLimit →
    ∀ theta : ℝ, 0 < theta → theta < 1 →
      (noCrossedPrecedingPole N y theta ∧
        shiftedBlaschkeLogIdentity N y t theta ∧
        shiftedBlaschkeEnvelope N y t d theta ∧
        takenakaMalmquistBasis N y t phi) →
      individualCompactTailBound N y d phi theta

end
end MathlibPlus.Open.Analysis.Claim3327
