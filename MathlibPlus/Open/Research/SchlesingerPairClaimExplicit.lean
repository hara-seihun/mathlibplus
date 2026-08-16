import Mathlib

namespace MathlibPlus.Open.Research

noncomputable section

def residueP : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(1 : ℂ), -1]

def residueQ : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(2 : ℂ), -2]

def residueTracePairing : ℂ :=
  (Finset.univ : Finset (Fin 2)).sum
    (fun i => (residueP * residueQ) i i)

def commutingPairTauLog (aₚ aᵩ : ℝ) : ℝ :=
  4 * Real.log (aₚ - aᵩ)

def commutingPairTauFactor (aₚ aᵩ : ℝ) : ℝ :=
  Real.exp (commutingPairTauLog aₚ aᵩ)

def commutingPairTauMixedHessian (aₚ aᵩ : ℝ) : ℝ :=
  deriv (fun x => deriv (fun y => commutingPairTauLog x y) aᵩ) aₚ

def claim11475_explicitTauVisibleDiagonalPair_batch01a00b1e : Prop :=
  residueP * residueQ = residueQ * residueP ∧
    residueTracePairing = 4 ∧
    (∀ aₚ aᵩ : ℝ, aₚ > aᵩ →
      commutingPairTauFactor aₚ aᵩ = (aₚ - aᵩ) ^ (4 : ℕ) ∧
        commutingPairTauMixedHessian aₚ aᵩ =
          4 / (aₚ - aᵩ) ^ (2 : ℕ) ∧
        commutingPairTauMixedHessian aₚ aᵩ ≠ 0)

end

end MathlibPlus.Open.Research
