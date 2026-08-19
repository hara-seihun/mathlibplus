import Mathlib

open scoped BigOperators
noncomputable section

namespace MathlibPlus.Open.LinearAlgebra.Claim13515HermitianBound

def sharpSpectrum (a : ℝ) : Fin 4 → ℝ :=
  ![-a, -a, -a, 3 * a]

def sharpMatrix (a : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal (fun i => (sharpSpectrum a i : ℂ))

def frobeniusNorm (H : Matrix (Fin 4) (Fin 4) ℂ) : ℝ :=
  Real.sqrt (∑ i : Fin 4, ∑ j : Fin 4, ‖H i j‖ ^ 2)

noncomputable def leastHermitianEigenvalue
    (H : Matrix (Fin 4) (Fin 4) ℂ) (hH : H.IsHermitian) : ℝ :=
  (Finset.univ : Finset (Fin 4)).inf'
    ⟨0, Finset.mem_univ 0⟩ hH.eigenvalues

/-- Claim 13515: the sharp traceless Hermitian four-by-four eigenvalue bound,
with the proportional `(-1,-1,-1,3)` equality family explicit. -/
def claim13515_sharpTracelessHermitian4x4Bound : Prop :=
  (∀ (H : Matrix (Fin 4) (Fin 4) ℂ) (hH : H.IsHermitian),
    Matrix.trace H = 0 →
      leastHermitianEigenvalue H hH ≤
        -frobeniusNorm H / Real.sqrt 12) ∧
    (∀ a : ℝ, 0 < a →
      ∃ (H : Matrix (Fin 4) (Fin 4) ℂ) (hH : H.IsHermitian),
        H = sharpMatrix a ∧
          Matrix.trace H = 0 ∧
          leastHermitianEigenvalue H hH =
            -frobeniusNorm H / Real.sqrt 12)

end MathlibPlus.Open.LinearAlgebra.Claim13515HermitianBound
