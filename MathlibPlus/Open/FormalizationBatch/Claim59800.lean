import Mathlib

open scoped BigOperators Matrix

namespace MathlibPlus.Open.FormalizationBatch.Claim59800

def block (t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, -2 * t]

def criticalLineDistinctLocalBlockCrossCoupling : Prop :=
  ∀ c d : ℝ, ∀ H : Matrix (Fin 2) (Fin 2) ℝ,
    c ≠ d → (block c).transpose * H * block d = H → H = 0

end MathlibPlus.Open.FormalizationBatch.Claim59800
