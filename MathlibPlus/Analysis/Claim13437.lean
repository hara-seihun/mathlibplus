import Mathlib

namespace MathlibPlus.Analysis

/-- The first-jet Gram matrix from admitted claim 13437. -/
def firstJetGram_claim13437 {R : Type*}
    (I₁₁ I₁₀ I₀₀ : R) : Matrix (Fin 2) (Fin 2) R :=
  !![I₁₁, I₁₀; I₁₀, I₀₀]

/-- The geodesic Hessian matrix from admitted claim 13437. -/
def geodesicHessian_claim13437 {R : Type*}
    (I₂₀ I₁₀ I₀₀ : R) : Matrix (Fin 2) (Fin 2) R :=
  !![I₂₀, I₁₀; I₁₀, I₀₀]

end MathlibPlus.Analysis
