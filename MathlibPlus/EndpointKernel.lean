import Mathlib

/-!
# Unsampled endpoint-kernel cell

This file formalizes the exact elementary nullspace statement in Record 4 of legacy
packet `C-0159`. It does not assert the packet's Möbius inversion or analytic source
realization.
-/

namespace MathlibPlus.EndpointKernel

/-- A perturbation supported in `(0, 1)` vanishes at every sampled point `n * u`
with natural `n ≥ 1` and real `u ≥ 1`. -/
theorem unsampledCell_invisible (h : ℝ → ℝ)
    (hsupport : Function.support h ⊆ Set.Ioo (0 : ℝ) 1)
    (n : ℕ) (u : ℝ) (hn : 1 ≤ n) (hu : 1 ≤ u) :
    h ((n : ℝ) * u) = 0 := by
  by_contra hne
  have hmem : (n : ℝ) * u ∈ Function.support h := hne
  have hlt : (n : ℝ) * u < 1 := (hsupport hmem).2
  have hn_real : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

end MathlibPlus.EndpointKernel
