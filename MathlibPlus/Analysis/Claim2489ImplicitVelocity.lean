import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

open scoped Topology

namespace MathlibPlus.Analysis

local instance {𝕜 : Type} [NontriviallyNormedField 𝕜] : NormedSpace 𝕜 𝕜 :=
  NormedField.toNormedSpace

/-- The velocity of a simple zero along a linear homotopy. -/
theorem implicitVelocityOfSimpleHomotopyZero
    {𝕜 : Type} [NontriviallyNormedField 𝕜]
    (F₀ C z : 𝕜 → 𝕜) (F₀' C' z' s : 𝕜)
    (hzero : (fun t => F₀ (z t) + t * C (z t)) =ᶠ[𝓝 s] (fun _ => 0))
    (hF : HasDerivAt F₀ F₀' (z s))
    (hC : HasDerivAt C C' (z s))
    (hz : HasDerivAt z z' s)
    (hsimple : F₀' + s * C' ≠ 0) :
    z' = -C (z s) / (F₀' + s * C') := by
  have hderiv := (hF.comp s hz).add ((hasDerivAt_id s).mul (hC.comp s hz))
  have hconst :=
    hderiv.congr_of_eventuallyEq hzero.symm
  have hEq := hconst.unique (hasDerivAt_const s 0)
  simp only [Function.comp_apply, id_eq] at hEq
  apply (eq_div_iff hsimple).2
  linear_combination hEq

end MathlibPlus.Analysis
