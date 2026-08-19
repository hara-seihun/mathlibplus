import Mathlib

namespace MathlibPlus.Analysis

/--
The graph and normalized pole-limit maps in Claim 12318.  Both scalar lines
are required to be injective, to have one-dimensional image and cokernel, and
therefore to have the same image and cokernel ranks for every `a`, including
`a = 0`.
-/
def scalarConstantTermGraphRanks : Prop :=
  ∀ a : ℂ,
    let graph : ℂ →ₗ[ℂ] ℂ × ℂ :=
      LinearMap.prod LinearMap.id
        (LinearMap.smulRight (LinearMap.id : ℂ →ₗ[ℂ] ℂ) a)
    let pole : ℂ →ₗ[ℂ] ℂ × ℂ :=
      LinearMap.prod 0 LinearMap.id
    Function.Injective graph ∧
      Module.finrank ℂ graph.range = 1 ∧
      Module.finrank ℂ ((ℂ × ℂ) ⧸ graph.range) = 1 ∧
      Function.Injective pole ∧
      Module.finrank ℂ pole.range = 1 ∧
      Module.finrank ℂ ((ℂ × ℂ) ⧸ pole.range) = 1 ∧
      Module.finrank ℂ graph.range = Module.finrank ℂ pole.range ∧
      Module.finrank ℂ ((ℂ × ℂ) ⧸ graph.range) =
        Module.finrank ℂ ((ℂ × ℂ) ⧸ pole.range)

end MathlibPlus.Analysis
