import Mathlib
import MathlibPlus.Open.ResearchFormalization.InteriorChainResonance

namespace MathlibPlus.Open.ResearchFormalization.D0094Claim5314

open MathlibPlus.Open.ResearchFormalization

noncomputable def residualFamily : Fin 3 → Polynomial :=
  ![R_bend, R_leaf, R_quad]

noncomputable def modeFamily : Fin 3 → Polynomial :=
  ![V_bend, V_leaf, V_quad]

/-- Claim 5314: the three residual polynomials are independent, endpoint
multiplication by the nonzero core is injective, the three factorized modes
are independent, and the resulting resonance module has dimension three over
`ℚ`. -/
def claim5314 : Prop :=
  LinearIndependent ℚ residualFamily ∧
    endpointCore ≠ 0 ∧
    Function.Injective endpointMultiply ∧
    LinearIndependent ℚ modeFamily ∧
    Module.finrank ℚ R_chain = 3

end MathlibPlus.Open.ResearchFormalization.D0094Claim5314
