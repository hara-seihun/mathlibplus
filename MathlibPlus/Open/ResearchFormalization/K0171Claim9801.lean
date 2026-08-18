import MathlibPlus.Open.Analysis.Claim9805

open scoped BigOperators
open Filter

namespace MathlibPlus.Open.ResearchFormalization.K0171Claim9801

noncomputable section

open MathlibPlus.Open.Analysis

/-- The exact eta-coefficient expansion used to define the finite-prime Li
term, tied to the meromorphic logarithmic derivative of the Riemann zeta
function rather than to an unconstrained callback. -/
def etaExpansion9801 (eta : ℕ → ℝ) : Prop :=
  ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < 1 / 2 →
    -(deriv riemannZeta (1 + w)) / riemannZeta (1 + w) =
      1 / w + ∑' j : ℕ, (eta j : ℂ) * w ^ j

/-- The fixed finite-prime Li term determined by the eta coefficients. -/
def finitePrimeLiTerm9801 (eta : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.Icc 1 n,
    (Nat.choose n j : ℝ) * eta (j - 1)

/-- Claim 9801: the centered finite-prime Laguerre transforms converge at
 each fixed index to the canonical finite-prime Li term. -/
def claim9801 : Prop :=
  ∀ (eta : ℕ → ℝ), etaExpansion9801 eta →
    ∀ n : ℕ,
      Filter.Tendsto
        (fun X : ℕ => finiteSf_claim9805 X n)
        Filter.atTop (nhds (finitePrimeLiTerm9801 eta n))

end

end MathlibPlus.Open.ResearchFormalization.K0171Claim9801
