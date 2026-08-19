import MathlibPlus.Open.Analysis.Claim9805

namespace MathlibPlus.Open.Analysis.K0171Claim9804

open MathlibPlus.Open.Analysis
open Classical

noncomputable section

/-- The Christoffel--Darboux quotient off the diagonal, using the reviewed
parameter-one Laguerre carrier. -/
def christoffelDarbouxQuotient9804 (M : ℕ) (x y : ℝ) : ℝ :=
  (laguerreOne_claim9805 M x * laguerreOne_claim9805 (M + 1) y -
      laguerreOne_claim9805 (M + 1) x * laguerreOne_claim9805 M y) /
    (x - y)

/-- The two-variable Christoffel--Darboux extension, with its diagonal value
set to the reviewed finite kernel. -/
def christoffelDarbouxExtension9804 (M : ℕ) (x y : ℝ) : ℝ :=
  if x = y then kernel_claim9805 M x y
  else christoffelDarbouxQuotient9804 M x y

/-- Claim 9804: the reviewed finite kernel has the exact off-diagonal
Christoffel--Darboux quotient and the quotient extension is continuous at every
diagonal point. -/
def exactChristoffelDarbouxCollapse_claim9804 : Prop :=
  (∀ (M : ℕ) (x y : ℝ), x ≠ y →
    kernel_claim9805 M x y = christoffelDarbouxQuotient9804 M x y) ∧
    (∀ (M : ℕ) (x : ℝ),
      ContinuousAt
        (fun p : ℝ × ℝ => christoffelDarbouxExtension9804 M p.1 p.2)
        (x, x))

end

end MathlibPlus.Open.Analysis.K0171Claim9804
