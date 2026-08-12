import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace MathlibPlus.Combinatorics

/-- Claim 5172: the doubled Euler curvature attached to a vertex of a finite
simple-graph card. -/
def doubledEulerCurvature_claim5172
    {V : Type*} [Fintype V] (C : SimpleGraph V) [DecidableRel C.Adj] (v : V) : ℤ :=
  (2 : ℤ) - (C.degree v : ℤ)

end MathlibPlus.Combinatorics
