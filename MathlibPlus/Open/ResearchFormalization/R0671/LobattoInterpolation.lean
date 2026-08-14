import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0671

noncomputable def lobattoSupNorm (p : Polynomial ℝ) : ℝ :=
  sSup (Set.range (fun x : Set.Icc (-1 : ℝ) 1 => |p.eval x.1|))

noncomputable def lobattoNodeNorm (d : ℕ) (p : Polynomial ℝ) : ℝ :=
  Real.sqrt
    (∑ j : Fin (d + 1),
      (p.eval (Real.cos (Real.pi * (j.1 : ℝ) / (d : ℝ)))) ^ 2)

def claim26616 : Prop :=
  ∀ (d : ℕ) (p : Polynomial ℝ),
    0 < d → p.natDegree ≤ d →
    lobattoSupNorm p ≤
      2 * Real.sqrt ((d : ℝ) - (1 / 2 : ℝ)) * lobattoNodeNorm d p

end MathlibPlus.Open.ResearchFormalization.R0671
