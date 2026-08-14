import Mathlib

namespace MathlibPlus.Open.Frontier

/--
If two real polynomials have equal derivatives on a finite set large enough
for the derivative difference, and agree at one point, then they are equal.
-/
def polynomialDerivativeReconstruction : Prop :=
  ∀ (p q : Polynomial ℝ) (S : Set ℝ) (a : ℝ),
    S.Finite →
    (p.derivative - q.derivative).natDegree < S.ncard →
    (∀ x ∈ S, p.derivative.eval x = q.derivative.eval x) →
    p.eval a = q.eval a →
    p = q

end MathlibPlus.Open.Frontier
