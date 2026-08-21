import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R0671

/-- The sup norm `‖p‖∞` on the Lobatto interval `[-1, 1]`, which is the norm
both bounds of R-0671 are stated in. -/
noncomputable def lobattoSupNorm (p : Polynomial ℝ) : ℝ :=
  sSup ((fun x => |p.eval x|) '' Set.Icc (-1 : ℝ) 1)

noncomputable def iteratedDerivative (p : Polynomial ℝ) (K : ℕ) : Polynomial ℝ :=
  (Polynomial.derivative^[K]) p

noncomputable def oscillatoryIntegral (p : Polynomial ℝ) (t : ℝ) : ℂ :=
  ∫ x in (-1 : ℝ)..1,
    Complex.ofReal (p.eval x) * Complex.exp (Complex.I * (t : ℂ) * (x : ℂ))

noncomputable def endpointTerm (p : Polynomial ℝ) (t : ℝ) (k : ℕ) : ℂ :=
  ((-1 : ℂ) ^ k / (Complex.I * (t : ℂ)) ^ (k + 1)) *
    (Complex.ofReal ((iteratedDerivative p k).eval (1 : ℝ)) *
        Complex.exp (Complex.I * (t : ℂ)) -
      Complex.ofReal ((iteratedDerivative p k).eval (-1 : ℝ)) *
        Complex.exp (-Complex.I * (t : ℂ)))

noncomputable def markovConstant (d K : ℕ) : ℝ :=
  (Finset.univ : Finset (Fin K)).prod
      (fun r => (d : ℝ) ^ 2 - (r.1 : ℝ) ^ 2) /
    (Nat.doubleFactorial (2 * K - 1) : ℝ)

def claim26617 : Prop :=
  ∀ (d K : ℕ) (p : Polynomial ℝ) (t : ℝ),
    p.natDegree ≤ d → t ≠ 0 →
    (∃ R : ℂ,
      oscillatoryIntegral p t =
          (∑ k : Fin K, endpointTerm p t k.1) + R ∧
        ‖R‖ ≤
          2 * lobattoSupNorm (iteratedDerivative p K) / |t| ^ K) ∧
    lobattoSupNorm (iteratedDerivative p K) ≤
      markovConstant d K * lobattoSupNorm p

end MathlibPlus.Open.ResearchFormalization.R0671
