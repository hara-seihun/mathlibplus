import Mathlib

namespace MathlibPlus.Open.Analysis.Claim16703

open scoped BigOperators

noncomputable section

/-- The polynomial family used for the Lagrange cardinal functions. -/
def lagrangeBasis {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : Polynomial ℝ :=
  Lagrange.basis (Finset.univ : Finset (Fin n)) a i

/-- The exact node, degree, and cardinal-value specification for a Lagrange
basis family. -/
def isLagrangeBasis {n : ℕ} (a : Fin n → ℝ)
    (p : Fin n → Polynomial ℝ) : Prop :=
  (∀ i : Fin n, (p i).natDegree < n) ∧
    (∀ i j : Fin n,
      (p i).eval (a j) = if i = j then 1 else 0)

/-- The Lagrange interpolant evaluated at `x`. -/
def lagrangeInterpolant {n : ℕ} (a : Fin n → ℝ)
    (p : Fin n → Polynomial ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, f (a i) * (p i).eval x

/-- The Lebesgue function associated with a Lagrange basis family. -/
def lebesgueFunction {n : ℕ}
    (p : Fin n → Polynomial ℝ) (x : ℝ) : ℝ :=
  ∑ i : Fin n, |(p i).eval x|

/-- Claim 16703: distinct nodes in `[-1,1]` carry the unique degree-bounded
cardinal polynomial family, with the displayed interpolant and Lebesgue
function. -/
def claim16703 : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℝ),
    (∀ i : Fin n, a i ∈ Set.Icc (-1 : ℝ) 1) →
      Function.Injective a →
        isLagrangeBasis a (fun i => lagrangeBasis a i) ∧
          ∀ p : Fin n → Polynomial ℝ,
            isLagrangeBasis a p →
              p = fun i => lagrangeBasis a i

end
end MathlibPlus.Open.Analysis.Claim16703
