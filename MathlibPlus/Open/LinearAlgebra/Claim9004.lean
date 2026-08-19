import MathlibPlus.Open.LinearAlgebra.Claim9007

namespace MathlibPlus.Open.LinearAlgebra

open scoped BigOperators
open Filter Asymptotics

noncomputable section

/-- Claim 9004: when the logarithmic layer length is sublinear at speed `N`,
the transfer, inverse-transfer, vector-comparison, and layer-mass costs from
Claims 9001--9003 are all zero at speed `N`. -/
def claim9004 : Prop :=
  ∀ (p q : ℕ → ℕ) (a : ℕ → ℕ → ℝ) (lam c : ℕ → ℝ),
    (hPQ : ∀ N : ℕ, p N ≤ q N) →
    (∀ N : ℕ, 0 < c N) →
    (∀ N : ℕ, ∀ r ∈ Finset.Icc (p N) (q N + 1),
      0 < a r N) →
    let L : ℕ → ℝ := fun N =>
      ((q N - p N + 1 : ℕ) : ℝ)
    let K : ℕ → ℝ := fun N =>
      localConditioning (fun r => a r N) (lam N) (c N) (p N) (q N)
        (hPQ N)
    (fun N : ℕ => L N * (1 + Real.log (K N))) =o[atTop]
        (fun N : ℕ => (N : ℝ)) →
    (fun N : ℕ => L N * Real.log (2 * K N ^ 2)) =o[atTop]
        (fun N : ℕ => (N : ℝ)) ∧
    (fun N : ℕ => L N * Real.log (2 * K N ^ 2)) =o[atTop]
        (fun N : ℕ => (N : ℝ)) ∧
    (fun N : ℕ => L N * Real.log (2 * K N ^ 2)) =o[atTop]
        (fun N : ℕ => (N : ℝ)) ∧
    (fun N : ℕ =>
      Real.log (L N + 2) + 2 * L N * Real.log (2 * K N ^ 2)) =o[atTop]
        (fun N : ℕ => (N : ℝ))

end

end MathlibPlus.Open.LinearAlgebra
