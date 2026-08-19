import MathlibPlus.Open.LinearAlgebra.Claim9007

namespace MathlibPlus.Open.ResearchFormalization.K0131Claim9006

open MathlibPlus.Open.LinearAlgebra
open Filter Asymptotics

noncomputable section

private def zeroSpeedLayerCosts (L K : ℕ → ℝ) : Prop :=
  (fun N : ℕ => L N * (1 + Real.log (K N))) =o[atTop]
      (fun N : ℕ => (N : ℝ)) ∧
    (fun N : ℕ => L N * Real.log (2 * K N ^ 2)) =o[atTop]
      (fun N : ℕ => (N : ℝ)) ∧
    (fun N : ℕ =>
      Real.log (L N + 2) + 2 * L N * Real.log (2 * K N ^ 2)) =o[atTop]
      (fun N : ℕ => (N : ℝ))

/-- Claim 9006: polynomial conditioning and a sufficiently short exact
 N-indexed Jacobi layer force all of its speed-N costs to vanish. -/
def claim9006 : Prop :=
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
    (∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, K N ≤ (N : ℝ) ^ C) →
    (fun N : ℕ => L N) =o[atTop]
      (fun N : ℕ => (N : ℝ) / Real.log (N : ℝ)) →
    zeroSpeedLayerCosts L K

end

end MathlibPlus.Open.ResearchFormalization.K0131Claim9006
