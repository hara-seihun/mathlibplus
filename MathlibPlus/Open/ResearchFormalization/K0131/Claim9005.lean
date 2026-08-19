import MathlibPlus.Open.LinearAlgebra.Claim9007

namespace MathlibPlus.Open.ResearchFormalization.K0131Claim9005

open MathlibPlus.Open.LinearAlgebra
open Filter Asymptotics

noncomputable section

private def interfaceInfinityNorm (u : Fin 2 → ℝ) : ℝ :=
  max |u 0| |u 1|

/-- The three little-o costs that the admitted zero-action criterion assigns
 to transfer, vector-comparison, and layer-mass estimates. -/
private def zeroSpeedLayerCosts (L K : ℕ → ℝ) : Prop :=
  (fun N : ℕ => L N * (1 + Real.log (K N))) =o[atTop]
      (fun N : ℕ => (N : ℝ)) ∧
    (fun N : ℕ => L N * Real.log (2 * K N ^ 2)) =o[atTop]
      (fun N : ℕ => (N : ℝ)) ∧
    (fun N : ℕ =>
      Real.log (L N + 2) + 2 * L N * Real.log (2 * K N ^ 2)) =o[atTop]
      (fun N : ℕ => (N : ℝ))

/-- Claim 9005: a zero-action layer transfers the forbidden-side exponent
 between its two exact Jacobi interface endpoints in either direction. -/
def claim9005 : Prop :=
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
    zeroSpeedLayerCosts L K →
    ∀ (I : ℝ) (R : ℕ → ℝ)
      (u : ℕ → ℕ → (Fin 2 → ℝ)),
      (∀ N : ℕ,
        u N (q N + 1) =
          Matrix.mulVec
            (layerTransfer
              (jacobiTransferMatrix (fun r => a r N) (lam N))
              (p N) (q N - p N + 1))
            (u N (p N))) →
      (∀ e : ℕ → ℝ,
        e =o[atTop] (fun _ : ℕ => (1 : ℝ)) →
        (∀ᶠ N : ℕ in atTop,
          R N ≤ Real.exp (-(N : ℝ) * I + (N : ℝ) * e N) *
            (interfaceInfinityNorm (u N (q N + 1))) ^ 2) →
        ∃ e' : ℕ → ℝ,
          e' =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
          ∀ᶠ N : ℕ in atTop,
            R N ≤ Real.exp (-(N : ℝ) * I + (N : ℝ) * e' N) *
              (interfaceInfinityNorm (u N (p N))) ^ 2) ∧
      (∀ e : ℕ → ℝ,
        e =o[atTop] (fun _ : ℕ => (1 : ℝ)) →
        (∀ᶠ N : ℕ in atTop,
          R N ≤ Real.exp (-(N : ℝ) * I + (N : ℝ) * e N) *
            (interfaceInfinityNorm (u N (p N))) ^ 2) →
        ∃ e' : ℕ → ℝ,
          e' =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
          ∀ᶠ N : ℕ in atTop,
            R N ≤ Real.exp (-(N : ℝ) * I + (N : ℝ) * e' N) *
              (interfaceInfinityNorm (u N (q N + 1))) ^ 2)

end

end MathlibPlus.Open.ResearchFormalization.K0131Claim9005
