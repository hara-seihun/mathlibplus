import MathlibPlus.Open.LinearAlgebra.LayerTransferBound

namespace MathlibPlus.Open.LinearAlgebra

open scoped BigOperators
open Filter Asymptotics

noncomputable section

/-- Claim 9007: a regular-edge `N^(1/3)` layer with polynomial conditioning
has zero speed-`N` transfer cost, and the terminal-packet action is unchanged
across the layer. -/
def claim9007 : Prop :=
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
    (L =O[atTop] (fun N : ℕ => (N : ℝ) ^ (1 / 3 : ℝ))) →
    (∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, K N ≤ (N : ℝ) ^ C) →
    (fun N : ℕ => L N * (1 + Real.log (K N))) =o[atTop]
      (fun N : ℕ => (N : ℝ)) ∧
    (fun N : ℕ => L N * Real.log (2 * K N ^ 2)) =o[atTop]
      (fun N : ℕ => (N : ℝ)) ∧
    (fun N : ℕ =>
      Real.log (L N + 2) + 2 * L N * Real.log (2 * K N ^ 2)) =o[atTop]
        (fun N : ℕ => (N : ℝ)) ∧
    (∀ (I : ℝ) (R : ℕ → ℝ)
        (u : ℕ → ℕ → (Fin 2 → ℝ)),
      (∀ N : ℕ,
        u N (q N + 1) =
          Matrix.mulVec
            (layerTransfer (jacobiTransferMatrix (fun r => a r N)
              (lam N)) (p N) (q N - p N + 1))
            (u N (p N))) →
      (∀ e : ℕ → ℝ,
        e =o[atTop] (fun _ : ℕ => (1 : ℝ)) →
        (∀ᶠ N : ℕ in atTop,
          R N ≤ Real.exp (-(N : ℝ) * I + (N : ℝ) * e N) *
            (max |u N (q N + 1) 0| |u N (q N + 1) 1|) ^ 2) →
        ∃ e' : ℕ → ℝ,
          e' =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
          ∀ᶠ N : ℕ in atTop,
            R N ≤ Real.exp (-(N : ℝ) * I + (N : ℝ) * e' N) *
              (max |u N (p N) 0| |u N (p N) 1|) ^ 2) ∧
      (∀ e : ℕ → ℝ,
        e =o[atTop] (fun _ : ℕ => (1 : ℝ)) →
        (∀ᶠ N : ℕ in atTop,
          R N ≤ Real.exp (-(N : ℝ) * I + (N : ℝ) * e N) *
            (max |u N (p N) 0| |u N (p N) 1|) ^ 2) →
        ∃ e' : ℕ → ℝ,
          e' =o[atTop] (fun _ : ℕ => (1 : ℝ)) ∧
          ∀ᶠ N : ℕ in atTop,
            R N ≤ Real.exp (-(N : ℝ) * I + (N : ℝ) * e' N) *
              (max |u N (q N + 1) 0| |u N (q N + 1) 1|) ^ 2))

end

end MathlibPlus.Open.LinearAlgebra
