import Mathlib

open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.C0020Claims317_319

noncomputable section

/-- Exact A4 derivative-matrix scaling: the coefficient sequence is tied to the
Cayley generating function, and the step-kernel convergence records both the
Hilbert--Schmidt and consequent operator-norm forms. -/
def claim317 : Prop :=
  let cayley : ℂ → ℂ := fun s => (1 + s) / (1 - s)
  let aPrime : ℂ → ℂ := fun v =>
    (15 * v ^ 6 + 416 * v ^ 5 + 236 * v ^ 4 + 5504 * v ^ 3 +
        8400 * v ^ 2 + 10240 * v + 6720) /
      (30 * (v - 2) ^ 2 * (v + 2) ^ 5)
  let Phi : ℝ → ℂ → ℂ := fun r s =>
    cayley s ^ 2 * aPrime (cayley s / (r : ℂ))
  let c : ℝ → ℝ := fun u =>
    (1 + u) * Real.exp u + Real.exp (-u) *
      (-(4 / 45) * u ^ 4 + (16 / 45) * u ^ 3 + (1 / 3) * u ^ 2 -
        (7 / 6) * u + 3 / 4)
  ∃ S : ℕ → ℕ → ℝ → ℝ,
    (∀ (r : ℝ), 0 < r → ∀ s t : ℂ,
      ‖s‖ < 1 → ‖t‖ < 1 → s ≠ t →
      HasSum
        (fun ij : ℕ × ℕ =>
          (S ij.1 ij.2 (1 / r) : ℂ) * s ^ ij.1 * t ^ ij.2)
        (((1 - s) * (1 - t)) / (2 * (1 - s * t)) *
          ((Phi r s - Phi r t) / (s - t)))) ∧
    ∀ (α : ℝ), 0 < α →
      ∀ (n : ℕ → ℕ) (r : ℕ → ℝ),
        (∀ k, 0 < r k) →
        Tendsto r atTop atTop →
        Tendsto (fun k => (n k : ℝ) / r k) atTop (𝓝 α) →
        let P : (k : ℕ) → Fin (n k) → Fin (n k) → ℝ := fun k i j =>
          (if i = j then 1 / (2 * r k) else 0) -
            S i j (1 / r k) / (r k) ^ 2
        let stepKernel : ℕ → ℝ → ℝ → ℝ := fun k x y =>
          ∑ i : Fin (n k), ∑ j : Fin (n k),
            if x ∈ Ico ((i : ℕ) / r k) (((i : ℕ) + 1) / r k) ∧
                y ∈ Ico ((j : ℕ) / r k) (((j : ℕ) + 1) / r k) then
              r k * ((if i = j then 1 / (2 * r k) else 0) - P k i j)
            else 0
        let kernel : ℝ → ℝ → ℝ := fun x y => c (x + y) + c |x - y|
        Tendsto
          (fun k => ∫ x in Ico 0 α, ∫ y in Ico 0 α,
            (stepKernel k x y - kernel x y) ^ 2)
          atTop (𝓝 0) ∧
        ∀ ε : ℝ, 0 < ε →
          ∀ᶠ k in atTop, ∀ f : ℝ → ℝ,
            IntegrableOn (fun x => f x ^ 2) (Ico 0 α) →
            (∫ x in Ico 0 α,
                (∫ y in Ico 0 α,
                  (stepKernel k x y - kernel x y) * f y) ^ 2) ≤
              ε ^ 2 * ∫ x in Ico 0 α, f x ^ 2

/-- The compact positive A4 integral operator has a simple, continuous,
strictly increasing top eigenvalue, with exactly one crossing of one half. -/
def claim319 : Prop :=
  let c : ℝ → ℝ := fun u =>
    (u + 1) * Real.exp u + Real.exp (-u) *
      (-(4 / 45 : ℝ) * u ^ 4 + (16 / 45 : ℝ) * u ^ 3 +
        (1 / 3 : ℝ) * u ^ 2 - (7 / 6 : ℝ) * u + 3 / 4)
  ∃ topEigenvalue : ℝ → ℝ,
    (∀ α : ℝ, 0 < α →
      let μ : Measure ℝ := volume.restrict (Set.Icc 0 α)
      ∃ K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ,
        IsCompactOperator K ∧
          (∀ f : Lp ℝ 2 μ,
            let g : ℝ → ℝ := fun x => ∫ y,
              (c (x + y) + c |x - y|) * f y ∂μ
            ∃ hg : MemLp g 2 μ, K f = hg.toLp g) ∧
          (∀ x ∈ Set.Icc (0 : ℝ) α, ∀ y ∈ Set.Icc (0 : ℝ) α,
            0 < c (x + y) + c |x - y|) ∧
          0 < topEigenvalue α ∧
          ∃ v : Lp ℝ 2 μ,
            v ≠ 0 ∧
              K v = (topEigenvalue α) • v ∧
              (∀ (r : ℝ) (w : Lp ℝ 2 μ),
                w ≠ 0 → K w = r • w → r ≤ topEigenvalue α) ∧
              ∀ w : Lp ℝ 2 μ,
                K w = (topEigenvalue α) • w → ∃ a : ℝ, w = a • v) ∧
    ContinuousOn topEigenvalue (Set.Ioi 0) ∧
    StrictMonoOn topEigenvalue (Set.Ioi 0) ∧
    Tendsto topEigenvalue (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) ∧
    Tendsto topEigenvalue atTop atTop ∧
    ∃! α : ℝ, 0 < α ∧ topEigenvalue α = 1 / 2

end

end MathlibPlus.Open.ResearchFormalization.C0020Claims317_319
