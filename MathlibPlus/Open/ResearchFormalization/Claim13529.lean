import Mathlib

namespace MathlibPlus.Open.ResearchFormalization

def claim13529_two_output_source_obstruction : Prop :=
  ∀ (x : ℝ), 0 ≤ x → x ≤ 1 →
    ∀ (κ : ℂ), κ ≠ 0 →
      ∀ (σ : ℂ), (σ = 1 ∨ σ = -1) →
        let d : ℝ := 2 + x
        let splitBasis : Fin 3 → ℝ → ℂ := fun i U =>
          ![(1 : ℂ), (Real.cosh U : ℂ), (Real.sinh U : ℂ)] i
        let compactBasis : Fin 3 → ℝ → ℂ := fun j Φ =>
          ![(1 : ℂ), (Real.cos Φ : ℂ), (Real.sin Φ : ℂ)] j
        let target : ℝ → ℝ → ℂ := fun U Φ =>
          (d : ℂ) * (Real.cosh U : ℂ) - 2 * (Real.cos Φ : ℂ) +
            σ * κ * (Real.sinh U : ℂ) * (Real.sin Φ : ℂ)
        let targetMatrix : Matrix (Fin 3) (Fin 3) ℂ :=
          !![0, -2, 0; d, 0, 0; 0, 0, σ * κ]
        let evaluateMatrix : Matrix (Fin 3) (Fin 3) ℂ → ℝ → ℝ → ℂ :=
          fun A U Φ =>
            Finset.sum Finset.univ (fun i =>
              splitBasis i U *
                Finset.sum Finset.univ (fun j => A i j * compactBasis j Φ))
        let twoOutputSource : Prop :=
          ∃ L : Matrix (Fin 3) (Fin 2) ℂ,
          ∃ B : Matrix (Fin 2) (Fin 2) ℂ,
          ∃ R : Matrix (Fin 2) (Fin 3) ℂ,
            ∀ U Φ : ℝ,
              target U Φ = evaluateMatrix (L * B * R) U Φ
        2 ≤ d ∧ d ≤ 3 ∧
          (∀ U Φ : ℝ, target U Φ = evaluateMatrix targetMatrix U Φ) ∧
          Matrix.det targetMatrix = 2 * σ * (d : ℂ) * κ ∧
          Matrix.det targetMatrix ≠ 0 ∧ ¬ twoOutputSource

end MathlibPlus.Open.ResearchFormalization
