import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4534FourNodeObstruction

noncomputable section

/-- Claim 53171: four distinct nodes have a nonzero barycentric kernel
vector for the degree-two moment map, so neither endpoint evaluation factors
through those moments, even after multiplying coordinates by nonzero weights. -/
def fourNodeEndpointMomentObstruction_claim53171 : Prop :=
  ∀ (x : Fin 4 → ℝ),
    (∀ i j : Fin 4, i ≠ j → x i ≠ x j) →
      let c : Fin 4 → ℝ := fun i =>
        ((Finset.univ.erase i).prod (fun l => x i - x l))⁻¹
      let moments : (Fin 4 → ℝ) → (Fin 3 → ℝ) := fun q j =>
        ∑ i : Fin 4, q i * (x i) ^ (j : ℕ)
      (∀ i : Fin 4, c i ≠ 0) ∧
        (∀ j : Fin 3, ∑ i : Fin 4, c i * (x i) ^ (j : ℕ) = 0) ∧
        (¬ ∃ φ : (Fin 3 → ℝ) →ₗ[ℝ] ℝ,
          ∀ q : Fin 4 → ℝ, q 0 = φ (moments q)) ∧
        (¬ ∃ ψ : (Fin 3 → ℝ) →ₗ[ℝ] ℝ,
          ∀ q : Fin 4 → ℝ, q (Fin.last 3) = ψ (moments q)) ∧
        (∀ a : Fin 4 → ℝ,
          (∀ i : Fin 4, a i ≠ 0) →
            let qₐ : Fin 4 → ℝ := fun i => c i / a i
            let weightedMoments : (Fin 4 → ℝ) → (Fin 3 → ℝ) :=
              fun q j =>
                ∑ i : Fin 4, a i * q i * (x i) ^ (j : ℕ)
            (∀ j : Fin 3, weightedMoments qₐ j = 0) ∧
              a 0 * qₐ 0 ≠ 0 ∧
                a (Fin.last 3) * qₐ (Fin.last 3) ≠ 0 ∧
                (¬ ∃ φ : (Fin 3 → ℝ) →ₗ[ℝ] ℝ,
                  ∀ q : Fin 4 → ℝ,
                    a 0 * q 0 = φ (weightedMoments q)) ∧
                (¬ ∃ ψ : (Fin 3 → ℝ) →ₗ[ℝ] ℝ,
                  ∀ q : Fin 4 → ℝ,
                    a (Fin.last 3) * q (Fin.last 3) =
                      ψ (weightedMoments q)))

end

end MathlibPlus.Open.ResearchFormalization.R4534FourNodeObstruction
