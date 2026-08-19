import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R4941FiniteDifference

noncomputable section

/-- Claim 53090: the order-d finite-difference vector annihilates all
polynomial moments through degree d while retaining both endpoint
coordinates, including the explicit source-independent linear-factorization
obstruction. -/
def finiteDifferenceEndpointObstruction_claim53090 : Prop :=
  ∀ d : ℕ,
    let m : ℕ := d + 1
    let x : Fin (m + 1) → ℝ := fun i => (i : ℕ)
    let w : Fin (m + 1) → ℝ := fun i =>
      (-1 : ℝ) ^ (i : ℕ) * (Nat.choose m (i : ℕ) : ℝ)
    (∀ j : Fin m, ∑ i : Fin (m + 1), w i * (x i) ^ (j : ℕ) = 0) ∧
      w 0 = 1 ∧ w (Fin.last m) = (-1 : ℝ) ^ m ∧
      (∀ i : Fin (m + 1), w i ≠ 0) ∧
      (¬ ∃ φ : (Fin m → ℝ) →ₗ[ℝ] ℝ,
        ∀ q : Fin (m + 1) → ℝ,
          q 0 = φ (fun j =>
            ∑ i : Fin (m + 1), q i * (x i) ^ (j : ℕ))) ∧
      (¬ ∃ ψ : (Fin m → ℝ) →ₗ[ℝ] ℝ,
        ∀ q : Fin (m + 1) → ℝ,
          q (Fin.last m) = ψ (fun j =>
            ∑ i : Fin (m + 1), q i * (x i) ^ (j : ℕ)))

end

end MathlibPlus.Open.ResearchFormalization.R4941FiniteDifference
