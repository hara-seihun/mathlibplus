import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization

noncomputable def weightedVandermondeMinor
    (n r : ℕ) (x : Fin n → ℝ) (w : Fin n → ℝ)
    (I : Fin r → Fin n) (J : Fin r → ℕ) : ℝ :=
  Matrix.det (fun i j => w (I i) * x (I i) ^ J j)

noncomputable def shiftedHankelQuadratic
    (n r k : ℕ) (x : Fin n → ℝ) (w : Fin n → ℝ)
    (v : Fin r → ℝ) : ℝ :=
  ∑ i : Fin r, ∑ j : Fin r,
    v i * (∑ a : Fin n, w a * x a ^ (k + (i : ℕ) + (j : ℕ))) * v j

def positiveWeightedMomentCurvesClaim : Prop :=
  ∀ n : ℕ, ∀ hn : 0 < n, ∀ x : Fin n → ℝ, ∀ w : Fin n → ℝ,
    0 < x ⟨0, hn⟩ → StrictMono x →
      (∀ i : Fin n, 0 < w i) →
      (∀ r : ℕ, r ≤ n →
        ∀ I : Fin r → Fin n, StrictMono I →
          ∀ J : Fin r → ℕ, StrictMono J →
            0 < weightedVandermondeMinor n r x w I J) ∧
      (∀ r : ℕ, r ≤ n → ∀ k : ℕ,
        ∀ v : Fin r → ℝ, v ≠ 0 →
          0 < shiftedHankelQuadratic n r k x w v)

end MathlibPlus.Open.ResearchFormalization
