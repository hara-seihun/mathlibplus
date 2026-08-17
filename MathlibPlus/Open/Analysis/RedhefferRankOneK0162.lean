import MathlibPlus.Open.Analysis.RedhefferSingularValues

open scoped BigOperators

noncomputable section

namespace MathlibPlus.Open.Analysis.RedhefferRankOneK0162

open MathlibPlus.Open.Analysis.RedhefferSingularValues

/-- The update vector and first basis vector in the one-based divisibility
indexing used by the Redheffer matrices. -/
def redhefferUpdateVector (n : ℕ) : Fin n → ℝ :=
  fun i => if i.1 = 0 then 0 else 1

def redhefferFirstBasisVector (n : ℕ) : Fin n → ℝ :=
  fun i => if i.1 = 0 then 1 else 0

def redhefferOuterProduct {n : ℕ} (v w : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => v i * w j

/-- The normalized anomaly is the exact `D⁻¹ A` matrix and the stated
rank-one perturbation of the identity. -/
def normalizedRedhefferAnomalyIsRankOne : Prop :=
  ∀ (n : ℕ), 0 < n →
    let u := redhefferUpdateVector n
    let e₁ := redhefferFirstBasisVector n
    let v : Fin n → ℝ := ((redhefferD n)⁻¹).mulVec u
    (redhefferB n = (redhefferD n)⁻¹ * redhefferA n) ∧
      redhefferB n =
        (1 : Matrix (Fin n) (Fin n) ℝ) +
          redhefferOuterProduct v e₁

end MathlibPlus.Open.Analysis.RedhefferRankOneK0162

end
