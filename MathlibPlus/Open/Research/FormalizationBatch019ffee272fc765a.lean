import Mathlib

namespace MathlibPlus
namespace Open
namespace Research

noncomputable def gammaMoment (α : ℝ) (k : ℕ) : ℝ :=
  Real.Gamma (α + k) / Real.Gamma α

noncomputable def gammaMomentMinor (α : ℝ) {n : ℕ} (r c : Fin n → ℕ) : ℝ :=
  Matrix.det (fun i j : Fin n => gammaMoment α (r i + c j))

def gammaMomentsStrictlyTotallyPositive : Prop :=
  ∀ α : ℝ, 0 < α →
    ∀ n : ℕ, 0 < n →
      ∀ r c : Fin n → ℕ,
        StrictMono r → StrictMono c →
          0 < gammaMomentMinor α r c

end Research
end Open
end MathlibPlus
