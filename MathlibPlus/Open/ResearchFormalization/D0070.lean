import Mathlib

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.D0070

def projectiveColumnMatrix {d : ℕ}
    (γ : ℝ → Fin d → ℝ) (q : Fin (d + 1) → ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => Fin.cases (1 : ℝ) (fun k => γ (q j) k) i

def projectiveTP {d : ℕ} (γ : ℝ → Fin d → ℝ) : Prop :=
  ∀ q : Fin (d + 1) → ℝ,
    StrictMono q → 0 < Matrix.det (projectiveColumnMatrix γ q)

end MathlibPlus.Open.ResearchFormalization.D0070
