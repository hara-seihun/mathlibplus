import MathlibPlus.Analysis.Claim7317

namespace MathlibPlus.Analysis.Claim7319

/-- First ECT derivative-collocation step. -/
def firstECTDerivativeCollocationStep_claim7319 : Prop :=
  ∀ (F : ℝ → ℝ) (k : ℕ) (x : ℝ) (y : Fin k → ℝ),
    (∀ (m : ℕ), 0 < m → m ≤ k → ∀ t : ℝ,
      0 < MathlibPlus.Analysis.Claim7317.orientedConfluentHankelMinor_claim7317 F m t) →
    StrictMono y →
    0 < Matrix.det (fun i j : Fin k =>
      iteratedDeriv i.1 F (x - y j))

end MathlibPlus.Analysis.Claim7319
