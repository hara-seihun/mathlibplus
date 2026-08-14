import Mathlib

namespace MathlibPlus.Open.NewResearch2.ThetaKernel

noncomputable section
open scoped BigOperators
open Set

/-- The standard theta-shell variable appearing in the Riemann kernel. -/
def thetaShellVariable (n : ℕ) (u : ℝ) : ℝ :=
  Real.pi * (n : ℝ) ^ 2 * Real.exp (2 * u)

def thetaShell (n : ℕ) (u : ℝ) : ℝ :=
  Real.exp (u / 2) *
    (4 * thetaShellVariable n u ^ 2 - 6 * thetaShellVariable n u) *
      Real.exp (-thetaShellVariable n u)

def thetaKernelPhi (u : ℝ) : ℝ :=
  ∑' n : ℕ, if 1 ≤ n then thetaShell n u else 0

def centeredXiFromKernel (Phi : ℝ → ℝ) (t : ℝ) : ℝ :=
  2 * ∫ u in Ioi (0 : ℝ), Phi u * Real.cos (t * u)

def claim4653_riemann_theta_kernel_fourier_representation
    (Xi Phi : ℝ → ℝ) : Prop :=
  ∀ t : ℝ,
    Xi t = 2 * ∫ u in Ioi (0 : ℝ), Phi u * Real.cos (t * u)

def claim4655_individual_theta_shell (phi : ℝ) (n : ℕ) (u : ℝ) : Prop :=
  1 ≤ n → 0 ≤ u →
    phi = Real.exp (u / 2) *
      (4 * thetaShellVariable n u ^ 2 - 6 * thetaShellVariable n u) *
        Real.exp (-thetaShellVariable n u)

def claim4656_complete_theta_kernel_as_shell_sum : Prop :=
  (∀ u : ℝ, 0 ≤ u →
    HasSum (fun n : ℕ => if 1 ≤ n then thetaShell n u else 0) (thetaKernelPhi u)) ∧
  ContDiffOn ℝ (⊤ : ℕ∞) thetaKernelPhi (Ici (0 : ℝ))

end
end MathlibPlus.Open.NewResearch2.ThetaKernel
