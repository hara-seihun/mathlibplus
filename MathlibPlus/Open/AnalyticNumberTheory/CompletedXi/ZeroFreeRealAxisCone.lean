import Mathlib

/-!
# Zero-free real-axis cone for shifted Riemann xi

Statement-fidelity registry node for admitted claim 516 (`C-0033`).  The completed
Riemann xi function uses mathlib's entire pole-cancelled completion.  The two cones
are written with `Complex.arg`; the negative-axis cone is the positive-axis cone
applied to `-z`.
-/

open Complex Set

namespace MathlibPlus.Open.AnalyticNumberTheory.CompletedXi

/-- The zeros of shifted completed xi stay strictly inside the vertical strip, are
separated from the real axis, and therefore admit a star-shaped zero-free
neighborhood consisting of two open real-axis cones and a disk. -/
noncomputable def zeroFreeRealAxisCone : Prop :=
  let xi : ℂ → ℂ := fun s ↦
    (1 / 2 : ℂ) * (s * (s - 1) * completedRiemannZeta₀ s + 1)
  let F : ℂ → ℂ := fun z ↦ xi ((1 / 2 : ℂ) + z)
  let zeros : Set ℂ := {z | F z = 0}
  let eta : ℝ := sInf ((fun z : ℂ ↦ |z.im|) '' zeros)
  (∀ z : ℂ, F z = 0 → |z.re| < 1 / 2) ∧
    (∀ x : ℝ, F (x : ℂ) ≠ 0) ∧
    IsDiscrete zeros ∧
    0 < eta ∧
    ∃ θ γ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧ 0 < γ ∧
      let coneDisk : Set ℂ :=
        {z | |Complex.arg z| < θ ∨ |Complex.arg (-z)| < θ ∨ ‖z‖ < γ}
      StarConvex ℝ 0 coneDisk ∧
        (∀ z : ℂ, z ∈ coneDisk → F z ≠ 0) ∧
        ∀ x : ℝ, (x : ℂ) ∈ coneDisk

end MathlibPlus.Open.AnalyticNumberTheory.CompletedXi
