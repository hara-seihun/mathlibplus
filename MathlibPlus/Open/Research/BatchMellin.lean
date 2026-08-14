import Mathlib

open MeasureTheory Set

namespace MathlibPlus.Open.Research.Mellin

noncomputable section

/-- A bounded-type quotient on an open complex domain. -/
def boundedTypeOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  ∃ g h : ℂ → ℂ,
    AnalyticOnNhd ℂ g U ∧ AnalyticOnNhd ℂ h U ∧
      (∀ z ∈ U, h z ≠ 0) ∧
      (∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ z ∈ U, ‖g z‖ ≤ Cg) ∧
      (∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ z ∈ U, ‖h z‖ ≤ Ch) ∧
      (∀ z ∈ U, f z = g z / h z)

def rightHalfPlane (α : ℝ) : Set ℂ := {s | α < s.re}

/-- Claim 3701. -/
def boundedHalfPlaneNormalizationOfCompactLiteral : Prop :=
  ∀ (L : ℝ) (κ : ℝ → ℂ),
    0 < L → IntegrableOn κ (Icc (-L) L) →
      let Fhat : ℂ → ℂ := fun s =>
        ∫ t in Icc (-L) L,
          κ t * Complex.exp ((s - (1 / 2 : ℂ)) * (t : ℂ))
      let B : ℂ → ℂ := fun s =>
        Complex.exp (-L * (s - (1 / 2 : ℂ))) * Fhat s
      (∀ s, B s = 0 ↔ Fhat s = 0) ∧
        (∀ s, Complex.exp (-L * (s - (1 / 2 : ℂ))) ≠ 0) ∧
        (∀ s, 1 / 2 < s.re →
          ‖B s‖ ≤ ∫ t in Icc (-L) L, ‖κ t‖) ∧
        (∀ α, 1 / 2 < α → Fhat ≠ 0 →
          boundedTypeOn Fhat (rightHalfPlane α))

end

end MathlibPlus.Open.Research.Mellin
