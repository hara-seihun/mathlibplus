import Mathlib

open MeasureTheory
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.OpenArcClosedComponentZeroCounts15387

noncomputable section

abbrev UnitCircle := {w : ℂ // ‖w‖ = 1}

noncomputable def normalizeToCircle (z : ℂ) : UnitCircle := by
  classical
  by_cases hz : z = 0
  · exact ⟨1, by norm_num⟩
  · refine ⟨z / (‖z‖ : ℂ), ?_⟩
    rw [norm_div]
    simp [hz]

def finiteCoveringDegree {E X : Type*}
    [TopologicalSpace E] [TopologicalSpace X]
    (p : E → X) (n : ℕ) : Prop :=
  IsCoveringMap p ∧
    Function.Surjective p ∧
      ∀ x : X,
        Set.Finite {e : E | p e = x} ∧
          Set.ncard {e : E | p e = x} = n

/-- The exact projective fields used by the two zero-count statements. -/
def projectiveF (X D : ℂ → ℂ) : ℂ → ℂ := fun z => X z + D z

def projectivePi (X D : ℂ → ℂ) : ℂ → ℂ := fun z => -X z / D z

noncomputable def projectiveOmega (X D : ℂ → ℂ) : ℂ → ℂ :=
  fun z => deriv X z / X z - deriv D z / D z

/-- A phase lift is a function of the arc parameter, not a single-valued
function of the point of a closed component. -/
def phaseLiftOnInterval
    (Pi : ℂ → ℂ) (γ : ℝ → ℂ) (θ : ℝ → ℝ) (a b : ℝ) : Prop :=
  ContinuousOn θ (Set.Icc a b) ∧
    ∀ s : ℝ, s ∈ Set.Icc a b →
      Complex.exp (Complex.I * (θ s : ℂ)) =
        Pi (γ s) / (‖Pi (γ s)‖ : ℂ)

/-- Claim 15387: the open-arc lattice count and the closed-component
covering-degree count, with the phase speed tied to the projective logarithmic
 derivative and with a phase lift on the parameter universal cover. -/
def exactOpenArcAndClosedComponentZeroCounts_claim15387 : Prop :=
  (∀ (U : Set ℂ) (X D : ℂ → ℂ) (γ : ℝ → ℂ) (θ : ℝ → ℝ)
      (a b : ℝ),
    IsOpen U →
      AnalyticOnNhd ℂ X U →
      AnalyticOnNhd ℂ D U →
      a < b →
      Set.InjOn γ (Set.Icc a b) →
      ContDiffOn ℝ 1 γ (Set.Icc a b) →
      (∀ s : ℝ, s ∈ Set.Icc a b →
        γ s ∈ U ∧ X (γ s) ≠ 0 ∧ D (γ s) ≠ 0) →
      ContDiffOn ℝ 1 θ (Set.Icc a b) →
      (∀ s : ℝ, s ∈ Set.Icc a b →
        HasDerivAt θ
          (‖projectiveOmega X D (γ s)‖) s) →
      (∀ s : ℝ, s ∈ Set.Icc a b →
        ‖deriv γ s‖ = 1) →
      (∀ s : ℝ, s ∈ Set.Icc a b →
        projectiveOmega X D (γ s) ≠ 0) →
      (∀ s : ℝ, s ∈ Set.Icc a b →
        ‖projectivePi X D (γ s)‖ = 1) →
      phaseLiftOnInterval
        (projectivePi X D) γ θ a b →
      let F := projectiveF X D
      let V : ℝ :=
        ∫ s in a..b,
          ‖projectiveOmega X D (γ s)‖ * ‖deriv γ s‖
      let Nγ : ℕ :=
        Set.ncard
          {z : ℂ | z ∈ γ '' Set.Ioo a b ∧ F z = 0}
      (∀ s : ℝ, s ∈ Set.Ioo a b →
        (F (γ s) = 0 ↔
          ∃ k : ℤ, θ s = 2 * Real.pi * (k : ℝ))) ∧
        (V / (2 * Real.pi) - 1 ≤ (Nγ : ℝ) ∧
          (Nγ : ℝ) ≤ V / (2 * Real.pi) + 1)) ∧
  (∀ (U : Set ℂ) (X D : ℂ → ℂ) (γ : ℝ → ℂ) (θ : ℝ → ℝ)
      (P : ℝ) (n : ℕ),
    IsOpen U →
      AnalyticOnNhd ℂ X U →
      AnalyticOnNhd ℂ D U →
      0 < P →
      0 < n →
      Function.Periodic γ P →
      ContDiff ℝ 1 γ →
      Set.InjOn γ (Set.Ioc 0 P) →
      (∀ s : ℝ, γ s ∈ U ∧ X (γ s) ≠ 0 ∧ D (γ s) ≠ 0) →
      (∀ s : ℝ, ‖deriv γ s‖ = 1) →
      (∀ s : ℝ,
        ‖projectivePi X D (γ s)‖ = 1 ∧
          projectiveOmega X D (γ s) ≠ 0) →
      ContDiff ℝ 1 θ →
      (∀ s : ℝ, HasDerivAt θ
        (‖projectiveOmega X D (γ s)‖) s) →
      (∀ s : ℝ,
        Complex.exp (Complex.I * (θ s : ℂ)) =
          projectivePi X D (γ s) /
            (‖projectivePi X D (γ s)‖ : ℂ)) →
      (∀ s : ℝ,
        θ (s + P) = θ s + 2 * Real.pi * (n : ℝ)) →
      let F := projectiveF X D
      let Pi := projectivePi X D
      let V : ℝ :=
        ∫ s in (0 : ℝ)..P,
          ‖projectiveOmega X D (γ s)‖ * ‖deriv γ s‖
      let Nγ : ℕ :=
        Set.ncard
          {z : ℂ | z ∈ Set.range γ ∧ F z = 0}
      let p : {z : ℂ // z ∈ Set.range γ} → UnitCircle :=
        fun z => normalizeToCircle (Pi z)
      (∀ z : {z : ℂ // z ∈ Set.range γ},
        F z = 0 ↔ p z = ⟨1, by norm_num⟩) ∧
        finiteCoveringDegree p n ∧
        V = 2 * Real.pi * (n : ℝ) ∧
        Nγ = n)

end

end MathlibPlus.Open.ResearchFormalization.OpenArcClosedComponentZeroCounts15387
