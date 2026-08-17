import Mathlib
import MathlibPlus.Open.ResearchFormalization.OpenArcClosedComponentZeroCounts15387

open MeasureTheory Set
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.O0324

noncomputable section

open MathlibPlus.Open.ResearchFormalization.OpenArcClosedComponentZeroCounts15387

/-- The regular open-arc data from the exact projective Stokes carrier. -/
def regularOpenStokesArc
    (U : Set ℂ) (X D : ℂ → ℂ) (γ : ℝ → ℂ) (θ : ℝ → ℝ)
    (a b : ℝ) : Prop :=
  IsOpen U ∧
    AnalyticOnNhd ℂ X U ∧
      AnalyticOnNhd ℂ D U ∧
        a < b ∧
          Set.InjOn γ (Set.Icc a b) ∧
            ContDiffOn ℝ 1 γ (Set.Icc a b) ∧
              (∀ s : ℝ, s ∈ Set.Icc a b →
                γ s ∈ U ∧
                  X (γ s) ≠ 0 ∧
                    D (γ s) ≠ 0) ∧
                ContDiffOn ℝ 1 θ (Set.Icc a b) ∧
                  (∀ s : ℝ, s ∈ Set.Icc a b →
                    HasDerivAt θ
                      (‖projectiveOmega X D (γ s)‖) s) ∧
                    (∀ s : ℝ, s ∈ Set.Icc a b →
                      ‖deriv γ s‖ = 1) ∧
                      (∀ s : ℝ, s ∈ Set.Icc a b →
                        projectiveOmega X D (γ s) ≠ 0) ∧
                        (∀ s : ℝ, s ∈ Set.Icc a b →
                          ‖projectivePi X D (γ s)‖ = 1) ∧
                          phaseLiftOnInterval
                            (projectivePi X D) γ θ a b

/-- Phase variation along a regular open arc. -/
noncomputable def openArcPhaseVariation
    (X D : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) : ℝ :=
  ∫ s in a..b,
    ‖projectiveOmega X D (γ s)‖ * ‖deriv γ s‖

/-- Zero-freeness is required only on the open arc; endpoints control whether
an endpoint lattice hit is counted. -/
def zeroFreeOpenArc
    (X D : ℂ → ℂ) (γ : ℝ → ℂ) (a b : ℝ) : Prop :=
  ∀ s : ℝ, s ∈ Set.Ioo a b → projectiveF X D (γ s) ≠ 0

/-- The exact regular closed-component data used for the endpoint equality
convention. -/
def regularClosedStokesComponent
    (U : Set ℂ) (X D : ℂ → ℂ) (γ : ℝ → ℂ) (θ : ℝ → ℝ)
    (P : ℝ) (n : ℕ) : Prop :=
  IsOpen U ∧
    AnalyticOnNhd ℂ X U ∧
      AnalyticOnNhd ℂ D U ∧
        0 < P ∧
          0 < n ∧
            Function.Periodic γ P ∧
              ContDiff ℝ 1 γ ∧
                Set.InjOn γ (Set.Ioc 0 P) ∧
                  (∀ s : ℝ,
                    γ s ∈ U ∧
                      X (γ s) ≠ 0 ∧
                        D (γ s) ≠ 0) ∧
                    (∀ s : ℝ, ‖deriv γ s‖ = 1) ∧
                      (∀ s : ℝ,
                        ‖projectivePi X D (γ s)‖ = 1 ∧
                          projectiveOmega X D (γ s) ≠ 0) ∧
                        ContDiff ℝ 1 θ ∧
                          (∀ s : ℝ,
                            HasDerivAt θ
                              (‖projectiveOmega X D (γ s)‖) s) ∧
                            (∀ s : ℝ,
                              Complex.exp
                                  (Complex.I * (θ s : ℂ)) =
                                projectivePi X D (γ s) /
                                  (‖projectivePi X D (γ s)‖ : ℂ)) ∧
                              (∀ s : ℝ,
                                θ (s + P) =
                                  θ s + 2 * Real.pi * (n : ℝ))

noncomputable def closedComponentPhaseVariation
    (X D : ℂ → ℂ) (γ : ℝ → ℂ) (P : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..P,
    ‖projectiveOmega X D (γ s)‖ * ‖deriv γ s‖

/-- The strict open-arc cap predicate whose failure records the endpoint
convention. -/
def universalStrictOpenArcCap : Prop :=
  ∀ (U : Set ℂ) (X D : ℂ → ℂ) (γ : ℝ → ℂ) (θ : ℝ → ℝ)
    (a b : ℝ),
    regularOpenStokesArc U X D γ θ a b →
      zeroFreeOpenArc X D γ a b →
        openArcPhaseVariation X D γ a b < 2 * Real.pi

/-- Claim 15388: a zero-free regular open Stokes arc has the non-strict
`2π` phase cap; strictness is not universal, while a degree-one closed
component realizes equality under its endpoint convention. -/
def claim15388_zeroFreeOpenArcPhaseCap : Prop :=
  (∀ (U : Set ℂ) (X D : ℂ → ℂ) (γ : ℝ → ℂ) (θ : ℝ → ℝ)
      (a b : ℝ),
    regularOpenStokesArc U X D γ θ a b →
      zeroFreeOpenArc X D γ a b →
        openArcPhaseVariation X D γ a b ≤ 2 * Real.pi) ∧
    ¬ universalStrictOpenArcCap ∧
    (∀ (U : Set ℂ) (X D : ℂ → ℂ) (γ : ℝ → ℂ) (θ : ℝ → ℝ)
        (P : ℝ) (n : ℕ),
      regularClosedStokesComponent U X D γ θ P n →
        n = 1 →
          closedComponentPhaseVariation X D γ P = 2 * Real.pi)

end

end MathlibPlus.Open.ResearchFormalization.O0324
