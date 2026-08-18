import Mathlib
import MathlibPlus.Analysis.ReciprocalXi
import MathlibPlus.Open.ResearchFormalization.O0252.Claim15011
import MathlibPlus.Open.ResearchFormalization.O0252.Claim15013

open Set Filter
open scoped Topology

namespace MathlibPlus.Open.ResearchFormalization.O0252

noncomputable section

def xiCarrier15024 (z : ℂ) : ℂ :=
  MathlibPlus.Analysis.ReciprocalXi.centeredXi (Complex.I * z)

def transitionScaleReal15024 (k : ℕ) (L : ℝ) : ℝ :=
  Real.rpow L ((1 : ℝ) / (2 * (k : ℝ)))

def profileValue15024
    (P : Polynomial ℝ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  Polynomial.eval
    (z ^ 2 / (transitionScaleReal15024 k L : ℂ) ^ 2)
    (P.map Complex.ofRealHom)

def diniFactor15024 (L : ℝ) (z : ℂ) : ℂ :=
  (z * Complex.sin ((L : ℂ) * z) -
      (1 / 2 : ℂ) * Complex.cos ((L : ℂ) * z)) /
    (z ^ 2 + (1 / 4 : ℂ))

def diniFactorHat15024 (L : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (L : ℂ) * z) * diniFactor15024 L z

def conformalCarrier15024
    (P : Polynomial ℝ) (k : ℕ) (L : ℝ) (z : ℂ) : ℂ :=
  xiCarrier15024 z * profileValue15024 P k L z / (2 * (Real.pi : ℂ))

def logarithmBranch15024
    (U : Set ℂ) (C G : ℂ → ℂ) (a : ℝ) (logC : ℂ → ℂ) : Prop :=
  IsOpen U ∧
    IsSimplyConnected U ∧
      (∀ z : ℂ, z ∈ U → 0 < z.im) ∧
        AnalyticOnNhd ℂ logC U ∧
          (∀ z : ℂ, z ∈ U →
            C z ≠ 0 ∧ G z ≠ 0 ∧ a ≠ 0 ∧
              Complex.exp (logC z) = C z / ((a : ℂ) * G z))

def conformalAction15024
    (k : ℕ) (α L a : ℝ) (P : Polynomial ℝ)
    (logC : ℂ → ℂ) (z : ℂ) : ℂ :=
  (α : ℂ) * z ^ (2 * k) -
      Complex.I * (L : ℂ) * z -
      ((5 / 2 : ℝ) * L : ℂ) -
    logC z

def actionReal15024
    (k : ℕ) (α L a : ℝ) (P : Polynomial ℝ)
    (logC : ℂ → ℂ) (z : ℂ) : ℝ :=
  (conformalAction15024 k α L a P logC z).re

def actionImag15024
    (k : ℕ) (α L a : ℝ) (P : Polynomial ℝ)
    (logC : ℂ → ℂ) (z : ℂ) : ℝ :=
  (conformalAction15024 k α L a P logC z).im

def goodActionChart15024
    (k : ℕ) (α L a y₀ y₁ δ ε : ℝ) (P : Polynomial ℝ)
    (U : Set ℂ) (I : Set ℝ) (logC : ℂ → ℂ) : Prop :=
  1 ≤ k ∧
    0 < α ∧
      0 < L ∧
        0 < a ∧
          0 < y₀ ∧
            y₀ < y₁ ∧
              y₁ < 1 / 2 ∧
                0 < δ ∧
                  δ < (1 / 2 : ℝ) * min y₀ ((1 / 2 : ℝ) - y₁) ∧
                    0 < ε ∧
                      ε < 1 / 3 ∧
                        Polynomial.eval 0 P = 1 ∧
                          let T := transitionScaleReal15024 k L
                          let κ : ℝ → ℝ := fun y =>
                            Real.rpow (((5 / 2 : ℝ) - y) / α)
                              ((1 : ℝ) / (2 * (k : ℝ)))
                          let x₁ := κ y₁ * T
                          let x₂ := κ y₀ * T
                          let y_b := y₀ - 2 * δ
                          let y_t := y₁ + 2 * δ
                          I.Nonempty ∧
                            IsPreconnected I ∧
                              I ⊆ Set.Ioo x₁ x₂ ∧
                                logarithmBranch15024 U
                                  (conformalCarrier15024 P k L)
                                  (diniFactorHat15024 L) a logC ∧
                                  AnalyticOnNhd ℂ
                                    (conformalAction15024 k α L a P logC) U ∧
                                  (∀ x : ℝ, x ∈ I →
                                    ∀ y : ℝ, y ∈ Set.Icc y_b y_t →
                                      ((x : ℂ) + Complex.I * (y : ℂ)) ∈ U) ∧
                                  (∀ x : ℝ, x ∈ I →
                                    actionReal15024 k α L a P logC
                                        ((x : ℂ) + Complex.I * (y_b : ℂ)) ≤
                                      -δ * L ∧
                                    actionReal15024 k α L a P logC
                                        ((x : ℂ) + Complex.I * (y_t : ℂ)) ≥
                                      δ * L) ∧
                                  (∀ x : ℝ, x ∈ I →
                                    ∀ y : ℝ, y ∈ Set.Icc y_b y_t →
                                      deriv
                                          (fun t : ℝ =>
                                            actionReal15024 k α L a P logC
                                              ((x : ℂ) + Complex.I * (t : ℂ))) y ≥
                                        (1 - 3 * ε) * L)

def claim15024_uniqueActionZeroGraph : Prop :=
  ∀ (k : ℕ) (α L a y₀ y₁ δ ε : ℝ) (P : Polynomial ℝ)
    (U : Set ℂ) (I : Set ℝ) (logC : ℂ → ℂ),
    goodActionChart15024 k α L a y₀ y₁ δ ε P U I logC →
      let y_b := y₀ - 2 * δ
      let y_t := y₁ + 2 * δ
      ∃ y : ℝ → ℝ,
        AnalyticOnNhd ℝ y I ∧
          (∀ x : ℝ, x ∈ I →
            y_b < y x ∧
              y x < y_t ∧
                actionReal15024 k α L a P logC
                    ((x : ℂ) + Complex.I * (y x : ℂ)) = 0 ∧
                (∀ y' : ℝ, y_b < y' → y' < y_t →
                  actionReal15024 k α L a P logC
                      ((x : ℂ) + Complex.I * (y' : ℂ)) = 0 →
                    y' = y x)) ∧
          (∀ x : ℝ, x ∈ I →
            let z := (x : ℂ) + Complex.I * (y x : ℂ)
            let p :=
              (deriv (conformalAction15024 k α L a P logC) z).re
            let q :=
              (deriv (conformalAction15024 k α L a P logC) z).im
            q ≠ 0 ∧
              deriv
                  (fun t : ℝ =>
                    actionImag15024 k α L a P logC
                      ((t : ℂ) + Complex.I * (y t : ℂ))) x =
                (p ^ 2 + q ^ 2) / q)

end

end MathlibPlus.Open.ResearchFormalization.O0252
