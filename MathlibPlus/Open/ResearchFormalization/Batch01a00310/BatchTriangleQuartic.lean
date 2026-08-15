import Mathlib

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter

namespace MathlibPlus.Open.ResearchFormalization.Batch01a00310.BatchTriangleQuartic

open scoped Topology

def triangle (u : ℝ) : ℝ := max (1 - |u|) 0

def quartic (u : ℝ) : ℝ := Real.exp (-((10 : ℝ)^8) * u^4)

def convolution (f g : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ v : ℝ, f v * g (u - v)

def K (u : ℝ) : ℝ := convolution triangle quartic u

def phi (τ u : ℝ) : ℝ := Real.exp (-τ * u^2) * K u

def F (τ t : ℝ) (z : ℂ) : ℂ :=
  ∫ u : ℝ,
    Complex.ofReal (Real.exp (t * u^2) * phi τ u) *
      Complex.exp (Complex.I * z * (u : ℂ))

def evenFunction (f : ℝ → ℝ) : Prop := ∀ u, f (-u) = f u

def logConcaveFunction (f : ℝ → ℝ) : Prop :=
  (∀ u, 0 ≤ f u) ∧
    ∀ x y θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      f (θ * x + (1 - θ) * y) ≥
        Real.rpow (f x) θ * Real.rpow (f y) (1 - θ)

def strictLogConcaveFunction (f : ℝ → ℝ) : Prop :=
  (∀ u, 0 < f u) ∧
    ∀ x y θ : ℝ, x ≠ y → 0 < θ → θ < 1 →
      f (θ * x + (1 - θ) * y) >
        Real.rpow (f x) θ * Real.rpow (f y) (1 - θ)

def claim11923 : Prop :=
  evenFunction triangle ∧ logConcaveFunction triangle ∧
  evenFunction quartic ∧ logConcaveFunction quartic ∧
  evenFunction K ∧ (∀ u, 0 < K u) ∧ logConcaveFunction K ∧
  ∀ τ : ℝ, 0 < τ →
    strictLogConcaveFunction (phi τ) ∧
      ∀ t : ℝ, t < τ →
        strictLogConcaveFunction (fun u => Real.exp (t * u^2) * phi τ u)

def claim11930 : Prop :=
  ∀ (τ : ℝ), 0 < τ → ∀ (t : ℝ) (z : ℂ),
    deriv (fun s : ℝ => F τ s z) t =
      -deriv (fun w : ℂ => deriv (fun q : ℂ => F τ t q) w) z

end MathlibPlus.Open.ResearchFormalization.Batch01a00310.BatchTriangleQuartic
