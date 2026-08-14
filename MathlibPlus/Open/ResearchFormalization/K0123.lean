import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.K0123

open Filter MeasureTheory
open scoped BigOperators Interval Topology

noncomputable section

/-- The band endpoint used by the reciprocal-capacity equilibrium. -/
def b : ℝ := Real.pi / 2

/-- The density displayed in the admitted equilibrium claim, extended by zero
outside the positive axis so that it is a genuine function on `ℝ`. -/
def rhoStar (z : ℝ) : ℝ :=
  if 0 < z ∧ z < b then
    (z⁻¹) ^ 2 * (1 - Real.sqrt (1 - (z / b) ^ 2))
  else if b ≤ z then
    (z⁻¹) ^ 2
  else
    0

/-- The constrained class in the leading reciprocal-capacity problem. -/
def admissibleDensity (rho : ℝ → ℝ) : Prop :=
  (∀ z : ℝ, 0 < z → 0 ≤ rho z ∧ rho z ≤ (z⁻¹) ^ 2) ∧
    (∫ z in Set.Ioi (0 : ℝ), rho z) = 1

/-- The logarithmic energy appearing in the admitted claims. -/
def constrainedEnergy (rho : ℝ → ℝ) : ℝ :=
  ∫ z in Set.Ioi (0 : ℝ),
    ∫ w in Set.Ioi (0 : ℝ),
      Real.log |z ^ 2 - w ^ 2| * rho z * rho w

/-- The equilibrium potential and saturated-vacancy action. -/
def equilibriumPotential (z : ℝ) : ℝ :=
  2 * ∫ w in Set.Ioi (0 : ℝ), Real.log |z ^ 2 - w ^ 2| * rhoStar w

def holeAction (z : ℝ) : ℝ :=
  4 * (Real.arcosh (z / b) - Real.sqrt (1 - b ^ 2 / z ^ 2))

def realPow (x p : ℝ) : ℝ := Real.rpow x p

/-- Claim 8857. -/
def claim8857 : Prop :=
  ∀ (gamma lambda : ℕ → ℝ),
    (∀ i : ℕ, lambda i = (gamma i)⁻¹) →
      Tendsto
          (fun i : ℕ => gamma i /
            (2 * Real.pi * (i : ℝ) / Real.log (i : ℝ)))
          atTop (𝓝 1) →
        ∀ (index : ℕ → ℕ) (t : ℝ),
          0 < t →
            Tendsto
                (fun n : ℕ => (index n : ℝ) / (n : ℝ))
                atTop (𝓝 t) →
              Tendsto
                (fun n : ℕ =>
                  (2 * Real.pi * (n : ℝ) / Real.log (n : ℝ)) *
                    lambda (index n))
                atTop (𝓝 t⁻¹)

/-- The push-forward of positive Lebesgue capacity by `t ↦ 1/t`. -/
def reciprocalCapacity : Measure ℝ :=
  Measure.map (fun t : ℝ => t⁻¹)
    (volume.restrict (Set.Ioi (0 : ℝ)))

def reciprocalDensityMeasure : Measure ℝ :=
  Measure.withDensity (volume.restrict (Set.Ioi (0 : ℝ)))
    (fun z : ℝ => ENNReal.ofReal ((z⁻¹) ^ 2))

/-- Claim 8858. -/
def claim8858 : Prop := reciprocalCapacity = reciprocalDensityMeasure

/-- Claim 8860. -/
def claim8860 : Prop :=
  admissibleDensity rhoStar ∧
    (∀ rho : ℝ → ℝ, admissibleDensity rho →
      constrainedEnergy rho ≤ constrainedEnergy rhoStar) ∧
    (∀ rho : ℝ → ℝ, admissibleDensity rho →
      constrainedEnergy rho = constrainedEnergy rhoStar →
        ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))), rho z = rhoStar z) ∧
    (∀ z : ℝ, 0 < z → z < b →
      rhoStar z = (z⁻¹) ^ 2 * (1 - Real.sqrt (1 - (z / b) ^ 2))) ∧
    (∀ z : ℝ, 0 < z → z < b → rhoStar z < (z⁻¹) ^ 2) ∧
    (∀ z : ℝ, b ≤ z → rhoStar z = (z⁻¹) ^ 2)

/-- Claim 8861. -/
def claim8861 : Prop :=
  ∀ z : ℝ, 0 < z →
    rhoStar z =
      2 * ∫ u in Set.Ioc (0 : ℝ) 1,
        (if z < b / u then 1 else 0) /
          (Real.pi * Real.sqrt ((b / u) ^ 2 - z ^ 2))

/-- Claim 8863. -/
def claim8863 : Prop :=
  (∫ z in Set.Ioi (0 : ℝ), rhoStar z) = 1 ∧
    (∫ z in Set.Ioi b, rhoStar z) = b⁻¹ ∧
    b⁻¹ = 2 / Real.pi ∧
    (∫ z in Set.Ioo (0 : ℝ) b, rhoStar z) = 1 - 2 / Real.pi

/-- Claim 8867. -/
def claim8867 : Prop :=
  (∀ z : ℝ, 0 < z → z < b →
      (z⁻¹) ^ 2 - rhoStar z =
        (z⁻¹) ^ 2 * Real.sqrt (1 - (z / b) ^ 2)) ∧
    Tendsto
      (fun z : ℝ =>
        ((z⁻¹) ^ 2 - rhoStar z) /
          ((Real.sqrt 2 / realPow b (5 / 2 : ℝ)) *
            Real.sqrt (b - z)))
      (nhdsWithin b (Set.Iio b)) (𝓝 1)

/-- Claim 8868. -/
def claim8868 : Prop :=
  ∀ z : ℝ, b < z →
    equilibriumPotential z - equilibriumPotential b = holeAction z

/-- Claim 8869. -/
def claim8869 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧
      ∀ epsilon : ℝ, 0 < epsilon → epsilon < epsilon₀ →
        |holeAction (b * (1 + epsilon)) -
            (8 * Real.sqrt 2 / 3) * realPow epsilon (3 / 2 : ℝ)| ≤
          C * realPow epsilon (5 / 2 : ℝ)

/-- Claim 8880. -/
def claim8880 : Prop :=
  (∀ y : ℝ, 0 < y → y < b →
      equilibriumPotential y = equilibriumPotential b) ∧
    (∀ z : ℝ, b < z →
      equilibriumPotential z - equilibriumPotential b =
        4 * (Real.arcosh (z / b) - Real.sqrt (1 - b ^ 2 / z ^ 2)))

end

end MathlibPlus.Open.ResearchFormalization.K0123
