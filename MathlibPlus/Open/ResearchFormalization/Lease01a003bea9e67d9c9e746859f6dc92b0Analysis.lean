import Mathlib

open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization

/-- The dual polynomial and its exact values at the node sequence. -/
def claim1157 : Prop :=
  ∀ (e : ℕ), 1 ≤ e →
    ∀ (a : ℝ) (n : ℕ),
      let Q : ℝ → ℝ := fun x =>
        ∏ j ∈ Finset.range e, (x ^ 2 - (a + (j : ℝ)) ^ 2)
      let _F : ℝ → ℝ := fun x => Q x - Q 0
      let rising : ℝ → ℕ → ℝ := fun z m =>
        ∏ j ∈ Finset.range m, (z + (j : ℝ))
      Q (a + (n : ℝ)) =
        if n < e then 0 else
          ((Nat.factorial n : ℝ) / (Nat.factorial (n - e) : ℝ)) *
            rising (2 * a + (n : ℝ)) e

/-- Bellotti's exact coefficient pair and its directed numerical bounds. -/
def claim1198 : Prop :=
  let C : ℝ := 8.7979
  let D : ℝ := 132.94357
  let Astar : ℝ :=
    (C + 1 + ((10 : ℝ)⁻¹) ^ 80) /
        Real.rpow (108 * Real.log 10) (2 / 3 : ℝ) +
      (1.569 : ℝ) * C * Real.rpow D (1 / 3 : ℝ)
  let Bstar : ℝ := (2 / 9 : ℝ) * Real.sqrt (3 * D)
  (70.6994 < Astar ∧ Astar < 70.699401 ∧ Astar < 70.6995) ∧
    (4.43794 < Bstar ∧ Bstar < 4.4379437 ∧ Bstar < 4.43795)

/-- The first bump has exactly the asserted derivative sign interval. -/
def claim4676 : Prop :=
  let A : ℝ → ℝ := fun v => Real.pi * Real.exp (2 * v)
  let phi₁ : ℝ → ℝ := fun v =>
    2 * Real.exp (v / 2) * A v * (2 * A v - 3) * Real.exp (-A v)
  let Astar : ℝ := (15 + Real.sqrt 105) / 8
  let V : ℝ := (1 / 2 : ℝ) * Real.log (Astar / Real.pi)
  ∀ v : ℝ, 0 ≤ v →
    (-deriv phi₁ v < 0 ↔ 0 < v ∧ v < V)

/-- Integration by parts for the finite bump moments. -/
def claim4679 : Prop :=
  let A : ℝ → ℝ := fun v => Real.pi * Real.exp (2 * v)
  let phi₁ : ℝ → ℝ := fun v =>
    2 * Real.exp (v / 2) * A v * (2 * A v - 3) * Real.exp (-A v)
  let Astar : ℝ := (15 + Real.sqrt 105) / 8
  let V : ℝ := (1 / 2 : ℝ) * Real.log (Astar / Real.pi)
  let beta : ℕ → ℝ := fun n =>
    (2 : ℝ) / (Nat.factorial (2 * n) : ℝ) *
      ∫ v in (0 : ℝ)..V, deriv phi₁ v * v ^ (2 * n + 1)
  ∀ n : ℕ,
    beta n =
      2 * phi₁ V * V ^ (2 * n + 1) / (Nat.factorial (2 * n) : ℝ) -
        (2 * (2 * n + 1) : ℝ) / (Nat.factorial (2 * n) : ℝ) *
          ∫ v in (0 : ℝ)..V, phi₁ v * v ^ (2 * n)

/-- Positivity of the endpoint curvature constant. -/
def claim4680 : Prop :=
  let A : ℝ → ℝ := fun v => Real.pi * Real.exp (2 * v)
  let phi₁ : ℝ → ℝ := fun v =>
    2 * Real.exp (v / 2) * A v * (2 * A v - 3) * Real.exp (-A v)
  let Astar : ℝ := (15 + Real.sqrt 105) / 8
  let V : ℝ := (1 / 2 : ℝ) * Real.log (Astar / Real.pi)
  let cstar : ℝ := -deriv (deriv phi₁) V
  0 < cstar

/-- Watson's endpoint asymptotic for the bump moments, expressed as a ratio limit. -/
def claim4681 : Prop :=
  let A : ℝ → ℝ := fun v => Real.pi * Real.exp (2 * v)
  let phi₁ : ℝ → ℝ := fun v =>
    2 * Real.exp (v / 2) * A v * (2 * A v - 3) * Real.exp (-A v)
  let Astar : ℝ := (15 + Real.sqrt 105) / 8
  let V : ℝ := (1 / 2 : ℝ) * Real.log (Astar / Real.pi)
  let beta : ℕ → ℝ := fun n =>
    (2 : ℝ) / (Nat.factorial (2 * n) : ℝ) *
      ∫ v in (0 : ℝ)..V, deriv phi₁ v * v ^ (2 * n + 1)
  let cstar : ℝ := -deriv (deriv phi₁) V
  let asymptotic : ℕ → ℝ := fun n =>
    2 * cstar * V ^ (2 * n + 3) /
      ((Nat.factorial (2 * n) : ℝ) * (2 * n + 2) * (2 * n + 3))
  Filter.Tendsto (fun n : ℕ => beta n / asymptotic n) Filter.atTop (𝓝 (1 : ℝ))

end MathlibPlus.Open.ResearchFormalization
