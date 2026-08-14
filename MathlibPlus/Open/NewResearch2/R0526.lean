import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.R0526

private def legProduct (A : Multiset ℕ) (y w : ℚ) : ℚ :=
  (A.map (fun a => 1 + w * y ^ a)).prod

private noncomputable def legProductPolynomial (A : Multiset ℕ) (y : ℚ) : Polynomial ℚ :=
  (A.map (fun a => 1 + Polynomial.C (y ^ a) * Polynomial.X)).prod

private def sideProduct (A : Multiset ℕ) (u z : ℚ) : ℚ :=
  (A.map (fun a => (z + (1 - u - z) * u ^ a) / (1 - u))).prod

private noncomputable def firstOrderOperator (N d : ℕ) (F : ℚ → ℚ → ℚ) (y w : ℚ) : ℚ :=
  (N : ℚ) * (1 - y) * F y w + (d : ℚ) * (y + 2 * w) * F y w
    - y * (1 - y) * deriv (fun t : ℚ => F t w) y
    + w * (w / y - 2 * w - y) * deriv (fun t : ℚ => F y t) w

private noncomputable def sideDerivativeTerm (A : Multiset ℕ) (u z : ℚ) : ℚ :=
  let d : ℚ := A.card
  let n : ℚ := A.sum
  let y := u
  let w := (1 - u - z) / z
  let t := 1 + w
  let P := sideProduct A
  t⁻¹ * (
      (n * (1 - y) + d * (y + 2 * w)) * P u z
        - y * (1 - y) *
            (deriv (fun v : ℚ => P v z) u - t⁻¹ * deriv (fun v : ℚ => P u v) z)
        + w * (w / y - 2 * w - y) *
            (d * t⁻¹ * P u z - (1 - y) * (t⁻¹) ^ 2 * deriv (fun v : ℚ => P u v) z))

/-- The birational side-product change of variables, with the leg multiset retained. -/
def claim22367 : Prop :=
  ∀ (A : Multiset ℕ) (d N : ℕ),
    A.card = d → A.sum = N →
      ∀ (u z : ℚ), z ≠ 0 → u ≠ 1 →
        let y := u
        let w := (1 - u - z) / z
        sideProduct A u z = (1 + w)⁻¹ ^ d * legProduct A y w ∧
          Polynomial.natDegree (legProductPolynomial A y) ≤ d

/-- The first-order side differential term in the chart. -/
def claim22368 : Prop :=
  ∀ (A : Multiset ℕ) (d N : ℕ),
    A.card = d → A.sum = N →
      ∀ (u z : ℚ), z ≠ 0 → u ≠ 1 → u ≠ 0 →
        let y := u
        let w := (1 - u - z) / z
        sideDerivativeTerm A u z =
          (1 + w)⁻¹ ^ (d + 1) * firstOrderOperator N d (legProduct A) y w

/-- Cyclotomic specialization separates finite multisets of leg lengths. -/
def claim22375 : Prop :=
  ∀ (A C : Multiset ℕ),
    (∀ u : ℚ, u ≠ 1 → sideProduct A u 1 = sideProduct C u 1) → A = C

end MathlibPlus.Open.NewResearch2.R0526
