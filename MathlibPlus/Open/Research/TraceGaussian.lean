import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.TraceGaussian

/-- The positive two-Gaussian mixture from Claim 7119. -/
def gaussianMixture (a b r t : ℝ) : ℝ :=
  Real.exp (-a * t ^ 2) + r * Real.exp (-b * t ^ 2)

/-- The order-two signed trace determinant, specialized from the Hankel determinant. -/
def traceDet2 (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  (deriv F t) ^ 2 - F t * deriv (deriv F) t

/-- The signed order-m trace determinant used in Claim 7120. -/
def traceDet (m : ℕ) (F : ℝ → ℝ) (t : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m * (m - 1) / 2) *
    Matrix.det (fun i j : Fin m => iteratedDeriv (i.val + j.val) F t)

/-- Claim 7119: the exact two-Gaussian order-two determinant formula and witness. -/
def claim7119 : Prop :=
  (∀ (a b r t : ℝ),
    traceDet2 (gaussianMixture a b r) t =
      let u := t ^ 2
      2 * a * Real.exp (-2 * a * u) +
        2 * b * r ^ 2 * Real.exp (-2 * b * u) +
        2 * r * Real.exp (-(a + b) * u) *
          ((a + b) - 2 * (a - b) ^ 2 * u)) ∧
  traceDet2 (gaussianMixture 1 2 10) 0 = 462 ∧
  traceDet2 (gaussianMixture 1 2 10) (4 / Real.sqrt 5) < 0 ∧
  (∀ t : ℝ, 0 < gaussianMixture 1 2 10 t)

/-- Claim 7120: a pure Gaussian propagates exactly as a Gaussian in every order. -/
def claim7120 : Prop :=
  ∀ (m : ℕ) (a t : ℝ),
    1 ≤ m →
    0 < a →
    traceDet m (fun x : ℝ => Real.exp (-a * x ^ 2)) 0 ≠ 0 ∧
    traceDet m (fun x : ℝ => Real.exp (-a * x ^ 2)) t /
      traceDet m (fun x : ℝ => Real.exp (-a * x ^ 2)) 0 =
      Real.exp (-(m : ℝ) * a * t ^ 2)

end MathlibPlus.Open.Research.TraceGaussian

end
