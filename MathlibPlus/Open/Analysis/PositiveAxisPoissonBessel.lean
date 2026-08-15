import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.PositiveAxisPoissonBessel

noncomputable section

/-- The order-one Bessel function, written by its defining power series. -/
def besselJOne (z : ℝ) : ℝ :=
  ∑' k : ℕ,
    ((-1 : ℝ) ^ k * (z / 2) ^ (2 * k + 1)) /
      ((Nat.factorial k : ℝ) * (Nat.factorial (k + 1) : ℝ))

/-- The generalized Laguerre polynomial `L_k^1`. -/
def laguerreOne (k : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    (Nat.choose (k + 1) (k - j) : ℝ) * (-t) ^ j /
      (Nat.factorial j : ℝ)

/-- The finite-cutoff integral of `L_(n-1)^1` against the centered
finite-place expression from the claim's repair context. -/
def centeredFinitePlaceIntegral (X n : ℕ) : ℝ :=
  if 2 ≤ X then
    (∑ m ∈ Finset.Icc 2 X,
        (ArithmeticFunction.vonMangoldt m / (m : ℝ)) *
          laguerreOne (n - 1) (Real.log (m : ℝ))) -
      ∫ t in Set.Icc (0 : ℝ) (Real.log (X : ℝ)), laguerreOne (n - 1) t
  else 0

/-- The finite-place Li moments in natural arithmetic cutoff order. -/
def finitePlaceLiMoment (n : ℕ) : ℝ :=
  if 1 ≤ n then
    Filter.limUnder Filter.atTop (fun X : ℕ => centeredFinitePlaceIntegral X n)
  else 0

/-- The critical Poisson smoothing of the finite-place Li moments. -/
def phi (u : ℝ) : ℝ :=
  Real.exp (-u ^ 2) *
    ∑' n : ℕ,
      if 1 ≤ n then
        finitePlaceLiMoment n * u ^ (2 * n) / (Nat.factorial n : ℝ)
      else 0

/-- The finite natural cutoff on the positive-axis Poisson--Bessel sum. -/
def positiveAxisPoissonBesselPartial (X : ℕ) (u : ℝ) : ℝ :=
  ∑ m ∈ Finset.Icc 2 X,
    (ArithmeticFunction.vonMangoldt m / (m : ℝ)) *
      (u / Real.sqrt (Real.log (m : ℝ))) *
        besselJOne (2 * u * Real.sqrt (Real.log (m : ℝ)))

/-- Exact positive-axis Poisson--Bessel transform, including natural-order
and compact-local-uniform convergence. -/
def exactPositiveAxisPoissonBesselTransform : Prop :=
  (∀ u : ℝ, 0 < u →
    phi u =
      -1 + Filter.limUnder Filter.atTop
        (fun X : ℕ => positiveAxisPoissonBesselPartial X u)) ∧
  (∀ K : Set ℝ, IsCompact K → K ⊆ Set.Ioi 0 →
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        ∀ u : ℝ, u ∈ K →
          |positiveAxisPoissonBesselPartial X u - (phi u + 1)| < ε)

end

end MathlibPlus.Open.Analysis.PositiveAxisPoissonBessel
