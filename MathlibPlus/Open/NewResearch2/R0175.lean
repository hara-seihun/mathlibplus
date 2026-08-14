import Mathlib

namespace MathlibPlus.Open.NewResearch2.R0175

open scoped BigOperators
open scoped Topology

private noncomputable def elementarySymmetricReal
    (r k : ℕ) (y : Fin r → ℝ) : ℝ :=
  ∑ S : Finset (Fin r),
    if S.card = k then S.prod (fun i => y i) else 0

private def omittedWindowExponent (r s k j : ℕ) : ℕ :=
  if j < r - k then s + j else s + j + 1

private def vandermonde (r : ℕ) (y : Fin r → ℝ) : ℝ :=
  Matrix.det (fun i j : Fin r => y i ^ j.val)

/-- Claim 18556: omitting the indicated exponent from a consecutive-window
alternant gives the Vandermonde times the elementary-symmetric factor. -/
def claim18556_omittedColumnAlternantIdentity : Prop :=
  ∀ r s k : ℕ, k ≤ r → ∀ y : Fin r → ℝ,
    Matrix.det
        (fun i j : Fin r =>
          y i ^ omittedWindowExponent r s k j.val) =
      vandermonde r y *
        (∏ i : Fin r, y i) ^ s * elementarySymmetricReal r k y

/-- Claim 18557: the consecutive-window Cauchy--Binet circuit is the
corresponding Vandermonde--elementary-symmetric polynomial. -/
def claim18557_consecutiveWindowCauchyBinetCircuitIdentity : Prop :=
  ∀ r s : ℕ, ∀ A : ℕ → ℕ → ℝ, ∀ J : Fin r → ℕ,
    StrictMono J → ∀ y : Fin r → ℝ,
      (Finset.sum (Finset.range (r + 1)) (fun k =>
        Matrix.det
            (fun i j : Fin r =>
              y i ^ omittedWindowExponent r s k j.val) *
          Matrix.det
            (fun i j : Fin r =>
              A (omittedWindowExponent r s k i.val) (J j)))) =
        vandermonde r y *
          (∏ i : Fin r, y i) ^ s *
            (Finset.sum (Finset.range (r + 1)) (fun k =>
              Matrix.det
                  (fun i j : Fin r =>
                    A (omittedWindowExponent r s k i.val) (J j)) *
                elementarySymmetricReal r k y))

end MathlibPlus.Open.NewResearch2.R0175
