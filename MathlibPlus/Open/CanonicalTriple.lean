import Mathlib

/-!
# Canonical rank-four connected-triple edge

This registry node formalizes admitted claim 181 from legacy packet `C-0012`.
The packet's numerator is expanded from its defining mixed logarithmic derivative,
so the declaration does not rely on an omitted coefficient table.
-/

namespace MathlibPlus.Open.CanonicalTriple

open scoped BigOperators

/-- For the completed rank-four Bezout determinant with moments
`m_n = 1 + a r^n + b s^n + c t^n` and factorial scaling
`h_n = m_n / (2n)!`, the connected mixed-log-derivative numerator is positive
on every canonical degenerate edge `(i⁻², j⁻², 0)`, `2 ≤ i < j`.

The nested `deriv`s spell out `∂_a ∂_b ∂_c log Δ₄ (0,0,0)`, and multiplication
by `2^29` is exactly the packet's normalization of `P`. -/
def canonicalDegenerateEdgePositive : Prop :=
  let moment := fun (r s t a b c : ℝ) (n : ℕ) =>
    1 + a * r ^ n + b * s ^ n + c * t ^ n
  let scaledMoment := fun (r s t a b c : ℝ) (n : ℕ) =>
    moment r s t a b c n / (Nat.factorial (2 * n) : ℝ)
  let completedEntry := fun (r s t a b c : ℝ) (i j : Fin 4) =>
    ∑ k ∈ Finset.range (min i.1 j.1 + 1),
      ((i.1 + j.1 + 1 - 2 * k : ℕ) : ℝ) *
        scaledMoment r s t a b c k *
        scaledMoment r s t a b c (i.1 + j.1 + 1 - k)
  let delta := fun (r s t a b c : ℝ) =>
    Matrix.det (fun i j : Fin 4 => completedEntry r s t a b c i j)
  let numerator := fun (r s t : ℝ) =>
    (2 : ℝ) ^ 29 *
      deriv (fun a =>
        deriv (fun b =>
          deriv (fun c => Real.log (delta r s t a b c)) 0) 0) 0
  ∀ i j : ℕ, 2 ≤ i → i < j →
    0 < numerator (1 / (i : ℝ) ^ 2) (1 / (j : ℝ) ^ 2) 0

end MathlibPlus.Open.CanonicalTriple
