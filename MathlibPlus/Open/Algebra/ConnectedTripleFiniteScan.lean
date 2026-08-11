import Mathlib

/-!
# Open finite connected-triple scan registry

A self-contained statement-fidelity repair for admitted claim 177 from packet
`C-0012`.  It does not depend on the rejected claim-174 numerator definition:
the factorial-scaled moments, completed rank-four determinant, mixed logarithmic
derivative, symmetry requirement, and local logarithm domain are all retained
inside this one registry proposition.
-/

open scoped BigOperators

namespace MathlibPlus.Open.Algebra.CompletedBezout

/-- The packet's exact finite scan consists of 84 triples
`2 ≤ i < j < k ≤ 10`; on every such triple, the unit-weight connected
cumulant `P(i⁻²,j⁻²,k⁻²) / 2²⁹` is positive.

The local numerator is required to be symmetric, repairing the substantive
omission for which the earlier claim-174-dependent submission was rejected.
Positivity of the determinant on a neighborhood of the derivative base point
makes the use of the real logarithm explicit rather than relying on its
irrelevant totalized values away from the completed-Bezout domain. -/
def finiteCanonicalTripleScan : Prop :=
  let Δ : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ := fun r s t a b c =>
    let m : ℕ → ℝ := fun j => 1 + a * r ^ j + b * s ^ j + c * t ^ j
    let h : ℕ → ℝ := fun j => m j / (Nat.factorial (2 * j) : ℝ)
    Matrix.det (fun i j : Fin 4 =>
      ∑ u ∈ Finset.range (min i.val j.val + 1),
        ((i.val + j.val + 1 - 2 * u : ℕ) : ℝ) *
          h u * h (i.val + j.val + 1 - u))
  let P : ℝ → ℝ → ℝ → ℝ := fun r s t =>
    (2 : ℝ) ^ 29 *
      deriv (fun a =>
        deriv (fun b =>
          deriv (fun c => Real.log (Δ r s t a b c)) 0) 0) 0
  let shells : Finset ℕ := Finset.Icc 2 10
  let triples : Finset (ℕ × ℕ × ℕ) :=
    (shells.product (shells.product shells)).filter
      (fun x => x.1 < x.2.1 ∧ x.2.1 < x.2.2)
  (∀ r s t : ℝ,
      P r s t = P r t s ∧
      P r s t = P s r t ∧
      P r s t = P s t r ∧
      P r s t = P t r s ∧
      P r s t = P t s r) ∧
    triples.card = 84 ∧
    ∀ x ∈ triples,
      let r := ((x.1 : ℝ) ^ 2)⁻¹
      let s := ((x.2.1 : ℝ) ^ 2)⁻¹
      let t := ((x.2.2 : ℝ) ^ 2)⁻¹
      (∃ ε : ℝ, 0 < ε ∧
        ∀ a b c : ℝ, |a| < ε → |b| < ε → |c| < ε →
          0 < Δ r s t a b c) ∧
      0 < P r s t / (2 : ℝ) ^ 29

end MathlibPlus.Open.Algebra.CompletedBezout
