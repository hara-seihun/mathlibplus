import Mathlib

open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization

/-- The fixed-modulus boundary value and its alternating zeta series. -/
def claim8288 : Prop :=
  let mobiusCoprimeMellin : ℕ → ℝ → ℝ := fun N t =>
    ∑' b : {b : ℕ // Nat.Coprime b N},
      (ArithmeticFunction.moebius b.1 : ℝ) / (b.1 : ℝ) * Real.exp (-t * b.1)
  let zetaN : ℕ → ℕ → ℝ := fun N s =>
    ∑' n : {n : ℕ // Nat.Coprime n N},
      1 / (n.1 : ℝ) ^ s
  let C : ℕ → ℝ → ℝ := fun N lam =>
    (Nat.totient N : ℝ) / N *
      ∫ r in Set.Ioi (0 : ℝ),
        Real.exp (-r) * mobiusCoprimeMellin N (lam * r) / r
  let term : ℕ → ℕ → ℝ := fun N k =>
    if 1 ≤ k then
      ((-1 : ℝ) ^ (k + 1)) /
        ((k : ℝ) * (N : ℝ) ^ k * zetaN N (k + 1))
    else 0
  ∀ N : ℕ, Squarefree N → 2 ≤ N →
    C N N =
      1 - (Nat.totient N : ℝ) / N *
        ∑' k : {k : ℕ // 1 ≤ k}, term N k.1 ∧
      (∀ k : ℕ, 1 ≤ k →
        0 < ((-1 : ℝ) ^ (k + 1)) * term N k ∧
        ‖term N (k + 1)‖ ≤ ‖term N k‖)

/-- The logarithmic majorant for the finite-u boundary layer. -/
def claim8293 : Prop :=
  let mobiusCoprimeMellin : ℕ → ℝ → ℝ := fun N t =>
    ∑' b : {b : ℕ // Nat.Coprime b N},
      (ArithmeticFunction.moebius b.1 : ℝ) / (b.1 : ℝ) * Real.exp (-t * b.1)
  let K : ℕ → ℝ → ℝ → ℝ := fun N x y =>
    ∑' a : {a : ℕ // Nat.Coprime a N},
      Real.exp (-a.1 * y) / a.1 * mobiusCoprimeMellin N (a.1 * x)
  ∀ N : ℕ, Squarefree N → 2 ≤ N →
    ∀ u : ℝ, 0 < u →
      let q : ℝ := u / (1 - Real.exp (-u * N))
      q < 1 →
        |K N (u * N) u - Real.exp (-u * N)| ≤
          Real.exp (-u * N) * Real.log (1 / (1 - q))

end MathlibPlus.Open.ResearchFormalization
