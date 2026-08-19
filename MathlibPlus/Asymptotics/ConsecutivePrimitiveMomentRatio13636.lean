import Mathlib

open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology

namespace MathlibPlus.Asymptotics

noncomputable section

/-!
Claim 13636 uses the source-defined one-shell Laplace moment, primitive
completed-theta moment, and canonical saddle/Lambert interfaces.  The two
relative asymptotics are written as exact little-oh relations.
-/

def consecutivePrimitiveMomentRatio_claim13636 : Prop :=
  let phase : ℕ → ℝ → ℝ := fun n u =>
    2 * (n : ℝ) * Real.log u + u / 2 - Real.pi * Real.exp (2 * u)
  let J : ℕ → ℝ := fun n =>
    ∫ u in Set.Ioi (0 : ℝ), Real.exp (phase n u)
  let expectedSquare : ℕ → ℝ := fun n =>
    (∫ u in Set.Ioi (0 : ℝ), u ^ 2 * Real.exp (phase n u)) / J n
  let saddle : ℕ → ℝ := fun n =>
    sInf {u : ℝ | 0 < u ∧ ∀ v : ℝ, 0 < v → phase n v ≤ phase n u}
  let W₀ : ℝ → ℝ := fun x =>
    sInf {w : ℝ | 0 < w ∧ w * Real.exp w = x}
  let theta : ℝ → ℝ := fun u =>
    ∑' m : ℕ,
      Real.exp
        (-Real.pi * (((m + 1 : ℕ) : ℝ) ^ 2) * Real.exp (2 * u))
  let I : ℕ → ℝ := fun n =>
    ∫ u in Set.Ioi (0 : ℝ),
      Real.exp (u / 2) * theta u * u ^ (2 * n)
  let t : ℕ → ℝ := fun n =>
    2 * I n / (Nat.factorial (2 * n) : ℝ)
  (∀ x : ℝ, 0 < x →
      0 < W₀ x ∧ W₀ x * Real.exp (W₀ x) = x) ∧
    (∀ n : ℕ, 1 ≤ n →
      0 < saddle n ∧
        ∀ v : ℝ, 0 < v → phase n v ≤ phase n (saddle n)) ∧
    (∀ n : ℕ, 1 ≤ n →
      J n / J (n - 1) = expectedSquare (n - 1)) ∧
    (fun n : ℕ =>
        J n / J (n - 1) - saddle (n - 1) ^ 2)
      =o[atTop] (fun n : ℕ => saddle (n - 1) ^ 2) ∧
    (fun n : ℕ =>
        t n / t (n - 1) -
          (W₀ (2 * (n : ℝ) / Real.pi)) ^ 2 /
            (16 * (n : ℝ) ^ 2))
      =o[atTop] (fun n : ℕ =>
        (W₀ (2 * (n : ℝ) / Real.pi)) ^ 2 /
          (16 * (n : ℝ) ^ 2))

end

end MathlibPlus.Asymptotics
