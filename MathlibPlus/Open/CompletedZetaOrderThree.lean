import Mathlib

/-!
# Global order-three completed-zeta Loewner positivity

Statement-fidelity formalization of admitted claim 209.  The completed xi source,
its radial logarithmic derivative `H`, the confluent matrices, and the negative
Loewner matrices are all inlined.  “Matrix monotone of order three” is represented
by the equivalent three-node negative-Loewner positive-semidefiniteness condition
stated in the claim.
-/

namespace MathlibPlus.Open.Analysis.CompletedZeta

/-- The completed-zeta radial kernel has strict confluent Loewner positivity in
order three; all negative Loewner matrices of order at most three are PSD, so any
RH-falsifying failure has order at least four. -/
def globalOrderThreePositivity : Prop :=
  let ξ : ℝ → ℝ := fun s =>
    ((1 / 2 : ℂ) * (s : ℂ) * ((s : ℂ) - 1) *
      completedRiemannZeta (s : ℂ)).re
  let X : ℝ → ℝ := fun r => ξ (1 / 2 + r)
  let L : ℝ → ℝ := fun r => deriv X r / X r
  let H : ℝ → ℝ := fun x => L (Real.sqrt x) / Real.sqrt x
  let C : (n : ℕ) → ℝ → Matrix (Fin n) (Fin n) ℝ := fun _ x i j =>
    (-1 : ℝ) ^ (i.val + j.val + 1) *
      (deriv^[i.val + j.val + 1]) H x /
        (Nat.factorial (i.val + j.val + 1) : ℝ)
  let Q : (n : ℕ) → (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ := fun _ q i j =>
    if i = j then -deriv H (q i)
    else (H (q i) - H (q j)) / (q j - q i)
  (∀ x : ℝ, 1 / 4 < x → (C 3 x).PosDef) ∧
    (∀ (n : ℕ), 1 ≤ n → n ≤ 3 →
      ∀ q : Fin n → ℝ,
        StrictMono q →
        (∀ i, 1 / 4 < q i) →
        (Q n q).PosSemidef) ∧
    (¬RiemannHypothesis →
      ∀ (n : ℕ), 1 ≤ n →
        ∀ q : Fin n → ℝ,
          StrictMono q →
          (∀ i, 1 / 4 < q i) →
          ¬(Q n q).PosSemidef → 4 ≤ n)

end MathlibPlus.Open.Analysis.CompletedZeta
