import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Fixed-order local Loewner transport

Registry statement for admitted claim 199 from legacy packet `C-0014`.
-/

namespace MathlibPlus.Open.Analysis

/-- For a real-analytic function on an interval and a fixed positive order, pointwise
positive semidefiniteness of the signed confluent derivative matrices is equivalent
to positive semidefiniteness of all negative Loewner matrices on distinct nodes.
Strict local positivity gives strict positivity on distinct nodes, and principal
submatrices inherit semidefinite positivity. -/
def fixedOrderLocalLoewnerTransport : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (H : ℝ → ℝ) (I : Set ℝ),
    Set.OrdConnected I → I.Nontrivial → AnalyticOn ℝ H I →
      let confluent : ℝ → Matrix (Fin n) (Fin n) ℝ := fun x i j =>
        (-1 : ℝ) ^ (i.1 + j.1 + 1) *
          iteratedDeriv (i.1 + j.1 + 1) H x / (i.1 + j.1 + 1).factorial
      let negativeLoewner : (k : ℕ) → (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ :=
        fun _k x i j =>
          if x i = x j then -deriv H (x i)
          else -(H (x i) - H (x j)) / (x i - x j)
      ((∀ x ∈ I, (confluent x).PosSemidef) ↔
          ∀ (x : Fin n → ℝ), (∀ i, x i ∈ I) → Function.Injective x →
            (negativeLoewner n x).PosSemidef) ∧
        ((∀ x ∈ I, (confluent x).PosDef) →
          ∀ (x : Fin n → ℝ), (∀ i, x i ∈ I) → Function.Injective x →
            (negativeLoewner n x).PosDef) ∧
        ∀ (m : ℕ) (e : Fin m → Fin n), Function.Injective e →
          ∀ (x : Fin n → ℝ), (negativeLoewner n x).PosSemidef →
            (negativeLoewner m (x ∘ e)).PosSemidef

end MathlibPlus.Open.Analysis
