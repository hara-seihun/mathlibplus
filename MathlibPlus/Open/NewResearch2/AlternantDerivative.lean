import Mathlib

open scoped BigOperators
open MeasureTheory
open intervalIntegral

namespace MathlibPlus.Open.NewResearch2.AlternantDerivative

/-- A strict-TP kernel and its fixed-width cell integral can coexist with a
    negative sparse confluent derivative minor. -/
def sparseDerivativeMinorCanBeNegative18547 : Prop :=
  ∃ (K : ℝ → ℝ → ℝ) (δ : ℝ) (r : ℕ)
    (x y : Fin r → ℝ) (orders : Fin r → ℕ),
    0 < δ ∧
      (∃ i : Fin r, 0 < orders i) ∧
      (let strictTP : (ℝ → ℝ → ℝ) → Prop :=
        fun F =>
          ∀ (m : ℕ) (a b : Fin m → ℝ),
            (∀ i j : Fin m, i < j → a i < a j) →
            (∀ i j : Fin m, i < j → b i < b j) →
            0 < Matrix.det (fun i j => F (a i) (b j))
       let cellIntegral : ℝ → ℝ → ℝ :=
         fun s t => ∫ z in s - δ..s + δ, K z t
       strictTP K ∧
         strictTP cellIntegral ∧
         (∀ i j : Fin r, i < j → x i < x j) ∧
         (∀ i j : Fin r, i < j → y i < y j) ∧
         Matrix.det
             (fun i j =>
               iteratedDeriv (orders i) (fun z => K z (y j)) (x i)) < 0)

end MathlibPlus.Open.NewResearch2.AlternantDerivative
