import Mathlib

open scoped BigOperators

namespace MathlibPlus.Open.FormalizationBatch

/-- Positive Hermitian similitude, and the supplied Euler/alternating counter-comparisons. -/
def claim12291 : Prop :=
  (∀ (n : ℕ) (H F : Matrix (Fin n) (Fin n) ℂ) (q : ℝ),
      0 < q →
        (∀ i j, H i j = star (H j i)) →
        (∀ v : Fin n → ℂ, v ≠ 0 →
          0 < (∑ i, ∑ j, star (v i) * H i j * v j).re) →
        (∀ i j,
          ∑ k, ∑ l, star (F k i) * H k l * F l j =
            (q : ℂ) * H i j) →
        ((∀ i j,
            ∑ k, ∑ l,
              star (F k i / (Real.sqrt q : ℂ)) * H k l *
                (F l j / (Real.sqrt q : ℂ)) = H i j) ∧
          (∀ z : ℂ,
            (∃ v : Fin n → ℂ,
              v ≠ 0 ∧ ∀ i, ∑ j, F i j * v j = z * v i) →
              ‖z‖ = Real.sqrt q))) ∧
    (∀ g : ℕ,
      let E : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
        if i = 0 then
          if j = 0 then (1 - (g : ℝ)) else 1
        else if j = 0 then -1 else 0
      let Esym : Matrix (Fin 2) (Fin 2) ℝ := fun i j => E i j + E j i
      ¬ (∀ v : Fin 2 → ℝ, v ≠ 0 →
          0 < ∑ i, ∑ j, v i * Esym i j * v j)) ∧
    (let J : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
      if i = 0 then
        if j = 1 then 1 else 0
      else if j = 0 then -1 else 0
     ∀ F : Matrix (Fin 2) (Fin 2) ℝ, ∀ i j,
       ∑ k, ∑ l, F k i * J k l * F l j =
         (F 0 0 * F 1 1 - F 0 1 * F 1 0) * J i j) ∧
    (let J : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
      if i = 0 then
        if j = 1 then 1 else 0
      else if j = 0 then -1 else 0
     let Ffake : Matrix (Fin 2) (Fin 2) ℝ := fun i j =>
      if i = 0 then
        if j = 0 then 0 else -9
      else if j = 0 then 1 else -7
     (∀ i j, ∑ k, ∑ l, Ffake k i * J k l * Ffake l j = 9 * J i j) ∧
       (∀ z : ℝ,
         z * (z + 7) + 9 = 0 ↔
           z = (-7 + Real.sqrt 13) / 2 ∨
             z = (-7 - Real.sqrt 13) / 2) ∧
       (1.6971 < |(-7 + Real.sqrt 13) / 2| ∧
          |(-7 + Real.sqrt 13) / 2| < 1.6973 ∧
        5.3027 < |(-7 - Real.sqrt 13) / 2| ∧
          |(-7 - Real.sqrt 13) / 2| < 5.3029 ∧
        |(-7 + Real.sqrt 13) / 2| ≠ 3 ∧
        |(-7 - Real.sqrt 13) / 2| ≠ 3))

end MathlibPlus.Open.FormalizationBatch
