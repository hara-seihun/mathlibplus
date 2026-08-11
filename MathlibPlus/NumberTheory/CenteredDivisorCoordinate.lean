import Mathlib

namespace MathlibPlus.NumberTheory

theorem centeredDivisorCoordinate
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (d : ℕ) (hd : d ∣ P.prod id) :
    let R_P : ℝ := P.prod (fun p ↦ (p : ℝ))
    let y_d : ℝ := Real.log d - (1 / 2 : ℝ) * Real.log R_P
    y_d = Real.log ((d : ℝ) / Real.sqrt R_P) := by
  have hRnat : 0 < P.prod id := by
    exact Finset.prod_pos (fun p hp ↦ (hP p hp).pos)
  have hdnat : 0 < d := Nat.pos_of_dvd_of_pos hd hRnat
  have hR : (0 : ℝ) < P.prod (fun p ↦ (p : ℝ)) :=
    Finset.prod_pos (fun p hp ↦ by exact_mod_cast (hP p hp).pos)
  have hd' : (0 : ℝ) < d := by exact_mod_cast hdnat
  have hsqrt : 0 < Real.sqrt (P.prod (fun p ↦ (p : ℝ))) := Real.sqrt_pos.2 hR
  dsimp
  rw [Real.log_div hd'.ne' hsqrt.ne', Real.log_sqrt hR.le]
  ring

end MathlibPlus.NumberTheory
