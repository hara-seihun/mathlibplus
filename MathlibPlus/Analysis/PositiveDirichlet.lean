import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.NormNum

namespace MathlibPlus.Analysis.PositiveDirichlet

/-- Finite-family form of claim 18766. -/
theorem vertical_bound
    (ι : Type*) [Fintype ι]
    (a : ι → ℝ) (n : ι → ℕ)
    (ha : ∀ j, 0 ≤ a j) (hn : ∀ j, 1 ≤ n j)
    (σ t : ℝ) :
    ‖∑ j, (a j : ℂ) * (n j : ℂ) ^
        (-(σ + (t : ℂ) * Complex.I))‖
      ≤ ∑ j, a j * Real.rpow (n j : ℝ) (-σ) := by
  calc
    ‖∑ j, (a j : ℂ) * (n j : ℂ) ^
        (-(σ + (t : ℂ) * Complex.I))‖
        ≤ ∑ j, ‖(a j : ℂ) * (n j : ℂ) ^
            (-(σ + (t : ℂ) * Complex.I))‖ := by
              simpa using
                (norm_sum_le (Finset.univ : Finset ι)
                  (fun j => (a j : ℂ) * (n j : ℂ) ^
                    (-(σ + (t : ℂ) * Complex.I))))
    _ = ∑ j, a j * Real.rpow (n j : ℝ) (-σ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha j)]
      have hnorm := Complex.norm_natCast_cpow_of_pos
        (Nat.zero_lt_of_lt (hn j)) (-(σ + (t : ℂ) * Complex.I))
      rw [hnorm]
      congr 1
      simp [Complex.add_re, Complex.mul_re]

/-- Equality in claim 18766 at height zero. -/
theorem at_zero
    (ι : Type*) [Fintype ι]
    (a : ι → ℝ) (n : ι → ℕ)
    (ha : ∀ j, 0 ≤ a j) (hn : ∀ j, 1 ≤ n j)
    (σ : ℝ) :
    ‖∑ j, (a j : ℂ) * (n j : ℂ) ^
        (-(σ + (0 : ℝ) * (Complex.I : ℂ)))‖
      = ∑ j, a j * Real.rpow (n j : ℝ) (-σ) := by
  have hterm (j : ι) :
      (a j : ℂ) * (n j : ℂ) ^
          (-(σ + (0 : ℝ) * (Complex.I : ℂ)))
        = ((a j * Real.rpow (n j : ℝ) (-σ) : ℝ) : ℂ) := by
    rw [show -(σ + (0 : ℝ) * (Complex.I : ℂ)) = ((-σ : ℝ) : ℂ) by norm_num]
    change (a j : ℂ) * ((n j : ℝ) : ℂ) ^ ((-σ : ℝ) : ℂ) = _
    have hn_nonneg : (0 : ℝ) ≤ (n j : ℝ) := by positivity
    calc
      (a j : ℂ) * ((n j : ℝ) : ℂ) ^ ((-σ : ℝ) : ℂ) =
          (a j : ℂ) * ((Real.rpow (n j : ℝ) (-σ) : ℝ) : ℂ) := by
            rw [← Complex.ofReal_cpow hn_nonneg]
            rfl
      _ = ((a j * Real.rpow (n j : ℝ) (-σ) : ℝ) : ℂ) := by
            rw [Complex.ofReal_mul]
  have hsum :
      (∑ j, (a j : ℂ) * (n j : ℂ) ^
        (-(σ + (0 : ℝ) * (Complex.I : ℂ))))
        = Complex.ofRealHom (∑ j, a j * Real.rpow (n j : ℝ) (-σ)) := by
    calc
      (∑ j, (a j : ℂ) * (n j : ℂ) ^
          (-(σ + (0 : ℝ) * (Complex.I : ℂ))))
          = ∑ j, Complex.ofRealHom (a j * Real.rpow (n j : ℝ) (-σ)) := by
              apply Finset.sum_congr rfl
              intro j hj
              exact hterm j
      _ = Complex.ofRealHom (∑ j, a j * Real.rpow (n j : ℝ) (-σ)) := by
              symm
              exact map_sum Complex.ofRealHom (fun j => a j * Real.rpow (n j : ℝ) (-σ))
                Finset.univ
  have hnonneg : 0 ≤ ∑ j, a j * Real.rpow (n j : ℝ) (-σ) :=
    Finset.sum_nonneg (fun j hj =>
      mul_nonneg (ha j) (Real.rpow_nonneg (by positivity) _))
  calc
    ‖∑ j, (a j : ℂ) * (n j : ℂ) ^
        (-(σ + (0 : ℝ) * (Complex.I : ℂ)))‖
        = ‖Complex.ofRealHom (∑ j, a j * Real.rpow (n j : ℝ) (-σ))‖ := by
            rw [hsum]
    _ = ∑ j, a j * Real.rpow (n j : ℝ) (-σ) := by
            rw [Complex.ofRealHom_eq_coe, Complex.norm_of_nonneg hnonneg]

/-- The same claim expressed as attainment of the vertical supremum. -/
theorem vertical_supremum
    (ι : Type*) [Fintype ι]
    (a : ι → ℝ) (n : ι → ℕ)
    (ha : ∀ j, 0 ≤ a j) (hn : ∀ j, 1 ≤ n j)
    (σ : ℝ) :
    IsGreatest
      (Set.range (fun t : ℝ =>
        ‖∑ j, (a j : ℂ) * (n j : ℂ) ^
          (-(σ + (t : ℂ) * Complex.I))‖))
      (∑ j, a j * Real.rpow (n j : ℝ) (-σ)) := by
  constructor
  · exact ⟨0, by simpa using at_zero ι a n ha hn σ⟩
  · rintro _ ⟨t, rfl⟩
    exact vertical_bound ι a n ha hn σ t

end MathlibPlus.Analysis.PositiveDirichlet
