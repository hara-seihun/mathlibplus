import MathlibPlus.Basic

namespace MathlibPlus.Complex.Claim9624

open Polynomial

/-- The explicit centered-axis witness in claim 9624. -/
theorem axis_supported_witness :
    let G : ℂ[X] := X ^ 2 + 1
    Squarefree G ∧
      (∀ z : ℂ, G.eval z = 0 ↔ z = Complex.I ∨ z = -Complex.I) ∧
      (∀ z : ℂ, G.eval z = 0 → z.re = 0) := by
  let G : ℂ[X] := X ^ 2 + 1
  change
    Squarefree G ∧
      (∀ z : ℂ, G.eval z = 0 ↔ z = Complex.I ∨ z = -Complex.I) ∧
      (∀ z : ℂ, G.eval z = 0 → z.re = 0)
  have hsep : (X ^ 2 - C (-1 : ℂ)).Separable := by
    apply (X_pow_sub_C_separable_iff (F := ℂ) (n := 2)
      (x := (-1 : ℂ)) (by norm_num) (by norm_num)).2
    norm_num
  have hsq0 : Squarefree (X ^ 2 - C (-1 : ℂ)) :=
    PerfectField.separable_iff_squarefree.mp hsep
  have hsq : Squarefree G := by
    simpa [G, sub_eq_add_neg] using hsq0
  have hroots : ∀ z : ℂ, G.eval z = 0 ↔ z = Complex.I ∨ z = -Complex.I := by
    intro z
    constructor
    · intro hz
      have hfactor : (z - Complex.I) * (z + Complex.I) = 0 := by
        calc
          (z - Complex.I) * (z + Complex.I) = z ^ 2 - Complex.I ^ 2 := by
            ring
          _ = z ^ 2 + 1 := by simp [pow_two, Complex.I_mul_I]
          _ = G.eval z := by simp [G]
          _ = 0 := hz
      rcases mul_eq_zero.mp hfactor with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)
    · rintro (rfl | rfl) <;> simp [G]
  refine ⟨hsq, hroots, ?_⟩
  intro z hz
  rcases (hroots z).mp hz with rfl | rfl <;> simp

end MathlibPlus.Complex.Claim9624
