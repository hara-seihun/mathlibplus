import Mathlib

namespace MathlibPlus.Analysis.Claim18774

/-- Odd iterated derivatives at the origin vanish for a smooth even function. -/
theorem evenFunction_oddIteratedDeriv_zero_claim18774
    (f : ℂ → ℂ) (_h_diff : ContDiff ℂ ⊤ f) (h_even : Function.Even f)
    (n : ℕ) (h_odd : Odd n) :
    iteratedDeriv n f 0 = 0 := by
  have hfun : (fun x : ℂ ↦ f (-x)) = f := funext h_even
  have hpar := iteratedDeriv_comp_neg n f (0 : ℂ)
  rw [hfun] at hpar
  have hpow : (-1 : ℂ) ^ n = (-1 : ℂ) := Odd.neg_one_pow h_odd
  simp only [smul_eq_mul, neg_zero, hpow, neg_one_mul] at hpar
  have hzero : (2 : ℂ) * iteratedDeriv n f 0 = 0 := by
    linear_combination hpar
  rcases mul_eq_zero.mp hzero with h | h
  · norm_num at h
  · exact h

/-- The quadratic `z² + a²` is an even entire counterexample to odd-jet tests. -/
theorem quadraticEvenEntireOffAxisCounterexample_claim18774 (a : ℝ) (ha : 0 < a) :
    let f : ℂ → ℂ := fun z => z ^ 2 + (a : ℂ) ^ 2
    Function.Even f ∧
      ContDiff ℂ ⊤ f ∧
      f 0 ≠ 0 ∧
      (∀ n : ℕ, Odd n → iteratedDeriv n f 0 = 0) ∧
      (∀ z : ℂ, f z = 0 ↔
        z = (a : ℂ) * Complex.I ∨ z = -(a : ℂ) * Complex.I) ∧
      Complex.im ((a : ℂ) * Complex.I) ≠ 0 ∧
      Complex.im (-(a : ℂ) * Complex.I) ≠ 0 := by
  dsimp
  have h_even : Function.Even (fun z : ℂ => z ^ 2 + (a : ℂ) ^ 2) := by
    intro z
    ring
  have h_cont : ContDiff ℂ ⊤ (fun z : ℂ => z ^ 2 + (a : ℂ) ^ 2) := by
    fun_prop
  have hodd : ∀ n : ℕ, Odd n →
      iteratedDeriv n (fun z : ℂ => z ^ 2 + (a : ℂ) ^ 2) 0 = 0 := by
    intro n hn
    exact evenFunction_oddIteratedDeriv_zero_claim18774
      (fun z : ℂ => z ^ 2 + (a : ℂ) ^ 2) h_cont h_even n hn
  refine ⟨h_even, h_cont, ?_, hodd, ?_, ?_, ?_⟩
  · norm_num
    positivity
  · intro z
    constructor
    · intro hz
      have hfac : (z - (a : ℂ) * Complex.I) * (z + (a : ℂ) * Complex.I) = 0 := by
        calc
          (z - (a : ℂ) * Complex.I) * (z + (a : ℂ) * Complex.I) =
              z ^ 2 - ((a : ℂ) * Complex.I) ^ 2 := by ring
          _ = z ^ 2 + (a : ℂ) ^ 2 := by
            rw [mul_pow, Complex.I_sq]
            ring
          _ = 0 := hz
      rcases mul_eq_zero.mp hfac with h | h
      · left
        exact sub_eq_zero.mp h
      · right
        simpa [neg_mul] using eq_neg_of_add_eq_zero_left h
    · intro hz
      rcases hz with h | h
      · rw [h]
        rw [mul_pow, Complex.I_sq]
        ring
      · rw [h]
        rw [mul_pow, Complex.I_sq]
        ring
  · simp [ha.ne']
  · simp [ha.ne']

end MathlibPlus.Analysis.Claim18774
