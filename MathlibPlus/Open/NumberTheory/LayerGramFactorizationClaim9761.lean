import Mathlib
import MathlibPlus.NumberTheory.Claim9757

namespace MathlibPlus.Open.NumberTheory

open scoped BigOperators

abbrev FareyHilbert := ↥(lp (fun _ : ℕ => ℝ) 2)

noncomputable def jordanTwo (r : ℕ) : ℝ :=
  r.divisors.sum (fun d => (d : ℝ) ^ 2 * (ArithmeticFunction.moebius (r / d) : ℤ))

noncomputable def fareyBasisVector (d : ℕ) : FareyHilbert :=
  ⟨fun r => if 0 < d ∧ r ∣ d then Real.sqrt (jordanTwo r) / (d : ℝ) else 0, by
    change Memℓp (fun r => if 0 < d ∧ r ∣ d then Real.sqrt (jordanTwo r) / (d : ℝ) else 0) 2
    by_cases hd : 0 < d
    · simp only [Memℓp, if_neg (by norm_num : (2 : ENNReal) ≠ 0),
        if_neg (by norm_num : (2 : ENNReal) ≠ ⊤)]
      apply summable_of_hasFiniteSupport
      refine (Set.finite_mem_finset (Nat.divisors d)).subset ?_
      intro r hr
      change ‖(if 0 < d ∧ r ∣ d then Real.sqrt (jordanTwo r) / (d : ℝ) else 0)‖ ^ (2 : ENNReal).toReal ≠ 0 at hr
      have hdiv : r ∣ d := by
        by_contra hrd
        simp [hd, hrd] at hr
      exact Nat.mem_divisors.mpr ⟨hdiv, Nat.ne_of_gt hd⟩
    · have hzero : (fun r => if 0 < d ∧ r ∣ d then Real.sqrt (jordanTwo r) / (d : ℝ) else 0) = 0 := by
        funext r
        simp [hd]
      rw [hzero]
      simp [Memℓp]
  ⟩

noncomputable def fareyLevelVector (n : ℕ) : FareyHilbert :=
  n.divisors.sum (fun d =>
    (((ArithmeticFunction.moebius (n / d) : ℤ) : ℝ)) • fareyBasisVector d)

noncomputable def fareyH (n : ℕ) : ℝ :=
  ((MathlibPlus.NumberTheory.Claim9757.fareyConvolutionCoeff n : ℚ) : ℝ)

noncomputable def whiteningWeight (n : ℕ) : ℝ :=
  n.primeFactors.prod (fun p => 1 - (p : ℝ)⁻¹ ^ 2)

def layerGramFactorization_claim9761 : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n →
    inner ℝ (fareyLevelVector m) (fareyLevelVector n) =
      ∑ q ∈ (Nat.gcd m n).divisors,
        whiteningWeight q * fareyH (m / q) * fareyH (n / q)

end MathlibPlus.Open.NumberTheory
