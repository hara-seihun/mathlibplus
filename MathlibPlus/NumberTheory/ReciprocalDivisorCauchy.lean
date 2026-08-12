import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

open scoped BigOperators ArithmeticFunction.Moebius

namespace MathlibPlus.NumberTheory

/-- The finite Cauchy-Schwarz component of admitted claim 13163. -/
theorem reciprocalDivisorCauchyFinite_13163
    (g : ℕ) (hg : Squarefree g) (M a c : ℕ) (E : ℕ → ℕ → ℕ → ℝ) :
    |∑ d ∈ g.divisors, ((μ d : ℤ) : ℝ) * E M (a * d) c / (d : ℝ)| ^ 2 ≤
      (∑ d ∈ g.divisors, ((d : ℝ)⁻¹) ^ 2) *
        (∑ d ∈ g.divisors, |E M (a * d) c| ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq g.divisors
    (fun d => (d : ℝ)⁻¹)
    (fun d => ((μ d : ℤ) : ℝ) * E M (a * d) c)
  have hmu :
      (∑ d ∈ g.divisors,
        (((μ d : ℤ) : ℝ) * E M (a * d) c) ^ 2) =
        ∑ d ∈ g.divisors, |E M (a * d) c| ^ 2 := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdsq : Squarefree d :=
      Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1 hg
    have hμ : ((μ d : ℤ) : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hdsq
    rw [mul_pow, sq_abs, hμ, one_mul]
  calc
    |∑ d ∈ g.divisors, ((μ d : ℤ) : ℝ) * E M (a * d) c / (d : ℝ)| ^ 2 =
        (∑ d ∈ g.divisors,
          (d : ℝ)⁻¹ * (((μ d : ℤ) : ℝ) * E M (a * d) c)) ^ 2 := by
      rw [sq_abs]
      congr 1
      apply Finset.sum_congr rfl
      intro d hd
      simp [div_eq_mul_inv, mul_left_comm, mul_comm]
    _ ≤ (∑ d ∈ g.divisors, ((d : ℝ)⁻¹) ^ 2) *
        (∑ d ∈ g.divisors,
          (((μ d : ℤ) : ℝ) * E M (a * d) c) ^ 2) := hcs
    _ = (∑ d ∈ g.divisors, ((d : ℝ)⁻¹) ^ 2) *
        (∑ d ∈ g.divisors, |E M (a * d) c| ^ 2) := by rw [hmu]

end MathlibPlus.NumberTheory

namespace MathlibPlus.Open.NumberTheory

/-- Claim 13163: the reciprocal-divisor Cauchy bound, together with the
convergent Euler product over all primes.  The source writes `E_{M,ad}(c)`;
the node makes the varying index `a * d` explicit. -/
def reciprocalDivisorCauchyBound_13163 : Prop :=
  let eulerProduct : ℝ :=
    ∏' (p : Nat.Primes), (1 + (((p : ℕ) : ℝ)⁻¹) ^ 2)
  (Multipliable (fun p : Nat.Primes =>
      (1 + (((p : ℕ) : ℝ)⁻¹) ^ 2))) ∧
    ∀ (g M a c : ℕ) (E : ℕ → ℕ → ℕ → ℝ), Squarefree g →
      |∑ d ∈ g.divisors, ((μ d : ℤ) : ℝ) * E M (a * d) c / (d : ℝ)| ^ 2 ≤
          (∑ d ∈ g.divisors, ((d : ℝ)⁻¹) ^ 2) *
            (∑ d ∈ g.divisors, |E M (a * d) c| ^ 2) ∧
        (∑ d ∈ g.divisors, ((d : ℝ)⁻¹) ^ 2) ≤ eulerProduct

end MathlibPlus.Open.NumberTheory
