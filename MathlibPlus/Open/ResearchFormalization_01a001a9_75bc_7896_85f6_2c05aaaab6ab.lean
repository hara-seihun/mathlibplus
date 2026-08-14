import Mathlib

namespace MathlibPlus.Open

private noncomputable def besselJ (j : ℕ) (y : ℝ) : ℝ :=
  ∑' k : ℕ,
    ((-1 : ℝ) ^ k * (y / 2) ^ (2 * k + j)) /
      ((k.factorial : ℝ) * ((j + k).factorial : ℝ))

private noncomputable def kernelSelfDet (r : ℕ) (x t : ℝ) : ℝ :=
  (t / x) ^ r *
    (besselJ (r - 1) (2 * Real.sqrt (x * t)) *
        besselJ (r + 1) (2 * Real.sqrt (x * t)) -
      (besselJ r (2 * Real.sqrt (x * t))) ^ 2)

def claim_4120 : Prop :=
  ∀ (r : ℤ),
    1 ≤ r →
    ∀ (x T : ℝ),
      0 < x →
      0 < T →
      (x ^ r.toNat / (r.toNat.factorial : ℝ)) *
          (Finset.sum (Finset.Icc 1 (Nat.floor (Real.exp T))) (fun n =>
            ((ArithmeticFunction.vonMangoldt.toFun n / (n : ℝ)) ^ 2) *
              |kernelSelfDet r.toNat x (Real.log (n : ℝ))|)) ≤
        (6 : ℝ) * ((r + 1 : ℤ) : ℝ) * ((r + 2 : ℤ) : ℝ)

end MathlibPlus.Open
