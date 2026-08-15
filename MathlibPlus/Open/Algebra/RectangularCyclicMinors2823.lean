import Mathlib

noncomputable section

namespace MathlibPlus.Open.Algebra

/-- The angle and the cyclic triple used in the mixed shell. -/
def cyclicAngle2823 (N : ℕ) : ℝ := 2 * Real.pi / (N : ℝ)

def cyclicSecond2823 (N : ℕ) : ℂ :=
  Complex.exp (Complex.I * (cyclicAngle2823 N : ℂ))

def cyclicThird2823 (N : ℕ) : ℂ :=
  Complex.exp (-Complex.I * (cyclicAngle2823 N : ℂ))

def cyclicTriple2823 (N : ℕ) : Fin 3 → ℂ :=
  fun i => if i = 0 then 1 else if i = 1 then cyclicSecond2823 N else cyclicThird2823 N

/-- The complete homogeneous polynomial of degree `r` on the cyclic triple. -/
def completeHomogeneous2823 (N r : ℕ) : ℂ :=
  Finset.sum (Finset.range (r + 1)) (fun i =>
    Finset.sum (Finset.range (r + 1 - i)) (fun j =>
      (cyclicTriple2823 N 1) ^ i *
        (cyclicTriple2823 N 2) ^ j *
        (cyclicTriple2823 N 0) ^ (r - i - j)))

def homogeneousIndex2823 (N : ℕ) (n : ℤ) : ℂ :=
  if 0 ≤ n then completeHomogeneous2823 N n.toNat else 0

/-- The rectangular Jacobi--Trudi determinant with `k` rows. -/
def rectangularMinor2823 (N r k : ℕ) : ℂ :=
  Matrix.det (fun i j : Fin k =>
    homogeneousIndex2823 N
      ((r : ℤ) - (i.1 : ℤ) + (j.1 : ℤ)))

/-- The displayed sine value for the complete homogeneous coefficient. -/
def cyclicSineValue2823 (N r : ℕ) : ℝ :=
  (Real.sin (((r + 1 : ℕ) : ℝ) * Real.pi / (N : ℝ)) *
      Real.sin (((r + 2 : ℕ) : ℝ) * Real.pi / (N : ℝ))) /
    (Real.sin (Real.pi / (N : ℝ)) *
      Real.sin (2 * Real.pi / (N : ℝ)))

def complexNonnegative2823 (z : ℂ) : Prop :=
  z.im = 0 ∧ 0 ≤ z.re

/-- Rectangular minors miss this nonreal mixed shell. -/
def rectangularCyclicMinorsNonnegative2823 : Prop :=
  (∀ (N : ℕ), 3 ≤ N →
    (∀ r : ℕ,
      completeHomogeneous2823 N r =
          (cyclicSineValue2823 N r : ℂ) ∧
        0 ≤ cyclicSineValue2823 N r ∧
        (cyclicSineValue2823 N r = 0 ↔
          r % N = N - 2 ∨ r % N = N - 1) ∧
        rectangularMinor2823 N r 1 = completeHomogeneous2823 N r ∧
        rectangularMinor2823 N r 2 = completeHomogeneous2823 N r ∧
        rectangularMinor2823 N r 3 = 1 ∧
        (∀ k : ℕ, 3 < k → rectangularMinor2823 N r k = 0)) ∧
    (∀ r k : ℕ, complexNonnegative2823 (rectangularMinor2823 N r k)) ∧
    Complex.im (cyclicSecond2823 N) ≠ 0) ∧
  Filter.Tendsto (fun N : ℕ => cyclicAngle2823 N) Filter.atTop (nhds 0)

end MathlibPlus.Open.Algebra

end
