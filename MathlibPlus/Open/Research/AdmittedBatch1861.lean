import Mathlib

namespace MathlibPlus.Open.Research

/-- The row indices `1, ..., L, L + n` used by the Riordan tail. -/
def nearHookRow (n L : ℕ) (i : Fin (L + 1)) : ℕ :=
  if i.1 < L then i.1 + 1 else L + n

/-- The binomial entry, with the usual zero convention for a negative lower index. -/
def riordanTailEntry (e t j : ℕ) : ℚ :=
  if j ≤ t then (Nat.choose (e + j) (t - j) : ℚ) else 0

/-- The determinant on rows `1, ..., L, L + n` and columns `0, ..., L`. -/
def riordanTailDeterminant (e n L : ℕ) : ℚ :=
  Matrix.det (fun i j : Fin (L + 1) =>
    riordanTailEntry e (nearHookRow n L i) j.1)

/-- The pure near-hook determinant with `L = ell + 1` and `d = e + L`. -/
def pureNearHookDeterminant (n ell e : ℕ) : ℚ :=
  let L := ell + 1
  let d := e + L
  (d : ℚ) * riordanTailDeterminant e n L -
    (Nat.choose d n : ℚ) * riordanTailDeterminant e 1 L

/-- Strict positivity of the pure near-hook determinant under the admissibility conditions. -/
def pureNearHookDeterminantStrictlyPositive : Prop :=
  ∀ (d n ell : ℕ),
    n ≥ 2 →
    ell ≥ 1 →
    d ≥ max n (ell + 2) →
    0 < pureNearHookDeterminant n ell (d - ell - 1)

end MathlibPlus.Open.Research
