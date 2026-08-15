import Mathlib

namespace MathlibPlus.Open.C0079

open scoped BigOperators

noncomputable section

/-- The complete homogeneous symmetric polynomial of degree `n` in a finite
family of variables.  Nondecreasing index maps list each monomial once. -/
def completeHomogeneous {R : Type*} [CommRing R] (n s : ℕ)
    (x : Fin s → R) : R := by
  classical
  exact ∑ f : Fin n → Fin s, if Monotone f then ∏ i, x (f i) else 0

/-- The usual zero extension of the complete homogeneous polynomials to
negative degrees. -/
def completeHomogeneousInt {R : Type*} [CommRing R] (n : ℤ) (s : ℕ)
    (x : Fin s → R) : R :=
  if 0 ≤ n then completeHomogeneous n.toNat s x else 0

/-- The consecutive variables `a, a+1, ..., a+k+1`. -/
def consecutiveVariables {R : Type*} [CommRing R] (a : R) (k : ℕ) : Fin (k + 2) → R :=
  fun i => a + (i.1 : R)

/-- The flagged array from the admitted rank-`r` construction, with `d=r-1`.
Rows are indexed by `0 ≤ k < 2d` and columns by `1 ≤ j ≤ d`. -/
def flaggedArray {R : Type*} [CommRing R] (d : ℕ) (a : R) :
    Matrix (Fin (2 * d)) (Fin d) R :=
  fun k j =>
    ((k.1 + 1 : ℕ) : R) *
      completeHomogeneousInt
        ((2 : ℤ) * ((j.1 + 1 : ℕ) : ℤ) - (k.1 : ℤ) - 1)
        (k.1 + 2) (consecutiveVariables a k.1)

/-- The row set belonging to the empty partition. -/
def emptyRows (d : ℕ) : Fin d → Fin (2 * d) :=
  fun i => ⟨i.1, by omega⟩

/-- The row set `K_(3)=(0,...,d-2,d+2)` for `d ≥ 3`. -/
def threeRows (d : ℕ) (hd : 3 ≤ d) : Fin d → Fin (2 * d) :=
  fun i =>
    if h : i.1 = d - 1 then
      ⟨d + 2, by omega⟩
    else
      ⟨i.1, by omega⟩

/-- The principal minor `H_empty(a)`. -/
def emptyMinor {R : Type*} [CommRing R] (d : ℕ) (a : R) : R :=
  Matrix.det ((flaggedArray d a).submatrix (emptyRows d) (fun j => j))

/-- The neighboring minor `H_(3)(a)`. -/
def threeMinor {R : Type*} [CommRing R] (d : ℕ) (hd : 3 ≤ d) (a : R) : R :=
  Matrix.det ((flaggedArray d a).submatrix (threeRows d hd) (fun j => j))

/-- Exact admitted neighboring-minor ratio and its everywhere cross-multiplied
polynomial identity. -/
def neighboringMinorRatio (R : Type*) [Field R] : Prop :=
  ∀ (d : ℕ) (hd : 3 ≤ d), ∀ a : R,
    let y : R := 2 * a + (d : R)
    let h₀ : R := emptyMinor d a
    let h₃ : R := threeMinor d hd a
    let q : R := 6 * y * (y + 1) * (y + 2)
    (h₀ ≠ 0 ∧ q ≠ 0 →
      h₃ / h₀ =
        (((d - 1) * (d - 2) * (d + 3) : ℕ) : R) / q) ∧
    q * h₃ = (((d - 1) * (d - 2) * (d + 3) : ℕ) : R) * h₀

/-- Claim 1185. -/
def claim1185 (R : Type*) [Field R] : Prop :=
  neighboringMinorRatio R

end

end MathlibPlus.Open.C0079
