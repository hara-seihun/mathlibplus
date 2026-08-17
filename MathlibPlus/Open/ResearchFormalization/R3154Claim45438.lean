import Mathlib

open scoped BigOperators
open Classical

namespace MathlibPlus.Open.ResearchFormalization.R3154

noncomputable section

abbrev Poly := Polynomial ℤ

def jacobiMatrix (N : ℕ) (alpha beta : ℕ → Poly) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) Poly :=
  fun i j =>
    if i = j then alpha i.1
    else if i.1 + 1 = j.1 then 1
    else if j.1 + 1 = i.1 then beta i.1
    else 0

def jacobiMomentConstruction (alpha beta : ℕ → Poly) (p : ℕ → Poly) : Prop :=
  ∀ n : ℕ,
    p n = ((jacobiMatrix n alpha beta) ^ n) 0 0

def alpha45438 : ℕ → Poly :=
  fun i => if i = 0 then 1 + Polynomial.X ^ 2 else 0

def beta45438 : ℕ → Poly :=
  fun _ => 0

def moment45438 : ℕ → Poly :=
  fun n => (1 + Polynomial.X ^ 2) ^ n

def coefficientwiseNonnegative (p : Poly) : Prop :=
  ∀ k : ℕ, 0 ≤ p.coeff k

def positiveJacobiData (alpha beta : ℕ → Poly) : Prop :=
  (∀ i k : ℕ, 0 ≤ (alpha i).coeff k) ∧
    (∀ i k : ℕ, 0 ≤ (beta i).coeff k)

def hankelMatrix (p : ℕ → Poly) : Matrix ℕ ℕ Poly :=
  fun i j => p (i + j)

def coefficientwiseHankelTN (p : ℕ → Poly) : Prop :=
  ∀ (r : ℕ) (rows cols : Fin r → ℕ),
    StrictMono rows → StrictMono cols →
      coefficientwiseNonnegative
        (Matrix.det (fun i j => hankelMatrix p (rows i) (cols j)))

def rankOneHankel (p : ℕ → Poly) : Prop :=
  p 0 = 1 ∧
    ∀ i j k l : ℕ,
      p (i + j) * p (k + l) = p (i + l) * p (k + j)

def rowExtension (a : Fin 3 → ℤ) : ℕ → ℤ :=
  fun k => if h : k < 3 then a ⟨k, h⟩ else 0

def lowerToeplitz (f : ℕ → ℤ) : Matrix ℕ ℕ ℤ :=
  fun i j => if j ≤ i then f (i - j) else 0

def rowPF (a : Fin 3 → ℤ) : Prop :=
  ∀ (r : ℕ) (rows cols : Fin r → ℕ),
    StrictMono rows → StrictMono cols →
      0 ≤ Matrix.det
        (fun i j => lowerToeplitz (rowExtension a) (rows i) (cols j))

def degreeTwoRow (p : ℕ → Poly) : Fin 3 → ℤ :=
  fun k => (p 1).coeff k.1

def degreeTwoToeplitzMinor (p : ℕ → Poly) : ℤ :=
  Matrix.det (fun i j : Fin 2 =>
    lowerToeplitz (rowExtension (degreeTwoRow p)) (i.1 + 1) j.1)

def degreeTwoRowIsOneZeroOne (p : ℕ → Poly) : Prop :=
  ∀ k : Fin 3,
    degreeTwoRow p k =
      if k.1 = 0 then 1 else if k.1 = 1 then 0 else 1

/-- Claim R-3154: the zero-beta ordinary Jacobi fraction with
`alpha_0 = 1 + x^2` has rank-one coefficientwise Hankel data but its
quadratic coefficient row is not PF. -/
def claim45438 : Prop :=
  ∃ alpha beta p : ℕ → Poly,
    alpha = alpha45438 ∧
      beta = beta45438 ∧
      positiveJacobiData alpha beta ∧
      jacobiMomentConstruction alpha beta p ∧
      (∀ n : ℕ, p n = moment45438 n) ∧
      rankOneHankel p ∧
      coefficientwiseHankelTN p ∧
      degreeTwoRowIsOneZeroOne p ∧
      ¬ rowPF (degreeTwoRow p) ∧
      degreeTwoToeplitzMinor p = -1

end

end MathlibPlus.Open.ResearchFormalization.R3154
