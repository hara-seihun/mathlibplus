import Mathlib

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d

/-! Exact effective transfer for the subdivided-tree state model. -/

abbrev R2940Variable (m : ℕ) := Sum (Fin m) (Sum (Fin m) Unit)
abbrev R2940Ring (m : ℕ) := MvPolynomial (R2940Variable m) ℤ

def r2940X {m : ℕ} (i : Fin m) : R2940Ring m :=
  MvPolynomial.X (Sum.inl i)

def r2940Z {m : ℕ} (i : Fin m) : R2940Ring m :=
  MvPolynomial.X (Sum.inr (Sum.inl i))

def r2940Y {m : ℕ} : R2940Ring m :=
  MvPolynomial.X (Sum.inr (Sum.inr ()))

def r2940Weight (m : ℕ) : Fin (m + 1) → R2940Ring m :=
  Fin.cases 1 (fun i => r2940X i)

def r2940Zeta (m : ℕ) : Fin (m + 1) → R2940Ring m :=
  Fin.cases 1 (fun i => r2940Z i)

def r2940Q (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) (R2940Ring m) :=
  fun s t => if s = t then r2940Zeta m s else r2940Y

def r2940W (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) (R2940Ring m) :=
  Matrix.diagonal (r2940Weight m)

/-- Claim 45521: the all-order effective edge transfer is exactly `Q W Q`. -/
def claim45521 : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    ∀ s t : Fin (m + 1),
      (r2940Q m * r2940W m * r2940Q m) s t =
        ∑ a : Fin (m + 1),
          r2940Q m s a * r2940W m a a * r2940Q m a t


end MathlibPlus.Open.ResearchFormalization.Batch_01a0040167a37f8a848e6f8a61d
