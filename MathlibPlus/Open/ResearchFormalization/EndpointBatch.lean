import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.Endpoint

open scoped BigOperators

noncomputable section

def endpointNearZeroSeries (F : ℂ → ℂ) (f : ℕ → ℂ) : Prop :=
  ∃ R : ℝ, 0 < R ∧
    ∀ z : ℂ, ‖z‖ < R → F z = ∑' n : ℕ, f n * z ^ n

def endpointAnalyticData (F : ℂ → ℂ) (α : ℂ) (f : ℕ → ℂ) : Prop :=
  α ≠ 0 ∧ AnalyticAt ℂ F α ∧ endpointNearZeroSeries F f

def endpointExteriorLaurent (F : ℂ → ℂ) (α : ℂ) (d : ℤ → ℂ) : Prop :=
  ∃ R : ℝ, ‖α‖ < R ∧
    ∀ z : ℂ, R < ‖z‖ →
      F z / (z - α) = ∑' n : ℤ, d n * z ^ n

def endpointB (r k : ℕ) (d : ℤ → ℂ) :
    Matrix (Fin (r + 1)) (Fin r) ℂ :=
  fun m j => d ((k : ℤ) + (j : ℤ) - (m : ℤ))

def skipFin {r : ℕ} (m : Fin (r + 1)) (i : Fin r) : Fin (r + 1) :=
  if h : i.1 < m.1 then ⟨i.1, lt_trans h m.2⟩
  else ⟨i.1 + 1, Nat.succ_lt_succ i.2⟩

def endpointMinor {r : ℕ} (B : Matrix (Fin (r + 1)) (Fin r) ℂ)
    (m : Fin (r + 1)) : Matrix (Fin r) (Fin r) ℂ :=
  fun i j => B (skipFin m i) j

def endpointCofactor (r k : ℕ) (d : ℤ → ℂ) (m : Fin (r + 1)) : ℂ :=
  (-1 : ℂ) ^ m.1 * Matrix.det (endpointMinor (endpointB r k d) m)

def endpointCofactorPolynomial (r k : ℕ) (d : ℤ → ℂ) : Polynomial ℂ :=
  ∑ m : Fin (r + 1), Polynomial.monomial m.1 (endpointCofactor r k d m)

def endpointCoefficient (r k : ℕ) (d : ℤ → ℂ) (N : ℤ) : ℂ :=
  ∑ m : Fin (r + 1), endpointCofactor r k d m * d (N - m.1)

def claim8097 : Prop :=
  ∀ (F : ℂ → ℂ) (α : ℂ) (f : ℕ → ℂ) (d : ℤ → ℂ),
    endpointAnalyticData F α f → endpointExteriorLaurent F α d →
      (∀ j : ℕ, 1 ≤ j → d (-(j : ℤ)) = F α * α ^ (j - 1)) ∧
      (∀ n : ℕ, Summable (fun l : ℕ => α ^ l * f (n + l + 1)) →
        d n = ∑' l : ℕ, α ^ l * f (n + l + 1))

def claim8098 : Prop :=
  ∀ (r k : ℕ) (d : ℤ → ℂ),
    (∀ j : Fin r,
      ∑ m : Fin (r + 1), endpointCofactor r k d m * endpointB r k d m j = 0) ∧
      (∀ N : ℤ, (k : ℤ) ≤ N → N ≤ (k + r - 1 : ℕ) →
        endpointCoefficient r k d N = 0) ∧
      ∀ m : Fin (r + 1),
        endpointCofactor r k d m =
          (-1 : ℂ) ^ m.1 *
            Matrix.det (endpointMinor (endpointB r k d) m)

end

end MathlibPlus.Open.ResearchFormalization.Endpoint
