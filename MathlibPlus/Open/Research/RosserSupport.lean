import Mathlib

namespace MathlibPlus.Open.Research.RosserSupport

/-- The ordered prime-factor predicate used by the lower Rosser support. -/
def lowerRosserFactorization (y z : ℝ) (d : ℕ) (k : ℕ)
    (p : Fin k → ℕ) : Prop :=
  z ≤ Real.sqrt y ∧
    (∀ i, Nat.Prime (p i)) ∧
    (∀ i j, i < j → p j < p i) ∧
    (∀ i, (p i : ℝ) < z) ∧
    (∏ i : Fin k, p i = d) ∧
    (∀ j : ℕ, (hj : 1 ≤ j) → (hjk : 2 * j ≤ k) →
      (Finset.univ.prod
          (fun i : Fin (2 * j - 1) =>
            (p ⟨i.1, by have hi := i.isLt; omega⟩ : ℝ))) *
        (p ⟨2 * j - 1, by omega⟩ : ℝ) ^ 3 < y)

/-- Claim 36047: the exact lower Rosser support produced by the cubic stopping
conditions. -/
def lowerRosserSupport (y z : ℝ) : Set ℕ :=
  {d | ∃ k : ℕ, ∃ p : Fin k → ℕ,
    lowerRosserFactorization y z d k p}

/-- The exponent appearing in the even-depth support bound. -/
noncomputable def evenRosserExponent (r : ℕ) : ℝ :=
  1 - (3 : ℝ)⁻¹ ^ r

/-- Claim 36048: every lower-support element with an even ordered prime
factorization has the stated geometric exponent. -/
def exactEvenDepthSupportExponent : Prop :=
  ∀ (y z : ℝ) (d r : ℕ) (p : Fin (2 * r) → ℕ),
    d ∈ lowerRosserSupport y z →
    lowerRosserFactorization y z d (2 * r) p →
    (d : ℝ) < Real.rpow y (evenRosserExponent r)

/-- The exponent appearing in the odd-depth support bound. -/
noncomputable def oddRosserExponent (r : ℕ) : ℝ :=
  1 - (2 * (3 : ℝ) ^ r)⁻¹

/-- Claim 36049: every lower-support element with an odd ordered prime
factorization has the stated geometric exponent. -/
def exactOddDepthSupportExponent : Prop :=
  ∀ (y z : ℝ) (d r : ℕ) (p : Fin (2 * r + 1) → ℕ),
    d ∈ lowerRosserSupport y z →
    lowerRosserFactorization y z d (2 * r + 1) p →
    (d : ℝ) < Real.rpow y (oddRosserExponent r)

end MathlibPlus.Open.Research.RosserSupport
