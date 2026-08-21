-- UNVERIFIED (downstream): submitted but not kernel-verified, so it is not built and MathlibPlus.lean does not import it. See unverified.txt.
import Mathlib
import MathlibPlus.Analysis.Claim11843

namespace MathlibPlus.Open.Analysis.Claim11758

noncomputable section

/-- The finite normalized divisor character supplied by the product-shell grouping. -/
def tau (x : ℝ) (k : ℕ) : ℂ :=
  ∑ q ∈ (Finset.Icc 1 k).product (Finset.Icc 1 k),
    if q.1 * q.2 = k then
      Complex.exp
        (-Complex.I * (x : ℂ) *
          (Real.log ((q.1 : ℝ) / (q.2 : ℝ)) : ℂ))
    else 0

/-- The sine quotient with its removable values filled in by the derivative ratio. -/
def continuousSineQuotient (r : ℕ) (θ : ℝ) : ℝ :=
  if Real.sin θ = 0 then
    ((r + 1 : ℕ) : ℝ) *
      Real.cos (((r + 1 : ℕ) : ℝ) * θ) / Real.cos θ
  else
    Real.sin (((r + 1 : ℕ) : ℝ) * θ) / Real.sin θ

/-- Claim 11758, using the everywhere-defined finite divisor sum as the carrier. -/
def claim11758 : Prop :=
  (∀ r : ℕ, Continuous (continuousSineQuotient r)) ∧
    (∀ x : ℝ, tau x 1 = 1) ∧
    (∀ p : ℕ, p.Prime →
      (∀ x : ℝ, ∀ r : ℕ,
        tau x (p ^ r) =
          (continuousSineQuotient r (x * Real.log (p : ℝ)) : ℂ)) ∧
      (∀ x : ℝ, ∀ r : ℕ, 1 ≤ r →
        tau x (p ^ (r + 1)) =
          ((2 * Real.cos (x * Real.log (p : ℝ)) : ℝ) : ℂ) *
              tau x (p ^ r) - tau x (p ^ (r - 1))))

end

end MathlibPlus.Open.Analysis.Claim11758

namespace MathlibPlus.Open.Analysis.Claim11840

/--
Claim 11840.  The factorial-scaled coefficient carrier and centered indexing are
those fixed by the reviewed first-failure certificate.
-/
def claim11840 : Prop :=
  let B : Polynomial ℤ :=
    (1 + Polynomial.X) ^ 10 * (1 + 13 * Polynomial.X) *
      (1 + 14 * Polynomial.X) ^ 2
  let c : Fin 9 → ℤ :=
    ![1, 51, 2030, 60678, 1339440, 22886640, 312409440,
      3452047200, 30831131520]
  (∀ k : Fin 9, c k = (Nat.factorial k.1 : ℤ) * B.coeff k.1) ∧
    Matrix.det (!![c 4, c 5; c 3, c 4] : Matrix (Fin 2) (Fin 2) ℤ) = 571 ∧
    Matrix.det (!![c 4, c 5, c 6; c 3, c 4, c 5; c 2, c 3, c 4] :
      Matrix (Fin 3) (Fin 3) ℤ) = 248080244 ∧
    Matrix.det (!![c 4, c 5, c 6, c 7;
      c 3, c 4, c 5, c 6;
      c 2, c 3, c 4, c 5;
      c 1, c 2, c 3, c 4] : Matrix (Fin 4) (Fin 4) ℤ) =
      61517381159999376 ∧
    Matrix.det (!![c 4, c 5, c 6, c 7, c 8;
      c 3, c 4, c 5, c 6, c 7;
      c 2, c 3, c 4, c 5, c 6;
      c 1, c 2, c 3, c 4, c 5;
      c 0, c 1, c 2, c 3, c 4] : Matrix (Fin 5) (Fin 5) ℤ) =
      -222236584443224648570880

end MathlibPlus.Open.Analysis.Claim11840
