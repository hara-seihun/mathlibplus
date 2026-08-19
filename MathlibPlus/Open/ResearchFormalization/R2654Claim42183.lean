import Mathlib
import MathlibPlus.Open.ResearchFormalization.R2654Claim42181

namespace MathlibPlus.Open.ResearchFormalization.R2654Claim42183

noncomputable section

open MathlibPlus.Open.ResearchFormalization

/-- Boyd's identity in the nonzero-complex evaluation form used by the
reviewed reciprocal-trace carrier. -/
def boydIdentity
    (R A Astar : Polynomial ℤ) : Prop :=
  ∀ z : ℂ, z ≠ 0 →
    (z ^ 2 + 1) * evalIntComplex R z =
      z * evalIntComplex A z + evalIntComplex Astar z

/-- The two denominator-cleared auxiliary definitions attached to Boyd's
odd-degree polynomial. -/
def auxiliaryTraceDefinitions
    (A Astar P1 P2 : Polynomial ℤ) : Prop :=
  (∀ z : ℂ, z ≠ 0 →
    (z - 1) * evalIntComplex P1 z =
      z * evalIntComplex A z - evalIntComplex Astar z) ∧
    (∀ z : ℂ, z ≠ 0 →
      (z - 1) * evalIntComplex P2 z =
        z ^ 2 * evalIntComplex A z - evalIntComplex Astar z)

/-- Record 2's reciprocal-trace and Boyd data, without assuming Boyd's
identity itself.  The monicity and degree of `R` retain the degree-`2n`
reciprocal trace lift. -/
def record2
    (n : ℕ) (ell A Astar R P1 P2 : Polynomial ℤ) : Prop :=
  ell.Monic ∧
    ell.natDegree = n ∧
      R.Monic ∧
        R.natDegree = 2 * n ∧
          A.Monic ∧
            A.natDegree = 2 * n + 1 ∧
              Astar = A.reverse ∧
                (∀ z : ℂ, z ≠ 0 →
                  evalIntComplex R z =
                    z ^ n * evalIntComplex ell (z + z⁻¹)) ∧
                  auxiliaryTraceDefinitions A Astar P1 P2

/-- The monic trace factorizations of `P₁` and `P₂` uniquely select `q` and
`r` in the trace variable `t = z + z⁻¹`. -/
def uniquelyAssociatedTraceFactors
    (n : ℕ) (P1 P2 q r : Polynomial ℤ) : Prop :=
  q.Monic ∧
    r.Monic ∧
      (∀ z : ℂ, z ≠ 0 →
        evalIntComplex P1 z =
          (z + 1) * z ^ n * evalIntComplex q (z + z⁻¹)) ∧
        (∀ z : ℂ, z ≠ 0 →
          evalIntComplex P2 z =
            z ^ (n + 1) * evalIntComplex r (z + z⁻¹)) ∧
          ∀ q' r' : Polynomial ℤ,
            q'.Monic →
              r'.Monic →
                (∀ z : ℂ, z ≠ 0 →
                  evalIntComplex P1 z =
                    (z + 1) * z ^ n * evalIntComplex q' (z + z⁻¹)) →
                  (∀ z : ℂ, z ≠ 0 →
                    evalIntComplex P2 z =
                      z ^ (n + 1) * evalIntComplex r' (z + z⁻¹)) →
                    q' = q ∧ r' = r

/-- Claim 42183: once the reciprocal trace, Boyd auxiliary definitions, and
unique monic trace factorizations are fixed, Boyd's identity is equivalent to
the exact linear relation in `ℤ[t]`. -/
def claim42183 : Prop :=
  ∀ (n : ℕ) (ell A Astar R P1 P2 q r : Polynomial ℤ),
    record2 n ell A Astar R P1 P2 →
      uniquelyAssociatedTraceFactors n P1 P2 q r →
        (boydIdentity R A Astar ↔
          Polynomial.C (2 : ℤ) * r -
              (Polynomial.X + Polynomial.C (2 : ℤ)) * q =
            Polynomial.X * ell)

end

end MathlibPlus.Open.ResearchFormalization.R2654Claim42183
