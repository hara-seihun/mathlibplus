import Mathlib

namespace MathlibPlus.Open.Analysis

open scoped BigOperators

/-- The square-free exponent of the formal amplitude monomial indexed by `B`. -/
noncomputable def simplePacketMonomial {L : ℕ} (B : Finset (Fin L)) : (Fin L →₀ ℕ) :=
  ∑ ν ∈ B, Finsupp.single ν 1

/-- The coefficient ring expression for the shell sequence at one Hankel entry. -/
noncomputable def simpleShellEntry {L k : ℕ}
    (P : Polynomial ℂ) (ω : Fin L → ℂ) (n : ℕ)
    (i j : Fin k) : MvPolynomial (Fin L) ℂ :=
  let t : ℕ := n + (i : ℕ) + (j : ℕ)
  MvPolynomial.C (P.eval (t : ℂ)) +
    ∑ ν : Fin L, MvPolynomial.C ((ω ν) ^ t) * MvPolynomial.X ν

/-- The size-`k` shell determinant with formal amplitude variables. -/
noncomputable def simpleShellDeterminant {L k : ℕ}
    (P : Polynomial ℂ) (ω : Fin L → ℂ) (n : ℕ) :
    MvPolynomial (Fin L) ℂ :=
  Matrix.det (fun i : Fin k => fun j : Fin k => simpleShellEntry P ω n i j)

/-- The coefficient of the `B`-packet after factoring out its simple-mode exponential. -/
noncomputable def simplePacketCoefficient {L k : ℕ}
    (P : Polynomial ℂ) (ω : Fin L → ℂ) (B : Finset (Fin L)) (n : ℕ) : ℂ :=
  (∏ ν ∈ B, (ω ν) ^ n)⁻¹ *
    MvPolynomial.coeff (simplePacketMonomial B)
      (simpleShellDeterminant (k := k) P ω n)

/--
The exact-degree assertion for every simple `b`-mode packet in a shell
Hankel determinant.  The amplitudes are represented by the formal variables
`MvPolynomial.X ν`, so the displayed coefficient is the coefficient of the
corresponding amplitude monomial after factoring out `∏ ν∈B, ω ν^n`.
-/
def exactDegreeOfEverySimpleBModePacket : Prop :=
  ∀ (M L k b : ℕ) (P : Polynomial ℂ) (ω : Fin L → ℂ),
    P ≠ 0 →
    P.natDegree + 1 = M →
    (∀ ν : Fin L, ‖ω ν‖ = 1) →
    (∀ ν : Fin L, ω ν ≠ 1) →
    Function.Injective ω →
    (∀ ν : Fin L, ∃ μ : Fin L, ω μ = star (ω ν)) →
    b ≤ k →
    ∀ B : Finset (Fin L), B.card = b →
      ∃ q : Polynomial ℂ,
        (q.natDegree : ℤ) =
          (k - b : ℤ) * ((M : ℤ) - (k - b : ℤ)) ∧
        (q.natDegree : ℤ) =
          (k - b : ℤ) * ((M : ℤ) - (k : ℤ) + (b : ℤ)) ∧
        ∀ n : ℕ,
          q.eval (n : ℂ) = simplePacketCoefficient (k := k) P ω B n

end MathlibPlus.Open.Analysis
