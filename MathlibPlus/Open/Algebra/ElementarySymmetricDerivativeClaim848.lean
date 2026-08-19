import Mathlib

namespace MathlibPlus.Open.Algebra.ElementarySymmetricDerivative

open scoped BigOperators

noncomputable section

private def elementarySymmetricSum {R : Type*} [CommRing R]
    (N : ℕ) (α : Fin N → R) (k : ℕ) : R :=
  Finset.sum (Finset.powersetCard k (Finset.univ : Finset (Fin N)))
    (fun s => Finset.prod s (fun i => α i))

private def reciprocalProductPolynomial {R : Type*} [CommRing R]
    (N : ℕ) (α : Fin N → R) : Polynomial R :=
  ∏ ν : Fin N, (1 + Polynomial.C (α ν) * Polynomial.X)

/-- Claim 848: derivatives at zero of a reciprocal-root product recover the
factorial-scaled elementary-symmetric polynomial, and seven positive factors
satisfy the reciprocal-root complement identity. -/
def reciprocalRootProductIdentities : Prop :=
  (∀ (N : ℕ) (α : Fin N → ℝ) (k : ℕ),
    let G : Polynomial ℝ := reciprocalProductPolynomial N α
    let e : ℕ → ℝ := elementarySymmetricSum N α
    Polynomial.eval 0 ((Polynomial.derivative^[k]) G) =
      (Nat.factorial k : ℝ) * e k) ∧
  (∀ α : Fin 7 → ℝ, (∀ ν : Fin 7, 0 < α ν) →
    let E : ℝ := ∏ ν : Fin 7, α ν
    let β : Fin 7 → ℝ := fun ν => (α ν)⁻¹
    ∀ k : Fin 8,
      elementarySymmetricSum 7 α (k : ℕ) =
        E * elementarySymmetricSum 7 β (7 - (k : ℕ)))

end

end MathlibPlus.Open.Algebra.ElementarySymmetricDerivative
