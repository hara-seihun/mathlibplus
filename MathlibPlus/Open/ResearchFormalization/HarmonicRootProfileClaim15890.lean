import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.HarmonicRootProfileClaim15890

open MvPolynomial
open scoped BigOperators

noncomputable section

/-- Claim 15890: the verified three-root profile-polynomial interaction is
nonzero, harmonic for card summation, invisible to all three separate
one-root-forgetting maps, symmetric under the six root relabelings, and rules
out a linear left inverse for the combined observations. -/
def harmonicInteraction_claim15890 : Prop :=
  let h : MvPolynomial (Fin 8) ℚ :=
    - X 0 + X 1 + X 2 + X 3 - X 4 - X 5 - X 6 + X 7
  let forget₁ : Fin 8 → Fin 4 := ![0, 0, 1, 2, 1, 2, 3, 3]
  let forget₂ : Fin 8 → Fin 4 := ![0, 1, 0, 2, 1, 3, 2, 3]
  let forget₃ : Fin 8 → Fin 4 := ![0, 1, 2, 0, 3, 1, 2, 3]
  let rootRelabel : Fin 6 → Fin 8 → Fin 8 :=
    ![![0, 1, 2, 3, 4, 5, 6, 7],
      ![0, 2, 1, 3, 4, 6, 5, 7],
      ![0, 3, 2, 1, 6, 5, 4, 7],
      ![0, 1, 3, 2, 5, 4, 6, 7],
      ![0, 2, 3, 1, 6, 4, 5, 7],
      ![0, 3, 1, 2, 5, 6, 4, 7]]
  let cardSum : MvPolynomial (Fin 8) ℚ → MvPolynomial (Fin 8) ℚ :=
    fun p => ∑ i : Fin 8, pderiv i p
  let forgetMap₁ : MvPolynomial (Fin 8) ℚ → MvPolynomial (Fin 4) ℚ :=
    fun p =>
      eval₂Hom (algebraMap ℚ (MvPolynomial (Fin 4) ℚ))
        (fun i => (X (forget₁ i) : MvPolynomial (Fin 4) ℚ)) p
  let forgetMap₂ : MvPolynomial (Fin 8) ℚ → MvPolynomial (Fin 4) ℚ :=
    fun p =>
      eval₂Hom (algebraMap ℚ (MvPolynomial (Fin 4) ℚ))
        (fun i => (X (forget₂ i) : MvPolynomial (Fin 4) ℚ)) p
  let forgetMap₃ : MvPolynomial (Fin 8) ℚ → MvPolynomial (Fin 4) ℚ :=
    fun p =>
      eval₂Hom (algebraMap ℚ (MvPolynomial (Fin 4) ℚ))
        (fun i => (X (forget₃ i) : MvPolynomial (Fin 4) ℚ)) p
  let Marginals :=
    MvPolynomial (Fin 8) ℚ ×
      (MvPolynomial (Fin 4) ℚ ×
        (MvPolynomial (Fin 4) ℚ × MvPolynomial (Fin 4) ℚ))
  let observations : MvPolynomial (Fin 8) ℚ → Marginals :=
    fun p => (cardSum p, (forgetMap₁ p, (forgetMap₂ p, forgetMap₃ p)))
  h ≠ 0 ∧
    cardSum h = 0 ∧
    forgetMap₁ h = 0 ∧
    forgetMap₂ h = 0 ∧
    forgetMap₃ h = 0 ∧
    (∀ k : Fin 6,
      eval₂Hom (algebraMap ℚ (MvPolynomial (Fin 8) ℚ))
        (fun i => (X (rootRelabel k i) : MvPolynomial (Fin 8) ℚ)) h = h) ∧
    ¬ ∃ R : Marginals →ₗ[ℚ] MvPolynomial (Fin 8) ℚ,
      ∀ p : MvPolynomial (Fin 8) ℚ, R (observations p) = p

end

end MathlibPlus.Open.ResearchFormalization.HarmonicRootProfileClaim15890
