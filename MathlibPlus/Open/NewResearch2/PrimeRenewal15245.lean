import MathlibPlus.Open.NewResearch2.PrimeRenewal15246

open scoped BigOperators

namespace MathlibPlus.Open.NewResearch2.PrimeRenewal15245

noncomputable section

open PrimeRenewal15246

/-- The Hilbert coefficient norm on the finite subset basis of the exterior
factor. -/
def koszulTwoNorm (P : Finset ℕ) (x : KoszulCarrier P) : ℝ :=
  Real.sqrt (∑ s : Finset (PrimeIndex P), ‖x s‖ ^ 2)

/-- The operator norm of the selected-generator contraction on the canonical
finite subset carrier. -/
def koszulHomotopyOperatorNorm (P : Finset ℕ) (q : PrimeIndex P) : ℝ :=
  sSup {r : ℝ |
    ∃ x : KoszulCarrier P,
      koszulTwoNorm P x = 1 ∧
        r = koszulTwoNorm P (koszulHomotopy P q x)}

/-- Claim 15245: every nonempty finite prime cube has the explicit selected
contraction, with the uniform inverse/contraction norm bound and exact
contracting-homotopy identity. -/
def claim_15245 : Prop :=
  (∀ p : ℕ, Nat.Prime p →
    ‖primeEulerFaceInverse p‖ =
        (1 - Real.rpow (p : ℝ) (- (1 : ℝ) / 2))⁻¹ ∧
      ‖primeEulerFaceInverse p‖ ≤ 2 + Real.sqrt 2) ∧
    (∀ P : Finset ℕ,
      (∀ p ∈ P, Nat.Prime p) → P.Nonempty →
        finitePrimeKoszulContractible P ∧
          ∀ q : PrimeIndex P,
            koszulHomotopyOperatorNorm P q ≤ 2 + Real.sqrt 2)

end

end MathlibPlus.Open.NewResearch2.PrimeRenewal15245
