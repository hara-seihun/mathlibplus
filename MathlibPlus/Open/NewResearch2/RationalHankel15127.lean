import MathlibPlus.Open.NewResearch2.RationalHankel15103

open scoped BigOperators
open Polynomial
open Classical

namespace MathlibPlus.Open.NewResearch2.RationalHankelStructure

noncomputable section

/-- The iterated polynomial derivative used by normalized Hermite jets. -/
def iteratedPolynomialDerivative : ℕ → Polynomial ℂ → Polynomial ℂ
  | 0, p => p
  | n + 1, p => Polynomial.derivative (iteratedPolynomialDerivative n p)

/-- A normalized derivative jet at a root, with the factorial normalization. -/
def normalizedHermiteJet {J : ℕ} (ζ : Fin J → ℂ) (μ : Fin J → ℕ)
    (p : Polynomial ℂ) (jk : Σ j : Fin J, Fin (μ j)) : ℂ :=
  Polynomial.eval (ζ jk.1)
    (iteratedPolynomialDerivative (jk.2 : ℕ) p) /
      (Nat.factorial (jk.2 : ℕ) : ℂ)

/-- The Frobenius norm of all Hermite numerator jets in all channels. -/
def allChannelCoupling {d J : ℕ} (P : Fin d → Polynomial ℂ)
    (ζ : Fin J → ℂ) (μ : Fin J → ℕ) : ℝ :=
  Real.sqrt (∑ x : (Σ j : Fin J, Fin (μ j)) × Fin d,
    ‖normalizedHermiteJet ζ μ (P x.2) x.1‖ ^ 2)

/-- A candidate shell factor, represented by its distinct roots and positive
multiplicities.  The nonzero scalar records that the factor need not be monic. -/
def candidateShell {J : ℕ} (Q S : Polynomial ℂ)
    (ζ : Fin J → ℂ) (μ : Fin J → ℕ) : Prop :=
  S ≠ 0 ∧ S ∣ Q ∧
    (∀ j : Fin J, 0 < μ j) ∧
    (∀ i j : Fin J, i ≠ j → ζ i ≠ ζ j) ∧
    ∃ a : ℂ, a ≠ 0 ∧
      S = Polynomial.C a *
        ∏ j : Fin J, (Polynomial.X - Polynomial.C (ζ j)) ^ μ j

/-- The proper vector-rational data used by the common-denominator carrier. -/
def properVectorRationalData {d : ℕ} (P : Fin d → Polynomial ℂ)
    (Q : Polynomial ℂ) : Prop :=
  Q ≠ 0 ∧ Q.coeff 0 = 1 ∧
    (∀ i : Fin d, (P i).degree < Q.degree)

/-- The certified excess multiplicity is nominal denominator multiplicity minus
recovered minimal pole-head multiplicity. -/
def certifiedExcessCount (nominal minimal : ℕ) : ℤ :=
  (nominal : ℤ) - (minimal : ℤ)

/-- The shell is eligible for removal when its certified excess count covers
its degree. -/
def eligibleShellForRemoval {J : ℕ} (Q S : Polynomial ℂ)
    (ζ : Fin J → ℂ) (μ : Fin J → ℕ) (nominal minimal : ℕ) : Prop :=
  candidateShell Q S ζ μ ∧
    (S.natDegree : ℤ) ≤ certifiedExcessCount nominal minimal

/-- A shell factor would delete a minimal-denominator mode exactly when it is
not a factor of the common Froissart divisor. -/
def wouldDeleteMinimalDenominatorMode {d : ℕ}
    (P : Fin d → Polynomial ℂ) (Q S : Polynomial ℂ) : Prop :=
  S ∣ Q ∧ ¬ S ∣ commonFroissartDivisor P Q

/-- The class assumption in the no-false-removal assertion. -/
def noFalseRemovalClass {d : ℕ} (P : Fin d → Polynomial ℂ)
    (Q : Polynomial ℂ) (τtrue : ℝ) : Prop :=
  ∀ (S : Polynomial ℂ) (J : ℕ) (ζ : Fin J → ℂ) (μ : Fin J → ℕ)
    (nominal minimal : ℕ),
    eligibleShellForRemoval Q S ζ μ nominal minimal →
      wouldDeleteMinimalDenominatorMode P Q S →
        τtrue ≤ allChannelCoupling P ζ μ

/-- The observed all-channel coupling comes with a two-sided certified error. -/
def certifiedCouplingInterval {d J : ℕ} (P : Fin d → Polynomial ℂ)
    (ζ : Fin J → ℂ) (μ : Fin J → ℕ) (ρhat eJet : ℝ) : Prop :=
  0 ≤ eJet ∧
    ρhat - eJet ≤ allChannelCoupling P ζ μ ∧
      allChannelCoupling P ζ μ ≤ ρhat + eJet

/-- The three outcomes of the shell classifier. -/
inductive ShellDecision where
  | removable
  | genuine
  | unresolved

/-- The classifier's exact branch specification.  In particular, the final
branch is the ordinary unresolved case: neither removal criterion holds nor
does the lower confidence bound certify a genuine mode. -/
def shellDecisionSpec {J : ℕ}
    (Q S : Polynomial ℂ) (ζ : Fin J → ℂ) (μ : Fin J → ℕ)
    (nominal minimal : ℕ) (ρhat eJet τrem τtrue : ℝ) :
    ShellDecision → Prop
  | .removable =>
      candidateShell Q S ζ μ ∧
        (S.natDegree : ℤ) ≤ certifiedExcessCount nominal minimal ∧
        ρhat + eJet ≤ τrem
  | .genuine =>
      candidateShell Q S ζ μ ∧ ρhat - eJet ≥ τtrue
  | .unresolved =>
      candidateShell Q S ζ μ ∧
        ¬ ((S.natDegree : ℤ) ≤ certifiedExcessCount nominal minimal ∧
          ρhat + eJet ≤ τrem) ∧
        ¬ (ρhat - eJet ≥ τtrue)

/-- Claim 15127: the all-channel three-way classifier is exhaustive and has no
false removals on the stated coupling-threshold class. -/
def claim_15127 : Prop :=
  ∀ (d : ℕ) (P : Fin d → Polynomial ℂ) (Q : Polynomial ℂ)
    (τrem τtrue : ℝ),
    properVectorRationalData P Q →
      0 ≤ τrem ∧ τrem < τtrue →
        noFalseRemovalClass P Q τtrue →
          ∀ (S : Polynomial ℂ) (J : ℕ) (ζ : Fin J → ℂ)
            (μ : Fin J → ℕ) (nominal minimal : ℕ) (ρhat eJet : ℝ),
            candidateShell Q S ζ μ →
              certifiedCouplingInterval P ζ μ ρhat eJet →
                (∃! decision : ShellDecision,
                    shellDecisionSpec Q S ζ μ nominal minimal
                      ρhat eJet τrem τtrue decision) ∧
                  (∀ decision : ShellDecision,
                    shellDecisionSpec Q S ζ μ nominal minimal
                      ρhat eJet τrem τtrue decision →
                      decision = .removable →
                        ¬ wouldDeleteMinimalDenominatorMode P Q S)

end
end MathlibPlus.Open.NewResearch2.RationalHankelStructure
