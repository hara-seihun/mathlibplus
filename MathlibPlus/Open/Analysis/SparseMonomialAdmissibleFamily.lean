import Mathlib

namespace MathlibPlus.Open.Analysis.SparseMonomialAdmissibleFamily

open Filter
noncomputable section

/-- The cutoff-dependent degree `⌊L^(1/(2k))⌋`. -/
def sparseDegree (k L : ℕ) : ℕ :=
  ⌊(L : ℝ) ^ (1 / (2 * (k : ℝ)))⌋₊

/-- The sparse family `P_L(u) = 1 + (B u)^(sparseDegree k L)`. -/
def sparsePolynomial (B : ℝ) (k L : ℕ) : Polynomial ℝ :=
  1 + (Polynomial.C B * Polynomial.X) ^ sparseDegree k L

/-- The coefficient-root envelope from the admissibility definition. -/
def coefficientRootEnvelope (B : ℝ) (P : ℕ → Polynomial ℝ) (d : ℕ → ℕ) : Prop :=
  ∀ L n, 1 ≤ n → n ≤ d L → |(P L).coeff n| ≤ B ^ n

/-- Admissibility at order `k`, with the fixed envelope `B_L = B`. -/
def admissibleAtOrder (B : ℝ) (k : ℕ) (P : ℕ → Polynomial ℝ) (d : ℕ → ℕ) : Prop :=
  1 ≤ B ∧
    coefficientRootEnvelope B P d ∧
    Tendsto (fun L : ℕ => B ^ k * (d L : ℝ) / (L : ℝ)) atTop (nhds 0) ∧
    Asymptotics.IsLittleO atTop
      (fun L : ℕ => (d L : ℝ) * Real.log B)
      (fun L : ℕ => (L : ℝ))

/-- The compact supremum appearing in the logarithmic gain. -/
def compactSup (B U : ℝ) (k L : ℕ) : ℝ :=
  sSup (Set.range (fun u : {u : ℝ // |u| ≤ U} =>
    |Polynomial.eval (u : ℝ) (sparsePolynomial B k L)|))

def logPlus (x : ℝ) : ℝ := max 0 (Real.log x)

/-- The compact logarithmic gain `log⁺ sup_{|u|≤U} |P_L(u)|`. -/
def compactGain (B U : ℝ) (k L : ℕ) : ℝ :=
  logPlus (compactSup B U k L)

/--
Claim 3118: for every fixed `B ≥ 1`, `k ≥ 1`, and `U` with `B*U > 1`,
the sparse family has the stated envelope and admissibility properties and
has compact logarithmic gain of order `L^(1/(2k))`.
-/
def claim3118 : Prop :=
  ∀ (B U : ℝ) (k : ℕ),
    1 ≤ B → 1 ≤ k → B * U > 1 →
      coefficientRootEnvelope B (sparsePolynomial B k) (sparseDegree k) ∧
      admissibleAtOrder B k (sparsePolynomial B k) (sparseDegree k) ∧
      Asymptotics.IsTheta atTop
        (fun L : ℕ => compactGain B U k L)
        (fun L : ℕ => (L : ℝ) ^ (1 / (2 * (k : ℝ))))

end
end MathlibPlus.Open.Analysis.SparseMonomialAdmissibleFamily
