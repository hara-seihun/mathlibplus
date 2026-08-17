import MathlibPlus.Open.ResearchFormalization.R2632Claim42992

namespace MathlibPlus.Open.ResearchFormalization.R2632.Claim42988

noncomputable section

open Filter
open MathlibPlus.Open.ResearchFormalization.R2632.Claim42992

/-- The matching integer order `r = floor (d x)` in the fixed-slope criterion. -/
def matchingOrder42988 (d x : ℝ) : ℕ :=
  Nat.floor (d * x)

/-- The factorial-normalized magnitude of the exterior-square channel at one
fixed slope. -/
def fixedSlopeExteriorChannel42988
    (S_f : ℕ → ℝ) (d x : ℝ) : ℝ :=
  let r := matchingOrder42988 d x
  x ^ r / (Nat.factorial r : ℝ) *
    |exteriorSquare42992 S_f x r|

/-- The limsup exponential rate of the fixed-slope magnitude channel. -/
def fixedSlopeExteriorRate42988
    (S_f : ℕ → ℝ) (d : ℝ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => x⁻¹ *
      Real.log (1 + fixedSlopeExteriorChannel42988 S_f d x))
    Filter.atTop

/-- The literal-prime determinant channel at the same fixed slope and the
uniform cutoff `C x^(5/3)(log x)^2`. -/
def finiteFixedSlopeExteriorChannel42988
    (S_f : ℕ → ℝ) (d C x : ℝ) : ℝ :=
  let r := matchingOrder42988 d x
  x ^ r / (Nat.factorial r : ℝ) *
    |finiteDeterminant42992 S_f x r (cutoff42992 C x)|

/-- The finite-cutoff fixed-slope exponential rate. -/
def finiteFixedSlopeExteriorRate42988
    (S_f : ℕ → ℝ) (d C : ℝ) : ℝ :=
  Filter.limsup
    (fun x : ℝ => x⁻¹ *
      Real.log (1 + finiteFixedSlopeExteriorChannel42988 S_f d C x))
    Filter.atTop

/-- Recurrent nonnegativity of the signed exterior-square channel, with no
absolute value. -/
def fixedSlopeSignRecurrence42988 (S_f : ℕ → ℝ) : Prop :=
  ∀ d : ℝ, 0 < d →
    ∀ᶠ x : ℝ in Filter.atTop,
      0 ≤ exteriorSquare42992 S_f x (matchingOrder42988 d x)

/-- The uniform finite-prime transfer needed to compare one fixed slope with a
finite determinant cutoff.  The bound is uniform in every order `r ≤ A x`. -/
def fixedSlopeFiniteTransfer42988
    (S_f : ℕ → ℝ) (d : ℝ) : Prop :=
  ∃ H C : ℝ,
    0 < H ∧ 0 < C ∧
      uniformFinitePrimeTransfer42992 S_f (d + 1) H C ∧
        (riemannHypothesis42992 ↔
          finiteFixedSlopeExteriorRate42988 S_f d C = 0)

/-- Claim 42988: every positive fixed slope has the exact RH rate criterion;
the same pointwise criterion survives the uniform literal-prime cutoff, and
signed recurrence is not a replacement for the magnitude criterion. -/
def claim_42988 : Prop :=
  ∀ (S_f : ℕ → ℝ), poissonCharlierCarrier42992 S_f →
    (riemannHypothesis42992 ↔
      ∀ d : ℝ, 0 < d → fixedSlopeExteriorRate42988 S_f d = 0) ∧
      (∀ d : ℝ, 0 < d → fixedSlopeFiniteTransfer42988 S_f d) ∧
      ¬ fixedSlopeSignRecurrence42988 S_f

end

end MathlibPlus.Open.ResearchFormalization.R2632.Claim42988
