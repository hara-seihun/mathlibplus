import MathlibPlus.Open.Analysis.AdmittedO0098

open scoped BigOperators

namespace MathlibPlus.Open.Analysis.Claim11433

noncomputable section

/-- The translation appearing in one logarithmic prime factor. -/
private def logarithmicTranslation (a : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x => f (x + a)

/-- The concrete factor `I - q^(-σ) T_(log q)` on the admitted function
carrier. -/
private def transferDifference (σ : ℝ) (q : ℕ) (f : ℝ → ℂ) : ℝ → ℂ :=
  fun x =>
    f x - (MathlibPlus.Open.Analysis.primeWeight σ q : ℂ) *
      logarithmicTranslation (Real.log (q : ℝ)) f x

/-- The concrete Neumann-series inverse factor already used by the admitted
finite transfer carrier. -/
private def inverseTransferFactor (σ : ℝ) (q : ℕ) :
    (ℝ → ℂ) → (ℝ → ℂ) :=
  fun f => MathlibPlus.Open.Analysis.primeResolvent σ q f

/-- The finite ordered product of the explicit inverse factors. -/
private def inverseTransferProduct (σ : ℝ) (P : ℕ) :
    (ℝ → ℂ) → (ℝ → ℂ) :=
  (MathlibPlus.Open.Analysis.primesUpTo P).toList.foldl
    (fun R q => fun f => inverseTransferFactor σ q (R f))
    (fun f : ℝ → ℂ => f)

/-- Claim 11433: the finite transfer is the explicit product of the prime
resolvent factors, its Fourier multiplier is the displayed Euler product,
and zero frequency maximizes its modulus. -/
def finiteTransferOperatorAndMultiplier_claim11433 : Prop :=
  ∀ σ : ℝ, 0 < σ → σ < 1 →
    ∀ P : ℕ,
      (∀ f : ℝ → ℂ,
        MathlibPlus.Open.Analysis.finiteTransfer σ P f =
          inverseTransferProduct σ P f) ∧
      (∀ ξ : ℝ,
        MathlibPlus.Open.Analysis.finiteTransferMultiplier σ P ξ =
          ∏ q ∈ MathlibPlus.Open.Analysis.primesUpTo P,
            (1 -
                (MathlibPlus.Open.Analysis.primeWeight σ q : ℂ) *
                  Complex.exp
                    (Complex.I * (ξ : ℂ) *
                      (Real.log (q : ℝ) : ℂ)))⁻¹) ∧
      (∀ ξ : ℝ,
        ‖MathlibPlus.Open.Analysis.finiteTransferMultiplier σ P ξ‖ ≤
          ‖MathlibPlus.Open.Analysis.finiteTransferMultiplier σ P 0‖)

end

end MathlibPlus.Open.Analysis.Claim11433
