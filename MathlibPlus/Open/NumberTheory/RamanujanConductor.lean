import Mathlib

open scoped BigOperators
open Filter Set

namespace MathlibPlus.Open.NumberTheory.RamanujanConductor

noncomputable section

/-- The squarefree-divisor interval remainder. -/
def divisorRemainder (d t H : ℕ) : ℚ :=
  (((t + H) / d : ℕ) : ℚ) - ((t / d : ℕ) : ℚ) - (H : ℚ) / (d : ℚ)

def divisorTrace (Q : ℕ) (coeffs : ℕ → ℂ) (t H : ℕ) : ℂ :=
  Finset.sum Q.divisors
    (fun d => coeffs d * (divisorRemainder d t H : ℂ))

def conductorCoefficient (Q q : ℕ) (coeffs : ℕ → ℂ) : ℂ :=
  Finset.sum (Q.divisors.filter (fun d => q ∣ d))
    (fun d => coeffs d / (d : ℂ))

def ramanujanCharacter (x : ℚ) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))

def ramanujanSum (q n : ℕ) : ℂ :=
  Finset.sum (Finset.range q) (fun a =>
    if Nat.Coprime a q then
      ramanujanCharacter ((a * n : ℚ) / (q : ℚ))
    else 0)

def ramanujanSumInt (q : ℕ) (n : ℤ) : ℂ :=
  Finset.sum (Finset.range q) (fun a =>
    if Nat.Coprime a q then
      ramanujanCharacter ((a : ℚ) * (n : ℚ) / (q : ℚ))
    else 0)

/-- Claim 37045: the two squarefree-divisor traces and their conductor
coefficients, with the floor convention made explicit. -/
def claim37045 : Prop :=
  ∀ Q : ℕ, Squarefree Q → 0 < Q → ∀ coeffs : ℕ → ℂ, ∀ t H : ℕ,
    divisorTrace Q coeffs t H =
      Finset.sum Q.divisors (fun d =>
        coeffs d *
          ((((t + H) / d : ℕ) : ℚ) - ((t / d : ℕ) : ℚ) -
            (H : ℚ) / (d : ℚ) : ℂ)) ∧
    ∀ q : ℕ,
      conductorCoefficient Q q coeffs =
        Finset.sum (Q.divisors.filter (fun d => q ∣ d))
          (fun d => coeffs d / (d : ℂ))

/-- Claim 37046: exact decomposition of every squarefree divisor trace into
primitive additive conductors. -/
def claim37046 : Prop :=
  ∀ Q : ℕ, Squarefree Q → 0 < Q → ∀ coeffs : ℕ → ℂ, ∀ t H : ℕ,
    divisorTrace Q coeffs t H =
      Finset.sum (Q.divisors.filter (fun q => q > 1)) (fun q =>
        conductorCoefficient Q q coeffs *
          Finset.sum (Finset.Icc 1 H) (fun j => ramanujanSum q (t + j)))

/-- The finite geometric packets used for the energy identities. -/
def packet (H a q : ℕ) : ℂ :=
  Finset.sum (Finset.Icc 1 H)
    (fun j => ramanujanCharacter ((a * j : ℚ) / (q : ℚ)))

def packetEnergy (H q : ℕ) : ℝ :=
  Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q))
    (fun a => ‖packet H a q‖ ^ 2)

def packetAlgebraMass (H q : ℕ) : ℝ :=
  Finset.sum ((Finset.range q).filter (fun a => Nat.Coprime a q))
    (fun a => ‖packet H a q‖)

def primitiveConductorSupport (q : ℕ) : Set ℚ :=
  {x | ∃ a : ℕ, a < q ∧ Nat.Coprime a q ∧
    x = (a : ℚ) / (q : ℚ)}

/-- Claim 37048: the packet data and disjoint support of distinct reduced
additive conductors. -/
def claim37048 : Prop :=
  (∀ H q a : ℕ, packet H a q =
    Finset.sum (Finset.Icc 1 H)
      (fun j => ramanujanCharacter ((a * j : ℚ) / (q : ℚ)))) ∧
  (∀ q₁ q₂ : ℕ, q₁ ≠ q₂ →
    Disjoint (primitiveConductorSupport q₁)
      (primitiveConductorSupport q₂))

/-- The exact diagonal energy and Fourier-algebra quantities. -/
def traceEnergy (Q H : ℕ) (coeffs : ℕ → ℂ) : ℝ :=
  (1 / (Q : ℝ)) *
    Finset.sum (Finset.range Q)
      (fun t => ‖divisorTrace Q coeffs t H‖ ^ 2)

def traceAlgebraNorm (Q H : ℕ) (coeffs : ℕ → ℂ) : ℝ :=
  Finset.sum (Q.divisors.filter (fun q => q > 1))
    (fun q => ‖conductorCoefficient Q q coeffs‖ * packetAlgebraMass H q)

/-- Claim 37050: orthogonality gives the exact conductor energy, algebra norm,
and autocorrelation formula. -/
def claim37050 : Prop :=
  ∀ Q : ℕ, Squarefree Q → 0 < Q → ∀ coeffs : ℕ → ℂ, ∀ H : ℕ,
    traceEnergy Q H coeffs =
      Finset.sum (Q.divisors.filter (fun q => q > 1)) (fun q =>
        ‖conductorCoefficient Q q coeffs‖ ^ 2 * packetEnergy H q) ∧
    traceAlgebraNorm Q H coeffs =
      Finset.sum (Q.divisors.filter (fun q => q > 1)) (fun q =>
        ‖conductorCoefficient Q q coeffs‖ * packetAlgebraMass H q) ∧
    ∀ q : ℕ,
      (packetEnergy H q : ℂ) =
        Finset.sum (Finset.Icc (-(H : ℤ) + 1) ((H : ℤ) - 1))
          (fun u => ((H - Int.natAbs u : ℤ) : ℂ) * ramanujanSumInt q u)

end
end MathlibPlus.Open.NumberTheory.RamanujanConductor
