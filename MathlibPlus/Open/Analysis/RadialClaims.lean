import Mathlib

namespace MathlibPlus.Open.Analysis.RadialClaims

noncomputable section

/-- The first-order shift used in the radial factors. -/
def radialShift (sign : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun u => deriv f u + sign * f u

/-- The two radial second-order factors. -/
def radialMinus (x : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun u =>
    deriv (radialShift (-((1 : ℝ) / 2)) f) u
      - ((1 : ℝ) / 2) * radialShift (-((1 : ℝ) / 2)) f u
      + x ^ 2 * f u

def radialPlus (x : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun u =>
    deriv (radialShift ((1 : ℝ) / 2) f) u
      + ((1 : ℝ) / 2) * radialShift ((1 : ℝ) / 2) f u
      + x ^ 2 * f u

/-- The fourth-order radial operator `L_x = A_{x,+} A_{x,-}`. -/
def radialL (x : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  radialPlus x (radialMinus x f)

/-- The decaying half-line solution, including the confluent branch at `x = 0`. -/
def decayingRadialSolution (x p q : ℝ) : ℝ → ℝ :=
  fun u =>
    if x = 0 then
      Real.exp (-u / 2) * (p + (q + p / 2) * u)
    else
      Real.exp (-u / 2) *
        (p * Real.cos (x * u) + (q + p / 2) * Real.sin (x * u) / x)

/-- Claim 11605: the solution from the half-line statement is in the first-factor
kernel and obeys the stated first-factor identity. -/
def claim11605FirstFactorIdentity : Prop :=
  ∀ (x p q : ℝ),
    radialPlus x (decayingRadialSolution x p q) = 0 ∧
      radialMinus x (decayingRadialSolution x p q) =
        fun u => -2 * deriv (decayingRadialSolution x p q) u

/-- Claim 11606: Green's identity for the radial factorization. -/
def claim11606GreenIdentity : Prop :=
  ∀ (x : ℝ) (f g : ℝ → ℝ) (u : ℝ),
    let H := radialMinus x f
    g u * radialL x f u - radialMinus x g u * radialMinus x f u =
      deriv (fun v => g v * (deriv H v + H v) - deriv g v * H v) u

/-- The value-derivative boundary jet. -/
def valueDerivativeJet (f : ℝ → ℝ) : Fin 2 → ℝ :=
  ![f 0, deriv f 0]

/-- The conormal boundary jet attached to `H = A_{x,-} f`. -/
def conormalJet (x : ℝ) (f : ℝ → ℝ) : Fin 2 → ℝ :=
  let H := radialMinus x f
  ![deriv H 0 + H 0, -H 0]

/-- The action of `2 diag(x^2+1/4,1)` on a two-component jet. -/
def calderonAction (x : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ :=
  ![2 * (x ^ 2 + (1 : ℝ) / 4) * v 0, 2 * v 1]

/-- Claim 11607: the conormal jet of the decaying solution is the exact
Calderón matrix applied to its value-derivative jet. -/
def claim11607CalderonMatrix : Prop :=
  ∀ (x p q : ℝ),
    conormalJet x (decayingRadialSolution x p q) =
      calderonAction x (valueDerivativeJet (decayingRadialSolution x p q))

/-- The Volterra test function used by the hostile-tail witness. -/
def volterraTest (ω : ℝ) : ℝ → ℝ :=
  fun u => u * Real.cosh (ω * u)

/-- Endpoint derivatives through order three vanish. -/
def zeroThreeJet (f : ℝ → ℝ) : Prop :=
  f 0 = 0 ∧
    deriv f 0 = 0 ∧
      deriv (deriv f) 0 = 0 ∧
        deriv (deriv (deriv f)) 0 = 0

/-- Claim 11611: the explicit finite-jet witness has the stated positive radial
energy and the stated tail pairing, while negation preserves the jet and energy
and changes only the tail sign. -/
def claim11611FiniteJetHostileWitness : Prop :=
  let ψ : ℝ → ℝ := fun u => u ^ 4 * Real.exp (-2 * u)
  let w : ℝ → ℝ := volterraTest ((1 : ℝ) / 4)
  let energy (f : ℝ → ℝ) : ℝ :=
    ∫ u in Set.Ici (0 : ℝ), |radialMinus 1 f u| ^ 2
  let tail (f : ℝ → ℝ) : ℝ :=
    ∫ u in Set.Ici (0 : ℝ), f u * radialL 1 w u
  let negψ : ℝ → ℝ := fun u => -ψ u
  zeroThreeJet ψ ∧
    energy ψ = (10467 : ℝ) / 32768 ∧
      tail ψ = (97132866688 : ℝ) / 20841167403 ∧
        0 < tail ψ ∧
          zeroThreeJet negψ ∧
            energy negψ = energy ψ ∧
              tail negψ = -tail ψ

end

end MathlibPlus.Open.Analysis.RadialClaims
