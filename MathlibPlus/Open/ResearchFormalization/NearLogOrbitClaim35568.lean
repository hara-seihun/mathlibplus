import MathlibPlus.Open.GraphTheory.AdmittedCubeFunctionInequalities

namespace MathlibPlus.Open.ResearchFormalization.NearLogOrbitClaim35568

open Classical
open Filter
open Asymptotics
open MathlibPlus.Open.GraphTheory.AdmittedCubeFunctionInequalities

noncomputable section

abbrev EdgeSystem (n : ℕ) :=
  ∀ i : Fin n, F2Omega n i → Bool

abbrev EdgeSystemFamily := ∀ n : ℕ, EdgeSystem n

/-- Translation of a literal direction function by a cube vector. -/
def translatedLiteral {n : ℕ} (f : EdgeSystem n) (i : Fin n)
    (v : F2Cube n) : F2Cube n → Bool :=
  fun x => f2EdgeAt f i (x + v)

/-- The literal translation-orbit cardinality, not an orbit of vertices or of
an induced vertex subgraph. -/
def literalDirectionalOrbitSize {n : ℕ} (f : EdgeSystem n)
    (i : Fin n) : ℕ :=
  (Finset.univ.image (translatedLiteral f i)).card

def familyC4Free (F : EdgeSystemFamily) : Prop :=
  ∀ n : ℕ, f2C4Free (F n)

def familyOrbitBound (F : EdgeSystemFamily) (M : ℕ → ℕ) : Prop :=
  ∀ (n : ℕ) (i : Fin n), literalDirectionalOrbitSize (F n) i ≤ M n

def directionalMass (F : EdgeSystemFamily) (n : ℕ) : ℝ :=
  ∑ i : Fin n, f2Density (F n) i

def littleLinearError (s : ℕ → ℝ) : Prop :=
  ∃ e : ℕ → ℝ,
    IsLittleO atTop e (fun _ : ℕ => (1 : ℝ)) ∧
      ∀ᶠ n : ℕ in atTop,
        s n ≤ ((1 / 2 : ℝ) + e n) * (n : ℝ)

def orbitLogCondition (M : ℕ → ℕ) : Prop :=
  IsLittleO atTop
    (fun n : ℕ => (M n : ℝ) * Real.log (M n : ℝ))
    (fun n : ℕ => Real.log (n : ℝ))

def logBaseTwo (x : ℝ) : ℝ :=
  Real.log x / Real.log 2

def explicitOrbitCondition (M : ℕ → ℕ) (ε : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    (M n : ℝ) ≤
      (1 / 2 - ε) * logBaseTwo (n : ℝ) /
        logBaseTwo (logBaseTwo (n : ℝ))

def rankSequence (M : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.floor (logBaseTwo (M n : ℝ))

def sunflowerSizeSequence (M : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 ^ (rankSequence M n + 1) - 1

def chosenBlockSize (M : ℕ → ℕ) (C α : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (Real.rpow
    (((n : ℝ) ^ α) /
      (((rankSequence M n + 1 : ℕ) : ℝ) *
        (C * Real.log (2 * (sunflowerSizeSequence M n : ℝ))) ^
          sunflowerSizeSequence M n))
    (1 / ((sunflowerSizeSequence M n + 1 : ℕ) : ℝ)))

def blockExcessSequence (M : ℕ → ℕ) (n : ℕ) : ℝ :=
  (2 : ℝ) ^ rankSequence M n +
    ((rankSequence M n + 1 : ℕ) : ℝ) / 2

def remainderSequence (M : ℕ → ℕ) (C α : ℝ) (n : ℕ) : ℝ :=
  ((rankSequence M n + 1 : ℕ) : ℝ) *
    ((chosenBlockSize M C α n - 1 : ℕ) : ℝ) *
    (C * (chosenBlockSize M C α n : ℝ) *
      Real.log (2 * (sunflowerSizeSequence M n : ℝ))) ^
        sunflowerSizeSequence M n

def parameterControl (M : ℕ → ℕ) (C α : ℝ) : Prop :=
  (∀ᶠ n : ℕ in atTop,
    remainderSequence M C α n ≤ (n : ℝ) ^ α) ∧
    Tendsto
      (fun n : ℕ =>
        (chosenBlockSize M C α n : ℝ) / blockExcessSequence M n)
      atTop atTop

/-- The near-logarithmic orbit conclusion, with the two sufficient regimes
kept as independent branches.  The explicit logarithmic branch does not
assume the little-o orbit condition. -/
def asymptoticNearLogarithmicOrbit_claim35568 : Prop :=
  ∀ (C : ℝ) (F : EdgeSystemFamily) (M : ℕ → ℕ) (α : ℝ),
    4 ≤ C → 0 < α → α < 1 →
      familyC4Free F →
        familyOrbitBound F M →
          (orbitLogCondition M →
            parameterControl M C α ∧
              littleLinearError (directionalMass F)) ∧
          (∀ ε : ℝ, 0 < ε → ε < 1 / 2 →
            explicitOrbitCondition M ε →
              parameterControl M C (1 - ε) ∧
                littleLinearError (directionalMass F))

end
end MathlibPlus.Open.ResearchFormalization.NearLogOrbitClaim35568
