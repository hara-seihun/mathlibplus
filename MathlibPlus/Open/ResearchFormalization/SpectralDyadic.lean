import Mathlib

namespace MathlibPlus
namespace Open
namespace ResearchFormalization
namespace SpectralDyadic

noncomputable section

abbrev C2 := Fin 2

/-- The Meixner–Pollaczek spectral amplitude from the admitted packet. -/
def mpAmplitude (a t : ℝ) : ℂ :=
  Complex.cpow (2 : ℂ)
      (((a / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ)) *
    Complex.Gamma (((a / 2 : ℝ) : ℂ) - Complex.I * (t : ℂ)) /
      Complex.sqrt (((2 * Real.pi : ℝ) : ℂ) * Complex.Gamma (a : ℂ))

/-- The two shifted chiral amplitudes h₊ and h₋. -/
def mpChiralShapes (a τ r : ℝ) : C2 → ℂ :=
  ![mpAmplitude a (r - τ / 2), mpAmplitude a (r + τ / 2)]

/-- The critical-line dyadic off-diagonal factor 2^(s-1). -/
def dyadicPhase (τ : ℝ) : ℂ :=
  ((1 / Real.sqrt 2 : ℝ) : ℂ) *
    Complex.exp (Complex.I * ((τ * Real.log 2 : ℝ) : ℂ))

def schurFactor (τ : ℝ) : Matrix C2 C2 ℂ :=
  !![1, dyadicPhase τ; star (dyadicPhase τ), 1]

def spectralDensity (a τ r : ℝ) : Matrix C2 C2 ℂ :=
  let h := mpChiralShapes a τ r
  !![star (h 0) * h 0, star (h 0) * h 1;
     star (h 1) * h 0, star (h 1) * h 1]

def schurProduct (A B : Matrix C2 C2 ℂ) : Matrix C2 C2 ℂ :=
  fun i j => A i j * B i j

def schurDensity (a τ r : ℝ) : Matrix C2 C2 ℂ :=
  schurProduct (schurFactor τ) (spectralDensity a τ r)

/-- Concrete positivity predicate for a complex 2-by-2 spectral matrix. -/
def complexPositiveDef (M : Matrix C2 C2 ℂ) : Prop :=
  Matrix.IsHermitian M ∧
    ∀ v : C2 → ℂ, v ≠ 0 →
      0 < (dotProduct (fun i => star (v i)) (M.mulVec v)).re

/-- In dimension two, these are the exact singular and full-rank conditions. -/
def rankOneTwo (M : Matrix C2 C2 ℂ) : Prop :=
  M ≠ 0 ∧ Matrix.det M = 0

def rankTwoTwo (M : Matrix C2 C2 ℂ) : Prop :=
  Matrix.det M ≠ 0

/-- Claim 7814: the dyadic Schur completion is positive definite and full rank. -/
def claim7814 : Prop :=
  ∀ (a τ r : ℝ), 0 < a →
    let h := mpChiralShapes a τ r
    let S := spectralDensity a τ r
    let M := schurDensity a τ r
    Complex.Gamma (((a / 2 : ℝ) : ℂ) -
        Complex.I * ((r - τ / 2 : ℝ) : ℂ)) ≠ 0 ∧
      Complex.Gamma (((a / 2 : ℝ) : ℂ) -
        Complex.I * ((r + τ / 2 : ℝ) : ℂ)) ≠ 0 ∧
      rankOneTwo S ∧
      complexPositiveDef M ∧
      Matrix.det M =
        (((1 / 2 : ℝ) * Complex.normSq (h 0) * Complex.normSq (h 1) : ℝ) : ℂ) ∧
      0 < (1 / 2 : ℝ) * Complex.normSq (h 0) * Complex.normSq (h 1) ∧
      rankTwoTwo M

end

end SpectralDyadic
end ResearchFormalization
end Open
end MathlibPlus
