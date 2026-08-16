import Mathlib

namespace MathlibPlus.Open.Research

noncomputable section

abbrev QIndex := Fin 2 × Fin 2
abbrev QMatrix := Matrix QIndex QIndex ℂ
abbrev PMatrix := Matrix (Fin 2) (Fin 2) ℂ

/-- The Pauli frame used by the admitted Gram-family statements. -/
def pauliI : PMatrix := 1

def pauliX : PMatrix := !![0, 1; 1, 0]

def pauliY : PMatrix := !![0, -Complex.I; Complex.I, 0]

def pauliZ : PMatrix := !![1, 0; 0, -1]

def tensor (A B : PMatrix) : QMatrix := Matrix.kronecker A B

def qFamily (x g t : ℝ) : QMatrix :=
  (((2 + x) / 4 : ℝ) : ℂ) • tensor pauliI pauliI
    - (((1 / 2 : ℝ) : ℂ) • tensor pauliX pauliX)
    - (((g / 4 : ℝ) : ℂ) • tensor pauliZ pauliY)
    + (((t : ℂ)) • tensor pauliY pauliZ)

def visibleGram (x g : ℝ) : QMatrix := qFamily x g 0

def hermitian (A : QMatrix) : Prop :=
  ∀ i j, A i j = star (A j i)

def partialTranspose (A : QMatrix) : QMatrix :=
  fun i j => A (i.1, j.2) (j.1, i.2)

def quadratic (A : QMatrix) (v : QIndex → ℂ) : ℝ :=
  (Complex.re (∑ i, star (v i) * (∑ j, A i j * v j)))

def unitVector (v : QIndex → ℂ) : Prop :=
  ∑ i, Complex.normSq (v i) = 1

def positiveSemidefinite (A : QMatrix) : Prop :=
  hermitian A ∧ ∀ v, 0 ≤ quadratic A v

def leastRayleigh (A : QMatrix) : ℝ :=
  sInf {r : ℝ | ∃ v, unitVector v ∧ quadratic A v = r}

def commonMargin (A : QMatrix) : ℝ :=
  min (leastRayleigh A) (leastRayleigh (partialTranspose A))

def nullPerturbation (a : Fin 7 → ℝ) : QMatrix :=
  ((a 0 : ℂ) • tensor pauliY pauliI)
    + ((a 1 : ℂ) • tensor pauliY pauliX)
    + ((a 2 : ℂ) • tensor pauliY pauliY)
    + ((a 3 : ℂ) • tensor pauliY pauliZ)
    + ((a 4 : ℂ) • tensor pauliI pauliZ)
    + ((a 5 : ℂ) • tensor pauliX pauliZ)
    + ((a 6 : ℂ) • tensor pauliZ pauliZ)

def allZero (a : Fin 7 → ℝ) : Prop := ∀ k, a k = 0

def bellCoefficientMatrix (x g t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![x / 4, t - g / 4; (4 + x) / 4, -t - g / 4]

def rankOneTwoByTwo (A : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
  (A 0 0 ≠ 0 ∨ A 0 1 ≠ 0 ∨ A 1 0 ≠ 0 ∨ A 1 1 ≠ 0)
    ∧ A 0 0 * A 1 1 - A 0 1 * A 1 0 = 0

def bellProductGauge (x g : ℝ) : ℝ := g / (2 * (2 + x))

def robustCanonical (x g : ℝ) : Prop :=
  ∀ a : Fin 7 → ℝ,
    commonMargin (visibleGram x g + nullPerturbation a) ≤ commonMargin (visibleGram x g)
      ∧ (commonMargin (visibleGram x g + nullPerturbation a) = commonMargin (visibleGram x g)
        ↔ allZero a)

def projector {ι : Type} (u : ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => u i * star (u j)

def separableGram (A : QMatrix) : Prop :=
  ∃ n : ℕ, ∃ w : Fin n → ℝ, ∃ u : Fin n → (Fin 2 → ℂ),
    ∃ v : Fin n → (Fin 2 → ℂ),
      (∀ k, 0 ≤ w k)
        ∧ A = ∑ k, ((w k : ℂ) • tensor (projector (u k)) (projector (v k)))

def splitLocalGram (A : QMatrix) : Prop := separableGram A

def pptCompletion (x g : ℝ) : Prop :=
  ∃ a : Fin 7 → ℝ,
    positiveSemidefinite (visibleGram x g + nullPerturbation a)
      ∧ positiveSemidefinite (partialTranspose (visibleGram x g + nullPerturbation a))

def separableCompletion (x g : ℝ) : Prop :=
  ∃ a : Fin 7 → ℝ, separableGram (visibleGram x g + nullPerturbation a)

def splitLocalCompletion (x g : ℝ) : Prop :=
  ∃ a : Fin 7 → ℝ, splitLocalGram (visibleGram x g + nullPerturbation a)

/--
The two canonical choices in Claim 13518, with the physical parameter range made
explicit so the Bell gauge denominator is nonzero.  The seven coefficients are
exactly the evaluation-null directions listed in the admitted repair context.
-/
def claim13518 : Prop :=
  ∀ x g : ℝ, 0 ≤ x → x ≤ 1 →
    (∀ t : ℝ, rankOneTwoByTwo (bellCoefficientMatrix x g t)
      ↔ t = bellProductGauge x g)
    ∧ robustCanonical x g
    ∧ (bellProductGauge x g = 0 ↔ g = 0)
    ∧ (g ≠ 0 → bellProductGauge x g ≠ 0)

def conjugateBy (U A : QMatrix) : QMatrix := U * A * U

def heat (lam : ℝ) (A : QMatrix) : QMatrix :=
  (((1 + lam) / 4 : ℝ) : ℂ) •
      (A + conjugateBy (tensor pauliX pauliX) A)
    + (((1 - lam) / 4 : ℝ) : ℂ) •
      (conjugateBy (tensor pauliX pauliI) A
        + conjugateBy (tensor pauliI pauliX) A)

def physicalPhase (lam x g : ℝ) : Prop :=
  0 ≤ x ∧ x ≤ 1 ∧ g ^ 2 = 72 * lam ^ 2 * x * (1 - x)

def phaseThreshold (lam : ℝ) : ℝ := 72 * lam ^ 2 / (1 + 72 * lam ^ 2)

def heatMatrixUnit (i j : QIndex) : QMatrix :=
  fun a b => if a = i ∧ b = j then 1 else 0

def heatChoi (Φ : QMatrix → QMatrix) : Matrix (QIndex × QIndex) (QIndex × QIndex) ℂ :=
  fun r c => Φ (heatMatrixUnit r.2 c.2) r.1 c.1

def bigProjector (u : QIndex → ℂ) : Matrix QIndex QIndex ℂ := projector u

def bigSeparable (A : Matrix (QIndex × QIndex) (QIndex × QIndex) ℂ) : Prop :=
  ∃ n : ℕ, ∃ w : Fin n → ℝ, ∃ u : Fin n → (QIndex → ℂ),
    ∃ v : Fin n → (QIndex → ℂ),
      (∀ k, 0 ≤ w k)
        ∧ A = ∑ k, ((w k : ℂ) • Matrix.kronecker (bigProjector (u k)) (bigProjector (v k)))

def entanglementBreaking (Φ : QMatrix → QMatrix) : Prop :=
  bigSeparable (heatChoi Φ)

def uniformSplitLocal (lam : ℝ) : Prop :=
  ∀ x g, physicalPhase lam x g → splitLocalCompletion x g

def uniformSeparable (lam : ℝ) : Prop :=
  ∀ x g, physicalPhase lam x g → separableCompletion x g

def uniformPPT (lam : ℝ) : Prop :=
  ∀ x g, physicalPhase lam x g → pptCompletion x g

/--
Claim 13519: the canonical positive threshold, the exact full-kernel split/PPT
threshold, the physical phase gap, and the uniform heat/entanglement-breaking
conclusions.  The final scope sentence of the admitted claim is a boundary on
these conclusions: no assertion here is made about Bell recoupling, higher-
dimensional non-Segre factorizations, or positivity without split locality.
-/
def claim13519 : Prop :=
  (∀ x g : ℝ, 0 ≤ x →
    (positiveSemidefinite (qFamily x g (bellProductGauge x g)) ↔ |g| ≤ 2 + x))
    ∧ (∀ x g : ℝ, 0 ≤ x → x ≤ 1 →
      (pptCompletion x g ↔ |g| ≤ x)
        ∧ (separableCompletion x g ↔ |g| ≤ x)
        ∧ (splitLocalCompletion x g ↔ |g| ≤ x))
    ∧ (∀ lam : ℝ, 0 < lam →
      (∃ x : ℝ, 0 < x ∧ x < phaseThreshold lam)
        ∧ (∀ x g : ℝ,
          0 < x → x < phaseThreshold lam →
            physicalPhase lam x g →
              ¬ pptCompletion x g ∧ ¬ separableCompletion x g
                ∧ ¬ splitLocalCompletion x g))
    ∧ (∀ lam : ℝ,
      0 ≤ lam → lam ≤ 1 →
        (uniformSplitLocal lam ↔ lam = 0)
          ∧ (uniformSeparable lam ↔ lam = 0)
          ∧ (uniformPPT lam ↔ lam = 0)
          ∧ (entanglementBreaking (heat lam) ↔ lam = 0))
    ∧ (∀ τ : ℝ, 0 < τ →
        ¬ uniformSplitLocal (Real.exp (-2 * τ))
          ∧ ¬ uniformSeparable (Real.exp (-2 * τ))
          ∧ ¬ uniformPPT (Real.exp (-2 * τ))
          ∧ ¬ entanglementBreaking (heat (Real.exp (-2 * τ))))
    ∧ (∀ lam x g : ℝ,
      0 < lam → physicalPhase lam x g →
        (separableCompletion x g ↔ x = 0 ∨ phaseThreshold lam ≤ x))

end
end MathlibPlus.Open.Research
