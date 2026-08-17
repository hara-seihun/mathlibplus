import MathlibPlus.Open.Research.Batch13518_13519

namespace MathlibPlus.Open.Research.GramExactBatch

noncomputable section

abbrev EvalIndex := QIndex
abbrev EvalMatrix := QMatrix
abbrev EvalFunction := ℝ → ℝ → ℝ

/-- The real factor in the real/complex Segre rays. -/
def realSegreFactor (U : ℝ) : Fin 2 → ℂ :=
  ![Complex.exp ((U : ℂ) / 2), Complex.exp (-((U : ℂ) / 2))]

/-- The complex phase factor in the real/complex Segre rays. -/
def complexSegreFactor (Φ : ℝ) : Fin 2 → ℂ :=
  ![Complex.exp (Complex.I * ((Φ : ℂ) / 2)),
    Complex.exp (-Complex.I * ((Φ : ℂ) / 2))]

def segreRay (U Φ : ℝ) : EvalIndex → ℂ :=
  fun p => realSegreFactor U p.1 * complexSegreFactor Φ p.2

def segreEvaluation (A : EvalMatrix) (U Φ : ℝ) : ℝ :=
  (∑ p : EvalIndex, star (segreRay U Φ p) * (A.mulVec (segreRay U Φ)) p).re

def evaluationFunction (A : EvalMatrix) : EvalFunction :=
  fun U Φ => segreEvaluation A U Φ

def evaluationNull (A : EvalMatrix) : Prop :=
  ∀ U Φ : ℝ, segreEvaluation A U Φ = 0

def nullBasis (k : Fin 7) : EvalMatrix :=
  ![tensor pauliY pauliI, tensor pauliY pauliX, tensor pauliY pauliY,
    tensor pauliY pauliZ, tensor pauliI pauliZ, tensor pauliX pauliZ,
    tensor pauliZ pauliZ] k

def nullCombination (c : Fin 7 → ℝ) : EvalMatrix :=
  ∑ k : Fin 7, ((c k : ℂ) • nullBasis k)

/-- The nine-dimensional visible evaluation space and the exact real null
kernel of the Hermitian matrices on the specified Segre rays. -/
def claim13496 : Prop :=
  (∃ b : Fin 9 → EvalFunction,
    LinearIndependent ℝ b ∧
      (∀ i : Fin 9, ∃ A : EvalMatrix,
        hermitian A ∧ b i = evaluationFunction A) ∧
      (∀ A : EvalMatrix, hermitian A →
        ∃ c : Fin 9 → ℝ,
          evaluationFunction A = ∑ i : Fin 9, (c i) • b i)) ∧
  (∀ k : Fin 7, hermitian (nullBasis k) ∧ evaluationNull (nullBasis k)) ∧
  LinearIndependent ℝ nullBasis ∧
  (∀ A : EvalMatrix, hermitian A →
    (evaluationNull A ↔ ∃ c : Fin 7 → ℝ, A = nullCombination c)) ∧
  (∀ x g : ℝ, ∀ A : EvalMatrix, hermitian A →
    (∀ U Φ : ℝ,
      evaluationFunction A U Φ = evaluationFunction (visibleGram x g) U Φ) →
      ∃ N : EvalMatrix,
        A = visibleGram x g + N ∧ hermitian N ∧ evaluationNull N)

def bellFrameQ : EvalMatrix :=
  let s : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  fun p q =>
    if q = (0, 0) then
      if p = (0, 0) ∨ p = (1, 1) then s else 0
    else if q = (0, 1) then
      if p = (0, 1) ∨ p = (1, 0) then s else 0
    else if q = (1, 0) then
      if p = (0, 0) then s else if p = (1, 1) then -s else 0
    else
      if p = (0, 1) then s else if p = (1, 0) then -s else 0

def bellConjugateQ (A : EvalMatrix) : EvalMatrix :=
  bellFrameQ.conjTranspose * A * bellFrameQ

def bellBlockQ (x g t : ℝ) : EvalMatrix :=
  fun p q =>
    if p.1 = 0 ∧ q.1 = 0 then
      (((x / 4 : ℝ) : ℂ) • pauliI +
        (((t - g / 4 : ℝ) : ℂ) • pauliY)) p.2 q.2
    else if p.1 = 1 ∧ q.1 = 1 then
      ((((4 + x) / 4 : ℝ) : ℂ) • pauliI +
        (((-t - g / 4 : ℝ) : ℂ) • pauliY)) p.2 q.2
    else 0

def bellPptBlockQ (x g t : ℝ) : EvalMatrix :=
  fun p q =>
    if p.1 = 0 ∧ q.1 = 0 then
      (((x / 4 : ℝ) : ℂ) • pauliI +
        (((t + g / 4 : ℝ) : ℂ) • pauliY)) p.2 q.2
    else if p.1 = 1 ∧ q.1 = 1 then
      ((((4 + x) / 4 : ℝ) : ℂ) • pauliI +
        (((-t + g / 4 : ℝ) : ℂ) • pauliY)) p.2 q.2
    else 0

/-- The direct and compact-partial-transpose Bell blocks and their exact
positive-semidefinite intervals. -/
def claim13498 : Prop :=
  ∀ x g t : ℝ,
    bellConjugateQ (qFamily x g t) = bellBlockQ x g t ∧
      bellConjugateQ (partialTranspose (qFamily x g t)) = bellPptBlockQ x g t ∧
      (positiveSemidefinite (qFamily x g t) ↔
        |t - g / 4| ≤ x / 4 ∧ |t + g / 4| ≤ (4 + x) / 4) ∧
      (positiveSemidefinite (partialTranspose (qFamily x g t)) ↔
        |t + g / 4| ≤ x / 4 ∧ |t - g / 4| ≤ (4 + x) / 4)

def qEigenvalue (A : EvalMatrix) (z : ℂ) : Prop :=
  ∃ v : EvalIndex → ℂ, v ≠ 0 ∧ A.mulVec v = fun i => z * v i

/-- The common margin formula, unique zero-gauge maximizer, and the common
four-value spectrum at the maximizing gauge. -/
def claim13500 : Prop :=
  ∀ x g : ℝ,
    (∀ t : ℝ,
      commonMargin (qFamily x g t) = (x - |g|) / 4 - |t|) ∧
    (∀ t : ℝ,
      commonMargin (qFamily x g t) ≤ commonMargin (qFamily x g 0) ∧
        (commonMargin (qFamily x g t) = commonMargin (qFamily x g 0) ↔ t = 0)) ∧
    commonMargin (qFamily x g 0) = (x - |g|) / 4 ∧
    (∀ z : ℂ,
      qEigenvalue (qFamily x g 0) z ↔
        z = (((x + |g|) / 4 : ℝ) : ℂ) ∨
        z = (((x - |g|) / 4 : ℝ) : ℂ) ∨
        z = ((((4 + x + |g|) / 4 : ℝ)) : ℂ) ∨
        z = ((((4 + x - |g|) / 4 : ℝ)) : ℂ)) ∧
    (∀ z : ℂ,
      qEigenvalue (partialTranspose (qFamily x g 0)) z ↔
        z = (((x + |g|) / 4 : ℝ) : ℂ) ∨
        z = (((x - |g|) / 4 : ℝ) : ℂ) ∨
        z = ((((4 + x + |g|) / 4 : ℝ)) : ℂ) ∨
        z = ((((4 + x - |g|) / 4 : ℝ)) : ℂ))

def physicalSplitPhase (lam : ℝ) : Set ℝ :=
  {x : ℝ | ∃ g : ℝ,
    physicalPhase lam x g ∧ splitLocalCompletion x g ∧ separableCompletion x g}

/-- The exact physical split/compact separable phase set, its three shell
values, and the whole positive complementary interval with no completion. -/
def claim13502 : Prop :=
  (∀ lam : ℝ,
    physicalSplitPhase lam =
      ({0} : Set ℝ) ∪ Set.Icc (phaseThreshold lam) 1) ∧
  phaseThreshold (1 / 2 : ℝ) = 18 / 19 ∧
  (∀ lam : ℝ, lam ^ 2 = 1 / 3 →
    phaseThreshold lam = 24 / 25) ∧
  (∀ lam : ℝ, lam ^ 2 = 1 / 2 →
    phaseThreshold lam = 36 / 37) ∧
  (∀ lam : ℝ, 0 < lam →
    Set.Nonempty {x : ℝ | 0 < x ∧ x < phaseThreshold lam} ∧
      (∀ x : ℝ, 0 < x → x < phaseThreshold lam →
        ∀ g : ℝ, physicalPhase lam x g →
          ¬ pptCompletion x g ∧
            ¬ splitLocalCompletion x g ∧
            ¬ separableCompletion x g))

end
end MathlibPlus.Open.Research.GramExactBatch
