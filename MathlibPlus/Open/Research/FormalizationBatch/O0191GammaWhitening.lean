import MathlibPlus.Open.Research.FormalizationBatchGammaJump
import MathlibPlus.Open.Research.FormalizationBatch.O0191PolarBoundary

namespace MathlibPlus.Open.Research.FormalizationBatch.O0191GammaWhitening

noncomputable section

open scoped BigOperators
open Set
open MeasureTheory
open MathlibPlus.Open.ResearchBatchMisc
open MathlibPlus.Open.Research.FormalizationBatch
open MathlibPlus.Open.Research.FormalizationBatchGammaJump

/-- The radius associated with the finite cutoff `c`. -/
def cutoffRadius (c : ℕ) : ℝ :=
  Real.log (c : ℝ) / 2

/-- The localized real Hilbert carrier `L²(-R,R)`. -/
abbrev CutoffHilbert (c : ℕ) : Type :=
  MeasureTheory.Lp ℝ 2
    ((volume : Measure ℝ).restrict
      (Set.Ioo (-cutoffRadius c) (cutoffRadius c)))

/-- The zero-extended representative of a localized `L²` vector. -/
def cutoffRepresentative (c : ℕ) (f : CutoffHilbert c) : ℝ → ℝ :=
  Set.indicator (Set.Ioo (-cutoffRadius c) (cutoffRadius c))
    (↑f : ℝ → ℝ)

/-- The exact strict common cutoff `2 ≤ n < c`. -/
noncomputable def finiteCutoffIndices (c : ℕ) : Finset ℕ :=
  Finset.Icc 2 (c - 1)

/-- The arithmetic complement from the exact finite-cutoff split. -/
noncomputable def cutoffArithmeticBlock (c : ℕ) (f : ℝ → ℝ) : ℝ :=
  -poleForm f +
      2 * ∑ n ∈ finiteCutoffIndices c,
        primeJumpCoefficient n *
          autocorrelation (f := f) (Real.log (n : ℝ)) +
    (Real.log Real.pi - (Complex.digamma (1 / 4 : ℂ)).re) *
      realL2Squared (f := f)

/-- The gamma-jump quadratic form on the localized carrier. -/
noncomputable def cutoffGammaForm (c : ℕ) (f : CutoffHilbert c) : ℝ :=
  gammaJumpMetric (cutoffRepresentative c f)

/-- The arithmetic quadratic form on the localized carrier. -/
noncomputable def cutoffArithmeticForm (c : ℕ) (f : CutoffHilbert c) : ℝ :=
  cutoffArithmeticBlock c (cutoffRepresentative c f)

/-- The exact finite-cutoff Weil form `Q_c = G_c - A_c`. -/
noncomputable def cutoffWeilForm (c : ℕ) (f : CutoffHilbert c) : ℝ :=
  cutoffGammaForm c f - cutoffArithmeticForm c f

/-- The proper form domain of the gamma-jump form. -/
def cutoffFormDomain (c : ℕ) : Set (CutoffHilbert c) :=
  {f |
    IntegrableOn
      (fun ell : ℝ =>
        gammaJumpWeight ell *
          jumpEnergy (f := cutoffRepresentative c f) ell)
      (Set.Ioi (0 : ℝ)) volume}

/-- A bounded operator is self-adjoint on the localized real Hilbert space. -/
def operatorSelfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) : Prop :=
  ∀ x y : H, inner ℝ (A x) y = inner ℝ x (A y)

/-- Positivity of a bounded self-adjoint operator. -/
def operatorPositive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H →L[ℝ] H) : Prop :=
  ∀ x : H, 0 ≤ inner ℝ (A x) x

/-- Linearity of a possibly unbounded graph on its displayed domain. -/
def graphLinear
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H → H) (D : Set H) : Prop :=
  (0 : H) ∈ D ∧ G 0 = 0 ∧
    (∀ (x y : H), x ∈ D → y ∈ D →
      x + y ∈ D ∧ G (x + y) = G x + G y) ∧
      (∀ (a : ℝ) (x : H), x ∈ D →
        a • x ∈ D ∧ G (a • x) = a • G x)

/-- The graph-adjoint characterization of a self-adjoint operator. -/
def graphSelfAdjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H → H) (D : Set H) : Prop :=
  ∀ (y z : H),
    (∃ hy : y ∈ D, G y = z) ↔
      ∀ (x : H) (hx : x ∈ D),
        inner ℝ (G x) y = inner ℝ x z

/-- Positivity of the graph operator on its form domain. -/
def graphPositive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H → H) (D : Set H) : Prop :=
  ∀ (x : H), x ∈ D → 0 ≤ inner ℝ (G x) x

/-- The upper unit order `T ≤ I`, expressed by quadratic forms. -/
def upperUnitOrder
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) : Prop :=
  ∀ x : H, inner ℝ (T x) x ≤ inner ℝ x x

/-- The lower unit order `-I ≤ T`, expressed by quadratic forms. -/
def lowerUnitOrder
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) : Prop :=
  ∀ x : H, -inner ℝ x x ≤ inner ℝ (T x) x

/-- Positivity of the exact Weil form on a displayed domain. -/
def cutoffWeilPositive (c : ℕ) (D : Set (CutoffHilbert c)) : Prop :=
  ∀ (f : CutoffHilbert c), f ∈ D → 0 ≤ cutoffWeilForm c f

/-- The bounded form `I-T`. -/
noncomputable def identityMinus
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : H →L[ℝ] H) : H →L[ℝ] H :=
  ContinuousLinearMap.id ℝ H - T

/-- The finite arithmetic form is represented by a bounded self-adjoint operator. -/
def operatorRepresentsArithmetic (c : ℕ)
    (A : CutoffHilbert c →L[ℝ] CutoffHilbert c) : Prop :=
  ∀ f : CutoffHilbert c,
    inner ℝ (A f) f = cutoffArithmeticForm c f

/-- Exact gamma square-root data, with the unbounded square root kept on its
proper form domain and only its inverse square root required everywhere. -/
def gammaWhiteningData (c : ℕ)
    (A Ginvhalf T : CutoffHilbert c →L[ℝ] CutoffHilbert c)
    (Ghalf : CutoffHilbert c → CutoffHilbert c)
    (D : Set (CutoffHilbert c)) : Prop :=
  D = cutoffFormDomain c ∧
    Dense D ∧
      graphLinear Ghalf D ∧
        graphSelfAdjoint Ghalf D ∧
          graphPositive Ghalf D ∧
            operatorSelfAdjoint A ∧
              operatorRepresentsArithmetic c A ∧
                operatorSelfAdjoint Ginvhalf ∧
                  operatorPositive Ginvhalf ∧
                    operatorSelfAdjoint T ∧
                      (∃ δ : ℝ, 0 < δ ∧
                  ∀ f : CutoffHilbert c, f ∈ D →
                    δ * ‖f‖ ^ 2 ≤ cutoffGammaForm c f) ∧
                  (∀ (f : CutoffHilbert c) (hf : f ∈ D),
                    inner ℝ (Ghalf f) (Ghalf f) = cutoffGammaForm c f) ∧
                    (∀ f : CutoffHilbert c,
                      Ginvhalf f ∈ D ∧ Ghalf (Ginvhalf f) = f) ∧
                      (∀ (f : CutoffHilbert c) (hf : f ∈ D),
                        Ginvhalf (Ghalf f) = f) ∧
                        (∀ f : CutoffHilbert c,
                          T f = Ginvhalf (A (Ginvhalf f))) ∧
                          (∀ (f : CutoffHilbert c) (hf : f ∈ D),
                            cutoffWeilForm c f =
                              inner ℝ
                                (identityMinus T (Ghalf f))
                                (Ghalf f)) ∧
                            (upperUnitOrder T ↔
                              cutoffWeilPositive c D) ∧
                              (‖T‖ ≤ 1 ↔
                                upperUnitOrder T ∧ lowerUnitOrder T)

/-- Claim 14954: exact gamma whitening, form-domain congruence, and the two
order consequences at every finite cutoff. -/
def claim_14954 : Prop :=
  ∀ c : ℕ, 2 ≤ c →
    ∃ (A Ginvhalf T : CutoffHilbert c →L[ℝ] CutoffHilbert c)
      (Ghalf : CutoffHilbert c → CutoffHilbert c)
      (D : Set (CutoffHilbert c)),
      gammaWhiteningData c A Ginvhalf T Ghalf D

/-- The fixed cutoff radius and frequency of the certified witness. -/
def witnessRadius : ℝ :=
  Real.log (1000 : ℝ) / 2

def witnessFrequency : ℝ :=
  (2827 : ℝ) / 200

/-- The discontinuous cosine witness on the exact closed cutoff interval. -/
def cosineWitness : ℝ → ℝ :=
  Set.indicator (Set.Icc (-witnessRadius) witnessRadius)
    (fun x => Real.cos (witnessFrequency * x))

/-- The exact autocorrelation formula for the cosine witness. -/
def cosineAutocorrelationFormula (ell : ℝ) : ℝ :=
  (2 * witnessRadius - ell) / 2 *
      Real.cos (witnessFrequency * ell) +
    Real.sin (2 * witnessFrequency * witnessRadius -
        witnessFrequency * ell) /
      (2 * witnessFrequency)

/-- The exact squared norm formula for the cosine witness. -/
def cosineNormFormula : ℝ :=
  witnessRadius +
    Real.sin (2 * witnessFrequency * witnessRadius) /
      (2 * witnessFrequency)

/-- Claim 14955: the exact cosine formulas, strict arithmetic bounds, and
separate negative directions for the arithmetic and whitened operators. -/
def claim_14955 : Prop :=
  (∀ ell : ℝ, ell ∈ Set.Icc 0 (2 * witnessRadius) →
    autocorrelation (f := cosineWitness) ell =
      cosineAutocorrelationFormula ell) ∧
    realL2Squared (f := cosineWitness) = cosineNormFormula ∧
      cutoffArithmeticBlock 1000 cosineWitness < -2 ∧
        cutoffArithmeticBlock 1000 cosineWitness /
              realL2Squared (f := cosineWitness) < -(7 : ℝ) / 10 ∧
            ∃ (A Ginvhalf T :
                CutoffHilbert 1000 →L[ℝ] CutoffHilbert 1000)
              (Ghalf : CutoffHilbert 1000 → CutoffHilbert 1000)
              (D : Set (CutoffHilbert 1000)),
              gammaWhiteningData 1000 A Ginvhalf T Ghalf D ∧
                (∃ vA : CutoffHilbert 1000,
                  inner ℝ (A vA) vA < 0) ∧
                  (∃ vT : CutoffHilbert 1000,
                    inner ℝ (T vT) vT < 0)

/-- The smooth even test functions in the same cutoff section. -/
def smoothEvenCutoff (f : ℝ → ℝ) : Prop :=
  ContDiff ℝ ⊤ f ∧
    Even f ∧
      HasCompactSupport f ∧
        Function.support f ⊆ Set.Icc (-witnessRadius) witnessRadius

/-- Claim 14956: smooth even compactly supported witnesses approximate the
fixed cosine witness while retaining strict negativity of the same block. -/
def claim_14956 : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ g : ℝ → ℝ,
      smoothEvenCutoff g ∧
        realL2Squared (f := fun x => g x - cosineWitness x) < ε ∧
          cutoffArithmeticBlock 1000 g < 0

end

end MathlibPlus.Open.Research.FormalizationBatch.O0191GammaWhitening
