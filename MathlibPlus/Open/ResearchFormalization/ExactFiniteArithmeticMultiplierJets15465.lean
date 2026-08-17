import Mathlib
import MathlibPlus.Analysis.CompletedGammaFactor

open MeasureTheory
open scoped BigOperators Topology

namespace MathlibPlus.Open.ResearchFormalization.ExactFiniteArithmeticMultiplierJets15465

noncomputable section

/-- The two consecutive positive arithmetic cells, retained as the actual
source carrier rather than merely as a subset of a larger interval. -/
def arithmeticCellUnion (c δ : ℝ) : Set ℝ :=
  Set.Ioo c (c + δ) ∪ Set.Ioo (c + δ) (c + 2 * δ)

def twoConsecutiveArithmeticCells (I : Set ℝ) (c δ : ℝ) : Prop :=
  0 < δ ∧
    I.Nonempty ∧
      IsConnected I ∧
        I ⊆ Set.Ioi 0 ∧
          arithmeticCellUnion c δ ⊆ I

/-- The complexification of the center-flat zero-mean source space, with
support tied to the two displayed cells and their reflected carrier. -/
def twoCellComplexSource (c δ : ℝ) (q : ℝ → ℂ) : Prop :=
  ContDiff ℝ ⊤ q ∧
    Function.Even q ∧
      HasCompactSupport q ∧
        Function.support q ⊆
          arithmeticCellUnion c δ ∪
            Set.image (fun x : ℝ => -x) (arithmeticCellUnion c δ) ∧
          (∫ x : ℝ, q x) = 0

noncomputable def complexPoissonFourierTransform
    (q : ℝ → ℂ) (ξ : ℝ) : ℂ :=
  ∫ t : ℝ,
    q t * Complex.exp (-Complex.I * (ξ : ℂ) * (t : ℂ))

noncomputable def complexPoissonKernel
    (q : ℝ → ℂ) (x : ℝ) : ℂ :=
  -(q 0 / 2) * (Real.exp (x / 2) : ℂ) +
    (Real.exp (-x / 2) : ℂ) *
      ∑' n : {n : ℕ // 1 ≤ n},
        complexPoissonFourierTransform q
          ((n.1 : ℝ) * Real.exp (-x))

noncomputable def complexEvenPoissonKernel
    (q : ℝ → ℂ) (x : ℝ) : ℂ :=
  (complexPoissonKernel q x + complexPoissonKernel q (-x)) / 2

noncomputable def complexFullPoissonCarrier
    (q : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t : ℝ,
    complexEvenPoissonKernel q t *
      Complex.exp (Complex.I * z * (t : ℂ))

noncomputable def complexLiteralPoissonCarrier
    (q : ℝ → ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Set.Icc (-L) L,
    complexEvenPoissonKernel q t *
      Complex.exp (Complex.I * z * (t : ℂ))

noncomputable def complexPoissonDefect
    (q : ℝ → ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  complexLiteralPoissonCarrier q L z - complexFullPoissonCarrier q z

noncomputable def complexSourceMellin (q : ℝ → ℂ) (s : ℂ) : ℂ :=
  mellin q s

def centeredCoordinate (z : ℂ) : ℂ :=
  (1 / 2 : ℂ) + Complex.I * z

noncomputable def centeredMultiplier
    (q : ℝ → ℂ) (z : ℂ) : ℂ :=
  let s := centeredCoordinate z
  (1 / 2 : ℂ) *
    (complexSourceMellin q s /
        MathlibPlus.Analysis.CompletedGammaFactor.completedGammaFactor s +
      complexSourceMellin q (1 - s) /
        MathlibPlus.Analysis.CompletedGammaFactor.completedGammaFactor (1 - s))

noncomputable def arithmeticMultiplier
    (q : ℝ → ℂ) (s : ℂ) : ℂ :=
  centeredMultiplier q (-Complex.I * (s - (1 / 2 : ℂ)))

def centeredStripCompact (K : Set ℂ) : Prop :=
  IsCompact K ∧
    IsConnected Kᶜ ∧
      (∀ z : ℂ, z ∈ K → -z ∈ K) ∧
        (∀ z : ℂ, z ∈ K → |z.im| < 1 / 2)

def rightHalfPlaneCompact (K : Set ℂ) : Prop :=
  IsCompact K ∧
    IsConnected Kᶜ ∧
      (∀ z : ℂ, z ∈ K → 1 < z.re)

def centeredAnalyticEvenTarget
    (K : Set ℂ) (f : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ f K ∧
    ∀ z : ℂ, z ∈ K → f (-z) = f z

def finiteCMApprox
    (f g : ℂ → ℂ) (K : Set ℂ) (m : ℕ) (ε : ℝ) : Prop :=
  ∀ k : ℕ, k ≤ m → ∀ z : ℂ, z ∈ K →
    ‖iteratedDeriv k f z - iteratedDeriv k g z‖ < ε

/-- Claim 15465: exact finite exterior arithmetic jets coexist with independent
finite-order approximation of the Poisson defect, centered quotient, and
arithmetic quotient on their prescribed compact carriers. -/
def exactFiniteArithmeticMultiplierJets_claim15465 : Prop :=
  ∀ (L c δ : ℝ) (I : Set ℝ),
    twoConsecutiveArithmeticCells I c δ →
      I ⊆ Set.Ioo 0 (Real.exp L) →
        ∀ (K_D K_E Kplus : Set ℂ),
          centeredStripCompact K_D →
            centeredStripCompact K_E →
              rightHalfPlaneCompact Kplus →
                ∀ (m N : ℕ)
                  (w : Fin N → ℂ)
                  (orders : Fin N → ℕ)
                  (jets : (j : Fin N) →
                    Fin (orders j + 1) → ℂ),
                  Function.Injective w →
                    (∀ j : Fin N, 1 < (w j).re) →
                      ∀ (f_D f_E fplus : ℂ → ℂ),
                        centeredAnalyticEvenTarget K_D f_D →
                          centeredAnalyticEvenTarget K_E f_E →
                            AnalyticOnNhd ℂ fplus Kplus →
                              ∀ ε : ℝ, 0 < ε →
                                ∃ q : ℝ → ℂ,
                                  twoCellComplexSource c δ q ∧
                                    finiteCMApprox
                                      (complexPoissonDefect q L)
                                      f_D K_D m ε ∧
                                    finiteCMApprox
                                      (centeredMultiplier q)
                                      f_E K_E m ε ∧
                                    finiteCMApprox
                                      (arithmeticMultiplier q)
                                      fplus Kplus m ε ∧
                                    (∀ j : Fin N,
                                      ∀ k : Fin (orders j + 1),
                                      iteratedDeriv (k : ℕ)
                                        (arithmeticMultiplier q)
                                        (w j) = jets j k)

end

end MathlibPlus.Open.ResearchFormalization.ExactFiniteArithmeticMultiplierJets15465
