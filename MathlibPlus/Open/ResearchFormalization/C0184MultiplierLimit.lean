import Mathlib
import MathlibPlus.Analysis.ReciprocalXi
import MathlibPlus.Open.ResearchFormalization.C0184GrowingEulerMoments

open Filter MeasureTheory Set Topology Asymptotics
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.C0184MultiplierLimit

noncomputable section

/-- The actual C-0180 Xi carrier in the transform variable. -/
noncomputable def xiTransformCarrier (z : ℂ) : ℂ :=
  MathlibPlus.Analysis.ReciprocalXi.xi
    ((1 / 2 : ℂ) + Complex.I * z)

/-- Supremum of a complex carrier over the closed horizontal substrip of
height `Y`, retaining the entire real direction. -/
noncomputable def closedSubstripSup
    (Y : ℝ) (F : ℂ → ℂ) : ℝ :=
  sSup ((fun z : ℂ => ‖F z‖) '' {z : ℂ | |z.im| ≤ Y})

/-- Claim 2737: the actual Xi multiplier has the stated fixed-substrip
power growth. -/
def fixedSubstripMultiplierEstimate_claim2737
    (k : ℕ) (α : ℝ) : Prop :=
  1 ≤ k ∧ 0 < α ∧
    ∀ Y : ℝ, 0 ≤ Y → Y < (1 / 2 : ℝ) →
      ∃ C_Y : ℝ, 0 < C_Y ∧
        ∀ j : ℕ,
          closedSubstripSup Y
              (fun z : ℂ =>
                z ^ (2 * j) * xiTransformCarrier z *
                  Complex.exp (-(α : ℂ) * z ^ (2 * k))) ≤
            Real.rpow (C_Y * (j + 1 : ℝ))
              ((j : ℝ) / (k : ℝ) + C_Y)

/-- The Gaussian carriers fixed in C-0180. -/
def hProfile (x : ℝ) : ℝ :=
  x ^ 2 * (2 * Real.pi * x ^ 2 - 3) * Real.exp (-Real.pi * x ^ 2)

def gProfile (x : ℝ) : ℝ := Real.exp (-Real.pi * x ^ 2)

def r0Profile (x : ℝ) : ℝ :=
  (1 - 2 * Real.pi * x ^ 2) * Real.exp (-Real.pi * x ^ 2)

def superheatOperator (α : ℝ) (k : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => ∑' n : ℕ,
    ((-α) ^ n / (Nat.factorial n : ℝ)) *
      ((C0184.mathcalZ^[k * n]) f) x

def baselineCarrier (α : ℝ) (k : ℕ) : ℝ → ℝ :=
  superheatOperator α k hProfile

def carrierScale (α : ℝ) (k : ℕ) : ℝ :=
  Real.exp (α * (-1 / 4 : ℝ) ^ k)

def integralCarrier (α : ℝ) (k : ℕ) : ℝ → ℝ :=
  carrierScale α k • superheatOperator α k gProfile

def centerCarrier (α : ℝ) (k : ℕ) : ℝ → ℝ :=
  carrierScale α k • superheatOperator α k r0Profile

def logGevreyBaseCutoff (k : ℕ) (θ : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) θ ∧
    (∀ t : ℝ, t ≤ 1 / 2 → θ t = 1) ∧
    (∀ t : ℝ, 1 ≤ t → θ t = 0) ∧
    (∀ n : ℕ, iteratedDeriv n θ 1 = 0) ∧
    (∃ C A : ℝ, 0 < C ∧ 0 < A ∧
      ∀ n : ℕ, ∀ t : ℝ,
        ‖iteratedDeriv n θ t‖ ≤
          C * A ^ n *
            Real.rpow (Nat.factorial n : ℝ)
              (1 + 1 / (2 * (k : ℝ))))

def logGevreyCutoff (θ : ℝ → ℝ) (lam : ℝ) : ℝ → ℝ :=
  fun x => if |x| ≤ 1 then 1 else θ (Real.log |x| / Real.log lam)

def profiledCarrier
    (k : ℕ) (α : ℝ) (d : ℝ → ℕ) (a : ℝ → ℕ → ℝ) (L : ℝ) : ℝ → ℝ :=
  C0184.growingProfileCarrier k (baselineCarrier α k) d a L

def profiledSource
    (k : ℕ) (α : ℝ) (d : ℝ → ℕ) (a : ℝ → ℕ → ℝ)
    (θ : ℝ → ℝ) (b : ℝ → ℝ) (L : ℝ) : ℝ → ℝ :=
  (logGevreyCutoff θ (Real.exp L)) *
    (profiledCarrier k α d a L +
      Real.exp (-2 * L) • centerCarrier α k - b L • integralCarrier α k)

/-- The exact logarithmic arithmetic-sum kernel used by the C-0180
finite arithmetic transform. -/
def arithmeticLogKernel (q : ℝ → ℝ) (y : ℝ) : ℝ :=
  Real.exp (y / 2) *
    ∑' n : ℕ,
      if 1 ≤ n then q ((n : ℝ) * Real.exp y) else 0

noncomputable def uncutArithmeticTransform
    (q : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ y : ℝ,
    (arithmeticLogKernel q y : ℂ) *
      Complex.cos (z * (y : ℂ))

noncomputable def finiteArithmeticTransform
    (q : ℝ → ℝ) (L : ℝ) (z : ℂ) : ℂ :=
  ∫ y in (-L : ℝ)..L,
    (arithmeticLogKernel q y : ℂ) *
      Complex.cos (z * (y : ℂ))

/-- The finite-versus-uncut error is tied to the two explicit arithmetic
transforms, not supplied as an unrelated callback. -/
def finiteSumIntegralError
    (q : ℝ → ℝ) (L : ℝ) (z : ℂ) : ℂ :=
  finiteArithmeticTransform q L z - uncutArithmeticTransform q z

def coefficientRootBound
    (d : ℝ → ℕ) (a : ℝ → ℕ → ℝ) (B : ℝ → ℝ) : Prop :=
  ∀ L : ℝ,
    1 ≤ B L ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ d L → |a L j| ≤ B L ^ j

def phaseCapacityConditions
    (k : ℕ) (d : ℝ → ℕ) (B : ℝ → ℝ) : Prop :=
  1 ≤ k ∧
    Tendsto
      (fun L : ℝ => B L ^ k * (d L : ℝ) / L)
      atTop (𝓝 0) ∧
    IsLittleO atTop
      (fun L : ℝ => (d L : ℝ) * Real.log (B L))
      (fun L : ℝ => L)

/-- Claim 2738: the actual profiled logarithmic arithmetic transform has the
whole-strip Xi limit, and its explicit finite transform remains convergent
when its finite/uncut error is enlarged by `exp(o(L))`. -/
def wholeStripProfiledSuperheatLimit_claim2738
    (k : ℕ) (α : ℝ) (d : ℝ → ℕ) (a : ℝ → ℕ → ℝ)
    (B : ℝ → ℝ) : Prop :=
  1 ≤ k ∧ 0 < α ∧
    coefficientRootBound d a B ∧
    phaseCapacityConditions k d B ∧
    ∃ θ b : ℝ → ℝ,
      logGevreyBaseCutoff k θ ∧
      (∀ L : ℝ, 0 < L →
        C0184.normalizedIntegral (profiledSource k α d a θ b L) = 0) ∧
      (∀ Y : ℝ, 0 ≤ Y → Y < (1 / 2 : ℝ) →
        Tendsto
          (fun L : ℝ =>
            closedSubstripSup Y
              (fun z : ℂ =>
                uncutArithmeticTransform
                  (profiledSource k α d a θ b L) z -
                  xiTransformCarrier z *
                    Complex.exp (-(α : ℂ) * z ^ (2 * k)) /
                      (2 * (Real.pi : ℂ))))
          atTop (𝓝 0)) ∧
      (∀ Y : ℝ, 0 ≤ Y → Y < (1 / 2 : ℝ) →
        ∃ η : ℝ → ℝ,
          IsLittleO atTop η (fun L : ℝ => L) ∧
          (∀ᶠ L : ℝ in atTop, 0 ≤ η L) ∧
          Tendsto
            (fun L : ℝ =>
              closedSubstripSup Y
                (fun z : ℂ =>
                  finiteSumIntegralError
                    (profiledSource k α d a θ b L) L z))
            atTop (𝓝 0) ∧
          Tendsto
            (fun L : ℝ =>
              Real.exp (η L) *
                closedSubstripSup Y
                  (fun z : ℂ =>
                    finiteSumIntegralError
                      (profiledSource k α d a θ b L) L z))
            atTop (𝓝 0))

end

end MathlibPlus.Open.ResearchFormalization.C0184MultiplierLimit
