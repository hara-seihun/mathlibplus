import Mathlib

noncomputable section

namespace MathlibPlus.Open.Analysis

/-- The paired age kernel from the admitted paired-density statement. -/
def pairedP (a b u v : ℝ) : ℝ :=
  Real.cosh (a * u) * Real.cosh (b * v) +
    Real.cosh (a * v) * Real.cosh (b * u)

/-- The paired Green eigenvalue. -/
def pairedDelta (a b : ℝ) : ℝ :=
  (a ^ 2 - (1 / 4 : ℝ)) * (b ^ 2 - (1 / 4 : ℝ))

/-- The admitted rate generator `b ∂_a - a ∂_b`, applied to the paired kernel. -/
def pairedRateDerivative (a b u v : ℝ) : ℝ :=
  b * deriv (fun x => pairedP x b u v) a -
    a * deriv (fun y => pairedP a y u v) b

/-- The removable confluent value of the paired density on the diagonal. -/
def pairedConfluentDensity (a u v : ℝ) : ℝ :=
  (u * Real.sinh (a * u) * Real.cosh (a * v) +
      v * Real.sinh (a * v) * Real.cosh (a * u)) / (4 * a) +
    (2 * u * v * Real.sinh (a * u) * Real.sinh (a * v) -
        (u ^ 2 + v ^ 2) * Real.cosh (a * u) * Real.cosh (a * v)) / 4

/-- The complete paired Loewner density, including its confluent value. -/
def pairedKhat (a b u v : ℝ) : ℝ :=
  if a = b then
    pairedConfluentDensity a u v
  else
    pairedRateDerivative a b u v / (2 * (b ^ 2 - a ^ 2))

/-- The one-dimensional Green operator `∂² - 1/4`. -/
def greenL (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  deriv (deriv f) u - (1 / 4 : ℝ) * f u

/-- Iteration of the one-dimensional Green operator. -/
def greenLIterate : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | Nat.succ n, f => greenLIterate n (fun x => greenL f x)
termination_by n => n

/-- The paired source operator `A = L_u L_v`. -/
def pairedA (F : ℝ → ℝ → ℝ) (u v : ℝ) : ℝ :=
  greenL (fun x => greenL (fun y => F x y) v) u

/-- Iteration of the paired source operator. -/
def pairedAIterate : ℕ → (ℝ → ℝ → ℝ) → ℝ → ℝ → ℝ
  | 0, F => F
  | Nat.succ n, F => pairedAIterate n (fun u v => pairedA F u v)
termination_by n => n

/-- The depth-`m` paired source kernel. -/
def pairedDepthKernel (a b : ℝ) (m : ℕ) (u v : ℝ) : ℝ :=
  pairedAIterate m (fun x y => pairedKhat a b x y) u v

/-- The positive-half-line (Volterra) convolution. -/
def positiveHalfLineConvolution (f g : ℝ → ℝ) (u : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..u, f (u - s) * g s

/-- The admitted kernels `f_r(u) = sinh(r u)/r`. -/
def sinhKernel (r u : ℝ) : ℝ :=
  Real.sinh (r * u) / r

/-- The positive-half-line convolution `h_{a,b} = f_a * f_b`. -/
def pairedBoundaryConvolution (a b u : ℝ) : ℝ :=
  positiveHalfLineConvolution (sinhKernel a) (sinhKernel b) u

/-- Every finite paired bulk depth has the admitted sign change and interior wedge. -/
def everyFinitePairedBulkChangesSign : Prop :=
  ∀ a b : ℝ,
    (1 / 2 : ℝ) < a →
    (1 / 2 : ℝ) < b →
    ∀ m : ℕ,
      1 ≤ m →
      let G : ℝ → ℝ → ℝ := fun u v => pairedDepthKernel a b m u v
      0 < G 0 0 ∧
        G 0 0 = 2 * (m : ℝ) * a * b * pairedDelta a b ^ (m - 1) ∧
        (∃ U : ℝ,
          0 < U ∧
            (∀ u : ℝ, U < u → G u 0 < 0) ∧
            (∀ u : ℝ,
              U < u →
                ∃ ε : ℝ,
                  0 < ε ∧
                    ∀ x v : ℝ,
                      |x - u| < ε → 0 < v → v < ε → G x v < 0)) ∧
        (∃ x₁ y₁ x₂ y₂ : ℝ,
          G x₁ y₁ < 0 ∧ 0 < G x₂ y₂)

/-- The explicit confluent threshold and its sufficient large-`t` condition. -/
def explicitConfluentNegativeThreshold : Prop :=
  ∀ a : ℝ,
    (1 / 2 : ℝ) < a →
    ∀ m : ℕ,
      1 ≤ m →
      ∀ t : ℝ,
        0 < t →
        let α : ℝ := a ^ 2 - (1 / 4 : ℝ)
        let value : ℝ := pairedDepthKernel a a m (t / a) 0
        (α ^ 2 * t * (t - Real.tanh t) > 8 * (m : ℝ) * a ^ 4 →
            value < 0) ∧
          (t > 1 + Real.sqrt (8 * (m : ℝ)) * a ^ 2 / α →
            value < 0)

/-- The exact Volterra boundary convolution and paired-density transfer identity. -/
def exactVolterraBoundaryConvolution : Prop :=
  ∀ a b u : ℝ,
    (1 / 2 : ℝ) < a →
    (1 / 2 : ℝ) < b →
    0 < u →
    0 < pairedBoundaryConvolution a b u ∧
      (a ≠ b →
        pairedBoundaryConvolution a b u =
          (sinhKernel b u - sinhKernel a u) / (b ^ 2 - a ^ 2)) ∧
      pairedKhat a b u 0 =
        -(a * b / 2) * u * pairedBoundaryConvolution a b u

/-- Every finite one-sided boundary transfer is strictly negative at every depth. -/
def everyFiniteOneSidedBoundaryTransferIsNegative : Prop :=
  ∀ a b : ℝ,
    (1 / 2 : ℝ) < a →
    (1 / 2 : ℝ) < b →
    ∀ u : ℝ,
      0 < u →
      ∀ m : ℕ,
        greenLIterate m (fun x => pairedKhat a b x 0) u < 0

end MathlibPlus.Open.Analysis
