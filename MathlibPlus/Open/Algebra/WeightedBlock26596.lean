import Mathlib

namespace MathlibPlus.Open.Algebra.WeightedBlock

noncomputable section

/-- The one-step emission row E_n=L_n(T_n-I). -/
def stepEmission {𝕜 V W : Type*} [Semiring 𝕜]
    [AddCommGroup V] [AddCommGroup W]
    [Module 𝕜 V] [Module 𝕜 W]
    (T : ℕ → V →ₗ[𝕜] V) (L : ℕ → V →ₗ[𝕜] W) (n : ℕ) : V →ₗ[𝕜] W :=
  (L n).comp (T n - (LinearMap.id : V →ₗ[𝕜] V))

/-- The state after a consecutive block, starting from an input state. -/
def blockState {𝕜 V : Type*} [Semiring 𝕜]
    [AddCommGroup V] [Module 𝕜 V]
    (T : ℕ → V →ₗ[𝕜] V) (a : ℕ) : ℕ → V → V
  | 0, z => z
  | n + 1, z => T (a + n) (blockState T a n z)

/-- The total block emission, evaluated on the entering state. -/
def blockEmission {𝕜 V W : Type*} [Semiring 𝕜]
    [AddCommGroup V] [AddCommGroup W]
    [Module 𝕜 V] [Module 𝕜 W]
    (T : ℕ → V →ₗ[𝕜] V) (L : ℕ → V →ₗ[𝕜] W)
    (a : ℕ) : ℕ → V → W
  | 0, z => 0
  | n + 1, z =>
      blockEmission T L a n z +
        stepEmission T L (a + n) (blockState T a n z)

/-- A pair of linear maps is a consecutive-block summary precisely when its
state and total-emission maps agree with the step recurrence. -/
def consecutiveBlockSummary
    {𝕜 V W : Type*} [Semiring 𝕜]
    [AddCommGroup V] [AddCommGroup W]
    [Module 𝕜 V] [Module 𝕜 W]
    (T : ℕ → V →ₗ[𝕜] V) (L : ℕ → V →ₗ[𝕜] W)
    (a n : ℕ) (TBlock : V →ₗ[𝕜] V) (EBlock : V →ₗ[𝕜] W) : Prop :=
  (∀ z : V, TBlock z = blockState T a n z) ∧
    (∀ z : V, EBlock z = blockEmission T L a n z)

/-- Composition of a right summary after a left summary. -/
def composeSummary
    {𝕜 V W : Type*} [Semiring 𝕜]
    [AddCommGroup V] [AddCommGroup W]
    [Module 𝕜 V] [Module 𝕜 W]
    (right left : (V →ₗ[𝕜] V) × (V →ₗ[𝕜] W)) :
    (V →ₗ[𝕜] V) × (V →ₗ[𝕜] W) :=
  (right.1.comp left.1, left.2 + right.2.comp left.1)

/-- The canonical summary obtained by composing all one-step blocks. -/
def blockSummary
    {𝕜 V W : Type*} [Semiring 𝕜]
    [AddCommGroup V] [AddCommGroup W]
    [Module 𝕜 V] [Module 𝕜 W]
    (T : ℕ → V →ₗ[𝕜] V) (L : ℕ → V →ₗ[𝕜] W)
    (a : ℕ) : ℕ → (V →ₗ[𝕜] V) × (V →ₗ[𝕜] W)
  | 0 => (LinearMap.id, 0)
  | n + 1 =>
      composeSummary
        (T (a + n), stepEmission T L (a + n))
        (blockSummary T L a n)

/-- The exact weighted block-summary state/emission convention. -/
def claim_26596 : Prop :=
  ∀ {𝕜 V W : Type*} [Semiring 𝕜]
    [AddCommGroup V] [AddCommGroup W]
    [Module 𝕜 V] [Module 𝕜 W]
    (T : ℕ → V →ₗ[𝕜] V) (L : ℕ → V →ₗ[𝕜] W),
    (∀ n : ℕ, stepEmission T L n =
      (L n).comp (T n - (LinearMap.id : V →ₗ[𝕜] V))) ∧
      (∀ (a n : ℕ),
        consecutiveBlockSummary T L a n
          (blockSummary T L a n).1
          (blockSummary T L a n).2)

end

end MathlibPlus.Open.Algebra.WeightedBlock
