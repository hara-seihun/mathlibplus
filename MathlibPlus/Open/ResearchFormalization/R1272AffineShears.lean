import MathlibPlus.LinearAlgebra.Claim30857

namespace MathlibPlus.Open.ResearchFormalization.R1272AffineShears

section AffineShear

variable {𝔽 W V : Type*}
variable [Field 𝔽] [Fintype 𝔽]
variable [AddCommGroup W] [AddCommGroup V]
variable [Module 𝔽 W] [Module 𝔽 V]
variable [FiniteDimensional 𝔽 W] [FiniteDimensional 𝔽 V]

/-- The displayed affine hyperplane from the admitted triangular-shear claims. -/
def affineHyperplane (a : W →ₗ[𝔽] 𝔽) (b : V →ₗ[𝔽] 𝔽) (t : 𝔽) : Set (W × V) :=
  {p | a p.1 + b p.2 = t}

/-- The triangular shear `q_c(w,v) = (w,v+c(w))`. -/
def triangularShear (c : W → V) : W × V → W × V :=
  fun p => (p.1, p.2 + c p.1)

/-- A `w`-fiber of a displayed affine hyperplane. -/
def affineFiber (a : W →ₗ[𝔽] 𝔽) (b : V →ₗ[𝔽] 𝔽) (t : 𝔽) (w : W) : Set V :=
  {v | a w + b v = t}

/-- The direction of a fiber, defined by its differences rather than by its normal. -/
def affineFiberDirection (a : W →ₗ[𝔽] 𝔽) (b : V →ₗ[𝔽] 𝔽) (t : 𝔽) (w : W) : Set V :=
  {d | ∃ v₁ v₂ : V, v₁ ∈ affineFiber a b t w ∧ v₂ ∈ affineFiber a b t w ∧ v₁ - v₂ = d}

/-- A set is an affine hyperplane in the displayed functional convention. -/
def displayedAffineHyperplane (H : Set (W × V)) : Prop :=
  ∃ (a : W →ₗ[𝔽] 𝔽) (b : V →ₗ[𝔽] 𝔽) (t : 𝔽),
    (a ≠ 0 ∨ b ≠ 0) ∧ H = affineHyperplane a b t

/-- Claim 30858: nonzero fiber normals determine the fiber directions, and after
rescaling a target normal the image equation is exactly the scalar-shadow equation. -/
def claim30858 : Prop :=
  ∀ (c : W → V) (a : W →ₗ[𝔽] 𝔽) (b : V →ₗ[𝔽] 𝔽) (t : 𝔽), b ≠ 0 →
    (∀ w : W, affineFiberDirection a b t w = (LinearMap.ker b : Set V)) ∧
    ∀ (a' : W →ₗ[𝔽] 𝔽) (b' : V →ₗ[𝔽] 𝔽) (t' : 𝔽),
      (a' ≠ 0 ∨ b' ≠ 0) →
        (triangularShear c '' affineHyperplane a b t = affineHyperplane a' b' t' →
          LinearMap.ker b = LinearMap.ker b' ∧
            ∃ μ : 𝔽, μ ≠ 0 ∧ b' = μ • b) ∧
        (triangularShear c '' affineHyperplane a b t = affineHyperplane a' b' t' ↔
          ∃ μ : 𝔽, μ ≠ 0 ∧ b' = μ • b ∧
            ∀ w : W,
              b (c w) = (μ⁻¹ * t' - t) +
                (a w - (μ⁻¹ • a') w))

end AffineShear

section MorrisShear

abbrev F3 := ZMod 3
abbrev MorrisBase := Fin 3 → F3
abbrev MorrisFiber := Fin 5 → F3

/-- The Morris correction from the admitted R-1272 packet. -/
def morrisCorrection (x : MorrisBase) : MorrisFiber :=
  ![x 0 * (x 1) ^ 2,
    x 0 * (x 2) ^ 2,
    (x 1) ^ 2 * x 2,
    x 1 * (x 2) ^ 2,
    x 0 * x 1 * x 2]

/-- The set of affine hyperplanes represented in the functional convention. -/
def morrisDisplayedAffineHyperplane
    (H : Set (MorrisBase × MorrisFiber)) : Prop :=
  ∃ (a : MorrisBase →ₗ[F3] F3) (b : MorrisFiber →ₗ[F3] F3) (t : F3),
    (a ≠ 0 ∨ b ≠ 0) ∧ H = affineHyperplane a b t

/-- The hyperplanes whose Morris-shear image is again affine. -/
def morrisSurvivingAffineHyperplanes : Set (Set (MorrisBase × MorrisFiber)) :=
  {H | morrisDisplayedAffineHyperplane H ∧
    morrisDisplayedAffineHyperplane
      (triangularShear morrisCorrection '' H)}

/-- The base vector used to test the first nonzero coefficient. -/
def morrisBasisVector (i : Fin 3) : MorrisBase :=
  Pi.single i 1

/-- Normalized representatives of projective nonzero base-normal directions. -/
def normalizedBaseDirection (a : MorrisBase →ₗ[F3] F3) : Prop :=
  a ≠ 0 ∧
    (a (morrisBasisVector 0) = 1 ∨
      (a (morrisBasisVector 0) = 0 ∧ a (morrisBasisVector 1) = 1) ∨
      (a (morrisBasisVector 0) = 0 ∧ a (morrisBasisVector 1) = 0 ∧
        a (morrisBasisVector 2) = 1))

def normalizedBaseDirections : Set (MorrisBase →ₗ[F3] F3) :=
  {a | normalizedBaseDirection a}

abbrev NormalizedBaseDirection :=
  {a : MorrisBase →ₗ[F3] F3 // a ∈ normalizedBaseDirections}

/-- The pure base-normal hyperplane indexed by a normalized direction and offset. -/
def pureBaseNormalHyperplane
    (p : NormalizedBaseDirection × F3) : Set (MorrisBase × MorrisFiber) :=
  affineHyperplane p.1.1 0 p.2

/-- The pure base-normal cosets, as actual subsets of the ambient affine space. -/
def pureBaseNormalCosets : Set (Set (MorrisBase × MorrisFiber)) :=
  {H | ∃ a ∈ normalizedBaseDirections, ∃ t : F3,
    H = affineHyperplane a 0 t}

/-- An affine scalar shadow of the Morris correction. -/
def morrisAffineScalarShadow (b : MorrisFiber →ₗ[F3] F3) : Prop :=
  ∃ (a : MorrisBase →ₗ[F3] F3) (t : F3),
    ∀ w : MorrisBase, b (morrisCorrection w) = a w + t

/-- Claim 30863: nonzero fiber normals do not survive; the surviving hyperplanes
are exactly the 13 normalized projective base directions with their three offsets,
with the displayed indexing map bijective onto the actual surviving hyperplane set. -/
def claim30863 : Prop :=
  (∀ (b : MorrisFiber →ₗ[F3] F3), b ≠ 0 → ¬ morrisAffineScalarShadow b) ∧
  (∀ (a : MorrisBase →ₗ[F3] F3) (b : MorrisFiber →ₗ[F3] F3) (t : F3),
    b ≠ 0 →
      ¬ morrisDisplayedAffineHyperplane
        (triangularShear morrisCorrection '' affineHyperplane a b t)) ∧
  (∀ (a : MorrisBase →ₗ[F3] F3) (b : MorrisFiber →ₗ[F3] F3) (t : F3),
    (a ≠ 0 ∨ b ≠ 0) →
      morrisDisplayedAffineHyperplane
        (triangularShear morrisCorrection '' affineHyperplane a b t) →
      b = 0) ∧
  morrisSurvivingAffineHyperplanes = pureBaseNormalCosets ∧
  Set.ncard normalizedBaseDirections = 13 ∧
  Fintype.card F3 = 3 ∧
  Set.Finite morrisSurvivingAffineHyperplanes ∧
  Set.ncard morrisSurvivingAffineHyperplanes = 39 ∧
  Set.BijOn pureBaseNormalHyperplane
    (Set.univ : Set (NormalizedBaseDirection × F3))
    morrisSurvivingAffineHyperplanes

end MorrisShear

end MathlibPlus.Open.ResearchFormalization.R1272AffineShears
