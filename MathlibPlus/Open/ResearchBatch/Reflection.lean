import Mathlib

namespace MathlibPlus.Open.ResearchBatch.Reflection

open scoped BigOperators

noncomputable section

/-- The Weil/Mellin reflection on the complex variable. -/
def weilTau (s : ℂ) : ℂ := 1 - star s

/-- A finite occurrence-indexed reflected zero packet.  The finite index
records multiplicity, while `reflect` pairs each occurrence with its
reflected occurrence. -/
def IsFiniteReflectedZeroPacket {ι : Type*} [Fintype ι]
    (root : ι → ℂ) (reflect : ι → ι) : Prop :=
  Function.Involutive reflect ∧
    ∀ i, root (reflect i) = weilTau (root i)

/-- The analytic finite reflection form, with the index type summing
multiplicities of repeated roots. -/
def reflectedAnalyticForm {ι : Type*} [Fintype ι]
    (root : ι → ℂ) (F G : ℂ → ℂ) : ℂ :=
  ∑ i, F (root i) * star (G (weilTau (root i)))

/-- The same form in occurrence coordinates. -/
def reflectedCoordinateForm {ι : Type*} [Fintype ι]
    (reflect : ι → ι) (v w : ι → ℂ) : ℂ :=
  ∑ i, v i * star (w (reflect i))

/-- The reflected form written in coordinates is the displayed analytic form. -/
def reflectionFormSpecification {ι : Type*} [Fintype ι]
    (root : ι → ℂ) (reflect : ι → ι) : Prop :=
  IsFiniteReflectedZeroPacket root reflect →
    ∀ F G : ℂ → ℂ,
      reflectedAnalyticForm root F G =
        reflectedCoordinateForm reflect (fun i => F (root i))
          (fun i => G (root i))

/-- Evaluation on a finite packet converts the analytic and coordinate forms
exactly, including multiplicities. -/
def analyticCoordinateReflectionAgreement {ι : Type*} [Fintype ι]
    (root : ι → ℂ) (reflect : ι → ι) : Prop :=
  IsFiniteReflectedZeroPacket root reflect →
    ∀ F G : ℂ → ℂ,
      reflectedAnalyticForm root F G =
        reflectedCoordinateForm reflect (fun i => F (root i))
          (fun i => G (root i))

/-- The finite reflection form is Hermitian. -/
def reflectionFormHermitian {ι : Type*} [Fintype ι]
    (root : ι → ℂ) (reflect : ι → ι) : Prop :=
  IsFiniteReflectedZeroPacket root reflect →
    ∀ F G : ℂ → ℂ,
      reflectedAnalyticForm root F G =
        star (reflectedAnalyticForm root G F)

/-- Reflection positivity means nonnegative real part on every complex-valued
function on the Mellin variable. -/
def ReflectionPositive {ι : Type*} [Fintype ι]
    (root : ι → ℂ) (reflect : ι → ι) : Prop :=
  IsFiniteReflectedZeroPacket root reflect →
    ∀ F : ℂ → ℂ, 0 ≤ (reflectedAnalyticForm root F F).re

/-- Reflection positivity is equivalent to every packet root being fixed by
Weil reflection. -/
def reflectionPositivityIffFixed {ι : Type*} [Fintype ι]
    (root : ι → ℂ) (reflect : ι → ι) : Prop :=
  IsFiniteReflectedZeroPacket root reflect →
    (ReflectionPositive root reflect ↔
      ∀ i, weilTau (root i) = root i)

/-- Fixed roots for Weil reflection are exactly roots on the critical line. -/
def reflectionPositivityIffCriticalLine {ι : Type*} [Fintype ι]
    (root : ι → ℂ) (reflect : ι → ι) : Prop :=
  IsFiniteReflectedZeroPacket root reflect →
    (ReflectionPositive root reflect ↔
      ∀ i, (root i).re = (1 : ℝ) / 2)

end

end MathlibPlus.Open.ResearchBatch.Reflection
