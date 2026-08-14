import Mathlib

noncomputable section

namespace MathlibPlus.Open.Research.Pauli

abbrev Mat₂ := Matrix (Fin 2) (Fin 2) ℂ

def pauliX : Mat₂ :=
  fun i j => if i = 0 ∧ j = 1 then 1 else
    if i = 1 ∧ j = 0 then 1 else 0

def pauliZ : Mat₂ :=
  fun i j => if i = j then (if i.val = 0 then 1 else -1) else 0

def pauliY : Mat₂ :=
  fun i j => if i = 0 ∧ j = 1 then -Complex.I else
    if i = 1 ∧ j = 0 then Complex.I else 0

def iPauliY : Mat₂ := (Complex.I : ℂ) • pauliY

def pauliPMinus : Mat₂ :=
  ((2 : ℂ)⁻¹) • ((1 : Mat₂) - pauliZ)

def klingenCoefficient (κ : ℂ) : Mat₂ := pauliX + κ • pauliPMinus

def oddProjection (B : Mat₂) : Mat₂ :=
  ((2 : ℂ)⁻¹) • (B - pauliZ * B * pauliZ)

def inSpan₂ (A B C : Mat₂) : Prop :=
  ∃ a b : ℂ, C = a • A + b • B

/-- Claim 11825: the Hecke-parity projection selects the X-axis. -/
def claim11825 : Prop :=
  (∀ κ : ℂ, oddProjection (klingenCoefficient κ) = pauliX) ∧
  (∀ B : Mat₂,
    B.transpose = B →
    pauliZ * B * pauliZ = -B →
    B 0 1 = 1 →
    B = pauliX)

def Rₕ (B : Mat₂) : Mat₂ := pauliX * B

def R_c (B : Mat₂) : Mat₂ := B * pauliX

def D (B : Mat₂) : Mat₂ := pauliX * B * pauliX

/-- Claim 11828: the left/right coefficient involutions and their eigenspaces. -/
def claim11828 : Prop :=
  (∀ B : Mat₂, Rₕ (Rₕ B) = B ∧ R_c (R_c B) = B ∧
    Rₕ (R_c B) = R_c (Rₕ B)) ∧
  (∀ B : Mat₂, D B = B ↔ inSpan₂ (1 : Mat₂) pauliX B) ∧
  (∀ B : Mat₂, D B = -B ↔ inSpan₂ pauliZ iPauliY B)

def rightPMinus (B : Mat₂) : Mat₂ := B * pauliPMinus

def rightImageSpan : Submodule ℂ Mat₂ :=
  Submodule.span ℂ {B : Mat₂ | ∃ A : Mat₂, B = rightPMinus A}

def rightKernelSet : Set Mat₂ := {B : Mat₂ | rightPMinus B = 0}

def scalarColumnSpan : Submodule ℂ Mat₂ :=
  Submodule.span ℂ {pauliPMinus}

/-- Claim 11829: one retained cusp column has rank two and loses half the frame. -/
def claim11829 : Prop :=
  rightPMinus (1 : Mat₂) = pauliPMinus ∧
  rightPMinus pauliZ = -pauliPMinus ∧
  rightPMinus pauliX = rightPMinus iPauliY ∧
  Module.finrank ℂ rightImageSpan = 2 ∧
  rightKernelSet =
    {B : Mat₂ | ∃ a b : ℂ,
      B = a • ((1 : Mat₂) + pauliZ) + b • (pauliX - iPauliY)} ∧
  Module.finrank ℂ scalarColumnSpan = 1

end MathlibPlus.Open.Research.Pauli

end
