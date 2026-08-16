import Mathlib
import MathlibPlus.Open.ResearchFormalizationBatch_01a0096e_5a75_7fe3_bebc_178cf02aa479

namespace MathlibPlus.Open.ResearchFormalization.O0140LowDegree

open MathlibPlus.Open.ResearchFormalizationBatch_01a0096e_5a75_7fe3_bebc_178cf02aa479

noncomputable section

abbrev D8 := DihedralGroup 4
abbrev V2 := Fin 2 → ℂ
abbrev MSpace (k : ℕ) := (Fin (k + 1) × Fin (k + 1)) → ℂ

def s0 : D8 := DihedralGroup.sr (0 : ZMod 4)
def s1 : D8 := DihedralGroup.sr (1 : ZMod 4)
def w0 : D8 := (s0 * s1) ^ 2

def coefficientRepresentation (k : ℕ)
    (ρ : Representation ℂ D8 (MSpace k)) : Prop :=
  ρ s0 = Matrix.toLin' (swapMatrix k) ∧
    ρ s1 = Matrix.toLin' (rhMatrixAt k) ∧
    ρ w0 = Matrix.toLin' (rhMatrixAt k * rcMatrixAt k)

def oneDimensionalCharacter (a b : ℂ)
    (χ : Representation ℂ D8 ℂ) : Prop :=
  χ s0 = a • (LinearMap.id : ℂ →ₗ[ℂ] ℂ) ∧
    χ s1 = b • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)

def M1LineSummands
    (χpp χpm : Representation ℂ D8 ℂ) :
    ∀ i : Fin 2, Representation ℂ D8 ℂ :=
  Fin.cases χpp (fun _ => χpm)

def M2LineSummands
    (χpp χpm χmp : Representation ℂ D8 ℂ) :
    ∀ i : Fin 5, Representation ℂ D8 ℂ :=
  Fin.cases χpp (fun i₁ =>
    Fin.cases χpp (fun i₂ =>
      Fin.cases χpp (fun i₃ =>
        Fin.cases χpm (fun _ => χmp) i₃) i₂) i₁)

def lineDirectSumM1
    (χpp χpm : Representation ℂ D8 ℂ) :=
  Representation.directSum (M1LineSummands χpp χpm)

def lineDirectSumM2
    (χpp χpm χmp : Representation ℂ D8 ℂ) :=
  Representation.directSum (M2LineSummands χpp χpm χmp)

def twoCopyDirectSum (ρ₂ : Representation ℂ D8 V2) :=
  Representation.directSum (fun _ : Fin 2 => ρ₂)

/-- The two explicit direct-sum blocks are joined by the canonical finite
biproduct representation. -/
def lowDegreeM1
    (χpp χpm : Representation ℂ D8 ℂ)
    (ρ₂ : Representation ℂ D8 V2) :=
  (lineDirectSumM1 χpp χpm).prod ρ₂

def lowDegreeM2
    (χpp χpm χmp : Representation ℂ D8 ℂ)
    (ρ₂ : Representation ℂ D8 V2) :=
  (lineDirectSumM2 χpp χpm χmp).prod (twoCopyDirectSum ρ₂)

def isTwoDimensionalIrrep {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ D8 W) : Prop :=
  Module.finrank ℂ W = 2 ∧ Representation.IsIrreducible τ

def isUniqueTwoDimensionalIrrep {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ D8 W) : Prop :=
  isTwoDimensionalIrrep τ ∧
    ∀ {U : Type} [AddCommGroup U] [Module ℂ U]
      (σ : Representation ℂ D8 U),
      isTwoDimensionalIrrep σ → Nonempty (σ.Equiv τ)

def centralNegativeFourSource {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ D8 W) : Prop :=
  Representation.IsSemisimpleRepresentation ρ ∧
    Module.finrank ℂ W = 4 ∧
    ρ w0 = (-1 : ℂ) • (LinearMap.id : W →ₗ[ℂ] W)

/-- Claim 14729: the fixed coefficient modules at degrees one and two are
isomorphic, as D₈-representations, to the displayed direct sums. -/
def claim14729 : Prop :=
  ∃ (ρ₁ : Representation ℂ D8 (MSpace 1))
    (ρ₂ : Representation ℂ D8 (MSpace 2))
    (χpp χpm χmp : Representation ℂ D8 ℂ)
    (τ : Representation ℂ D8 V2),
    coefficientRepresentation 1 ρ₁ ∧
      coefficientRepresentation 2 ρ₂ ∧
      oneDimensionalCharacter 1 1 χpp ∧
      oneDimensionalCharacter 1 (-1) χpm ∧
      oneDimensionalCharacter (-1) 1 χmp ∧
      isUniqueTwoDimensionalIrrep τ ∧
      Nonempty (ρ₁.Equiv (lowDegreeM1 χpp χpm τ)) ∧
      Nonempty (ρ₂.Equiv (lowDegreeM2 χpp χpm χmp τ))

/-- Claim 14733: one-dimensional characters are trivial on the central
longest element, and a semisimple four-dimensional source on which it is
negative is two copies of the unique two-dimensional irreducible. -/
def claim14733 : Prop :=
  (∀ χ : Representation ℂ D8 ℂ, χ w0 = (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) ∧
    ∃ (τ : Representation ℂ D8 V2),
      isUniqueTwoDimensionalIrrep τ ∧
        ∀ {W : Type} [AddCommGroup W] [Module ℂ W]
          (ρ : Representation ℂ D8 W),
          centralNegativeFourSource ρ →
          Nonempty (ρ.Equiv (twoCopyDirectSum τ))

end
end MathlibPlus.Open.ResearchFormalization.O0140LowDegree
