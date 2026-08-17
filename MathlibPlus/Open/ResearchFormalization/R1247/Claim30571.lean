import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1247.Claim30571

noncomputable section

abbrev V (p : ℕ) := ZMod p × ZMod p
abbrev SectionLabel := Equiv.Perm (Fin 3)
abbrev Point (p : ℕ) := V p × SectionLabel

/-- The finite-field quadratic `c(t)=binom(t,2)`. -/
def binomialTwo (p : ℕ) (t : ZMod p) : ZMod p :=
  t * (t - 1) * (2 : ZMod p)⁻¹

def shearA (p : ℕ) (v : V p) : V p :=
  (v.1, v.2 + binomialTwo p v.1)

def shearB (p : ℕ) (v : V p) : V p :=
  (v.1 + binomialTwo p v.2, v.2)

def rotationSection (h : SectionLabel) : Prop :=
  Equiv.Perm.sign h = 1

def reflectionSection (h : SectionLabel) : Prop :=
  ¬ rotationSection h

def sectionShear (p : ℕ) (h : SectionLabel) : V p → V p :=
  if Equiv.Perm.sign h = 1 then shearA p else shearB p

/-- The sectionwise quadratic-shear map `F`. -/
def markedMap (p : ℕ) : Point p → Point p :=
  fun z => (sectionShear p z.2 z.1, z.2)

/-- The seven inversion-compatible blocks from the nine local derivative
orbits. -/
def sevenBlocks (p : ℕ) : Set (Set (Point p)) :=
  {C | (C = {z | z.2 = 1 ∧ z.1 = 0}) ∨
    (C = {z | z.2 = 1 ∧ z.1 ≠ 0}) ∨
    (C = {z | rotationSection z.2 ∧ z.2 ≠ 1 ∧ z.1 = 0}) ∨
    (C = {z | rotationSection z.2 ∧ z.2 ≠ 1 ∧ z.1 ≠ 0}) ∨
    (∃ h : SectionLabel, reflectionSection h ∧
      C = {z | z.2 = h})}

/-- Claim 30571: both quadratic shears are bijections fixing zero, and `F`
fixes each of the seven blocks setwise. -/
def claim30571_markedMapFixesSevenBlocks : Prop :=
  ∀ p : ℕ, Nat.Prime p → Odd p →
    Function.Bijective (shearA p) ∧
      shearA p 0 = 0 ∧
        Function.Bijective (shearB p) ∧
          shearB p 0 = 0 ∧
            ∀ C ∈ sevenBlocks p,
              Set.image (markedMap p) C = C

end

end MathlibPlus.Open.ResearchFormalization.R1247.Claim30571
