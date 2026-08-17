import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1247.Claim30572

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

def shearAInverse (p : ℕ) (v : V p) : V p :=
  (v.1, v.2 - binomialTwo p v.1)

def shearBInverse (p : ℕ) (v : V p) : V p :=
  (v.1 - binomialTwo p v.2, v.2)

def rotationSection (h : SectionLabel) : Prop :=
  Equiv.Perm.sign h = 1

def reflectionSection (h : SectionLabel) : Prop :=
  ¬ rotationSection h

def sectionShear (p : ℕ) (h : SectionLabel) : V p → V p :=
  if Equiv.Perm.sign h = 1 then shearA p else shearB p

def sectionShearInverse (p : ℕ) (h : SectionLabel) : V p → V p :=
  if Equiv.Perm.sign h = 1 then shearAInverse p else shearBInverse p

/-- The normalized sectionwise quadratic-shear map `F`. -/
def markedMap (p : ℕ) : Point p → Point p :=
  fun z => (sectionShear p z.2 z.1, z.2)

/-- The normalized relative derivative with its section fixed in the inverse
factor. -/
def relativeDerivative (p : ℕ) (u : V p) (k h : SectionLabel) : V p → V p :=
  fun v => sectionShearInverse p h
    (sectionShear p (h * k) (v + u) - sectionShear p k u)

/-- The full derivative on all six sections for one choice of translation and
section multiplier. -/
def fullDerivativeGenerator (p : ℕ) (d : Equiv.Perm (Point p)) : Prop :=
  ∃ u : V p, ∃ k : SectionLabel,
    ∀ v : V p, ∀ h : SectionLabel,
      d (v, h) = (relativeDerivative p u k h v, h)

def pointIdentity (p : ℕ) : Point p :=
  (0, 1)

def pointInverse (p : ℕ) (z : Point p) : Point p :=
  (-z.1, z.2⁻¹)

def inverseClosedPointSet (p : ℕ) (S : Set (Point p)) : Prop :=
  ∀ z, z ∈ S → pointInverse p z ∈ S

/-- The seven inversion-compatible blocks. -/
def sevenBlocks (p : ℕ) : Set (Set (Point p)) :=
  {C | (C = {z | z.2 = 1 ∧ z.1 = 0}) ∨
    (C = {z | z.2 = 1 ∧ z.1 ≠ 0}) ∨
    (C = {z | rotationSection z.2 ∧ z.2 ≠ 1 ∧ z.1 = 0}) ∨
    (C = {z | rotationSection z.2 ∧ z.2 ≠ 1 ∧ z.1 ≠ 0}) ∨
    (∃ h : SectionLabel, reflectionSection h ∧
      C = {z | z.2 = h})}

/-- A union of selected members of the seven-block family. -/
def unionOfSevenBlocks (p : ℕ) (S : Set (Point p)) : Prop :=
  ∃ selected : Set (Set (Point p)),
    selected ⊆ sevenBlocks p ∧
      ∀ z : Point p,
        z ∈ S ↔ ∃ C : Set (Point p), C ∈ selected ∧ z ∈ C

/-- Claim 30572: for an odd prime, identity-free sets invariant under the
normalized relative derivatives, with both the source and marked image
inverse-closed, are unions of selected seven blocks and are fixed by `F`. -/
def claim30572_derivativeInvariantCIShadow : Prop :=
  ∀ p : ℕ, Nat.Prime p → Odd p →
    ∀ S : Set (Point p),
      S ⊆ {z | z ≠ pointIdentity p} →
        inverseClosedPointSet p S →
          inverseClosedPointSet p (Set.image (markedMap p) S) →
            (∀ d : Equiv.Perm (Point p),
              fullDerivativeGenerator p d → Set.image d S = S) →
              unionOfSevenBlocks p S ∧
                Set.image (markedMap p) S = S

end

end MathlibPlus.Open.ResearchFormalization.R1247.Claim30572
