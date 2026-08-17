import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1247.Claim30569

noncomputable section

abbrev V (p : ℕ) := ZMod p × ZMod p
abbrev SectionLabel := Equiv.Perm (Fin 3)

/-- The finite-field quadratic `c(t)=binom(t,2)`. -/
def binomialTwo (p : ℕ) (t : ZMod p) : ZMod p :=
  t * (t - 1) * (2 : ZMod p)⁻¹

/-- The two section maps in the admitted parity-mixed construction. -/
def shearA (p : ℕ) (v : V p) : V p :=
  (v.1, v.2 + binomialTwo p v.1)

def shearB (p : ℕ) (v : V p) : V p :=
  (v.1 + binomialTwo p v.2, v.2)

def shearAInverse (p : ℕ) (v : V p) : V p :=
  (v.1, v.2 - binomialTwo p v.1)

def shearBInverse (p : ℕ) (v : V p) : V p :=
  (v.1 - binomialTwo p v.2, v.2)

/-- The rotation/reflection section split of `S₃`. -/
def rotationSection (h : SectionLabel) : Prop :=
  Equiv.Perm.sign h = 1

def reflectionSection (h : SectionLabel) : Prop :=
  ¬ rotationSection h

def sectionShear (p : ℕ) (h : SectionLabel) : V p → V p :=
  if Equiv.Perm.sign h = 1 then shearA p else shearB p

def sectionShearInverse (p : ℕ) (h : SectionLabel) : V p → V p :=
  if Equiv.Perm.sign h = 1 then shearAInverse p else shearBInverse p

/-- The normalized relative derivative on the fixed section `h`. -/
def relativeDerivative (p : ℕ) (u : V p) (k h : SectionLabel) : V p → V p :=
  fun v => sectionShearInverse p h
    (sectionShear p (h * k) (v + u) - sectionShear p k u)

/-- Generators for the normalized relative-derivative group on one fixed
section.  The section parameter is not existentially pooled with the other
sections. -/
def derivativeGenerator (p : ℕ) (h : SectionLabel)
    (d : Equiv.Perm (V p)) : Prop :=
  ∃ u : V p, ∃ k : SectionLabel,
    ∀ v : V p, d v = relativeDerivative p u k h v

def derivativeGroup (p : ℕ) (h : SectionLabel) : Subgroup (Equiv.Perm (V p)) :=
  Subgroup.closure {d | derivativeGenerator p h d}

def derivativeOrbit (p : ℕ) (h : SectionLabel) (v : V p) : Set (V p) :=
  {w | ∃ d : derivativeGroup p h,
    (d : Equiv.Perm (V p)) v = w}

/-- Claim 30569: the fixed-section normalized relative-derivative group has
exactly the zero/nonzero rotation orbits and the single full reflection orbit,
with the odd-prime restriction retained. -/
def claim30569_sectionwiseDerivativeOrbits : Prop :=
  ∀ p : ℕ, Nat.Prime p → Odd p →
    (∀ h : SectionLabel, rotationSection h →
      derivativeOrbit p h 0 = ({0} : Set (V p)) ∧
        (∀ v : V p, v ≠ 0 →
          derivativeOrbit p h v = {w | w ≠ 0})) ∧
    (∀ h : SectionLabel, reflectionSection h →
      ∀ v : V p, derivativeOrbit p h v = Set.univ)

end

end MathlibPlus.Open.ResearchFormalization.R1247.Claim30569
