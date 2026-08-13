import Mathlib

/-!
# Finite shift packets

Core finite-packet vocabulary and the zeroth-moment identities from packet `D-0030`.
The finite integer packet and finite signed measure remain distinct types.  This file
does not identify either finite type with a distributional or unbounded shift carrier.
-/

namespace MathlibPlus.Analysis.ShiftPacket

/-- A finite real shift spectrum with integer exponents. -/
abbrev IntegerShiftPacket := ℝ →₀ ℤ

/-- A finite atomic signed measure on real shifts. -/
abbrev FiniteSignedShiftMeasure := ℝ →₀ ℝ

/-- Total exponent of an integer shift packet. -/
def packetTotalExponent (p : IntegerShiftPacket) : ℤ :=
  p.sum fun _ c => c

/-- Degree-`d` exponent-weighted shift moment. -/
def packetShiftMoment (p : IntegerShiftPacket) (d : ℕ) : ℝ :=
  p.sum fun alpha c => (c : ℝ) * alpha ^ d

/-- Total mass of a finite signed shift measure. -/
def measureMass (mu : FiniteSignedShiftMeasure) : ℝ :=
  mu.sum fun _ mass => mass

/-- Degree-`d` moment of a finite signed shift measure. -/
def measureShiftMoment (mu : FiniteSignedShiftMeasure) (d : ℕ) : ℝ :=
  mu.sum fun alpha mass => mass * alpha ^ d

/-- Integer packets are balanced when their zeroth and first shift data vanish. -/
def IsBalancedIntegerPacket (p : IntegerShiftPacket) : Prop :=
  packetTotalExponent p = 0 ∧ packetShiftMoment p 1 = 0

/-- Finite signed shift measures are balanced when their mass and first moment vanish. -/
def IsBalancedFiniteMeasure (mu : FiniteSignedShiftMeasure) : Prop :=
  measureMass mu = 0 ∧ measureShiftMoment mu 1 = 0

/-- A degree-zero shift moment is exactly total exponent or total mass, respectively. -/
theorem zerothShiftMoments :
    (∀ p : IntegerShiftPacket,
      packetShiftMoment p 0 = (packetTotalExponent p : ℝ)) ∧
    ∀ mu : FiniteSignedShiftMeasure, measureShiftMoment mu 0 = measureMass mu := by
  constructor
  · intro p
    classical
    simp [packetShiftMoment, packetTotalExponent]
  · intro mu
    classical
    simp [measureShiftMoment, measureMass]

/-- Every translated integer-packet atom moves by `a` and retains its exponent. -/
theorem shiftPacket_atom (a alpha : ℝ) (p : IntegerShiftPacket) :
    (Finsupp.mapDomain (fun beta => beta + a) p) (alpha + a) = p alpha := by
  apply Finsupp.mapDomain_apply
  intro x y hxy
  linarith

/-- A translated atom is in the translated support exactly when its source atom is. -/
theorem mem_support_shiftPacket_iff (a alpha : ℝ) (p : IntegerShiftPacket) :
    alpha + a ∈ (Finsupp.mapDomain (fun beta => beta + a) p).support ↔
      alpha ∈ p.support := by
  simp only [Finsupp.mem_support_iff, ne_eq, shiftPacket_atom]

end MathlibPlus.Analysis.ShiftPacket
