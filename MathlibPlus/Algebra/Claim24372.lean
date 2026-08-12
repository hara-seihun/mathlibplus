import Mathlib

namespace MathlibPlus.Algebra

/-- Claim 24372: the displayed simultaneous-rectangle recursions force equal
coarse states.  The tree carrier and `node` operation are left abstract; the
claim only supplies these state recursions. -/
theorem simultaneousRectangleParents_equalCoarseMomentStates_claim24372
    {T R : Type*} [CommRing R]
    (p ν ρ : T → R) (node : T → T → T)
    (A C B D : T) (a q : R)
    (hpc : p A * p C = p B * p D)
    (hν : ν A * ν C = ν B * ν D)
    (hρAC : ρ (node A C) = p A * p C)
    (hρBD : ρ (node B D) = p B * p D)
    (hpAC : p (node A C) = a * (p A * p C) + (q - a) * (ν A * ν C))
    (hpBD : p (node B D) = a * (p B * p D) + (q - a) * (ν B * ν D)) :
    ρ (node A C) = ρ (node B D) ∧ p (node A C) = p (node B D) := by
  constructor
  · calc
      ρ (node A C) = p A * p C := hρAC
      _ = p B * p D := hpc
      _ = ρ (node B D) := hρBD.symm
  · calc
      p (node A C) = a * (p A * p C) + (q - a) * (ν A * ν C) := hpAC
      _ = a * (p B * p D) + (q - a) * (ν B * ν D) := by rw [hpc, hν]
      _ = p (node B D) := hpBD.symm

end MathlibPlus.Algebra
