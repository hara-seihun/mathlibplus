import Mathlib

namespace MathlibPlus.Algebra.Claim33443

/-!
Formalization of admitted claim 33443.

The source statement does not define `δ_v`; this file exposes the convention
used here: `δ_v t x = t (x + v) - t x`.  The source also leaves the domain
and codomain implicit, so the identity is stated for arbitrary additive
commutative groups.
-/

/-- Periodicity of the anti-sum gives the corresponding finite-difference
identity. -/
theorem antiSum_periodicity
    {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (c v : G) (t : G → A)
    (hperiod : ∀ h : G,
      t (c - h) + t h = t (c - (h - v)) + t (h - v)) :
    ∀ h : G,
      t ((c - h) + v) - t (c - h) = t h - t (h - v) := by
  intro h
  have hshift : c - (h - v) = (c - h) + v := by
    abel
  have hp := hperiod h
  rw [hshift] at hp
  calc
    t ((c - h) + v) - t (c - h) =
        (t ((c - h) + v) + t (h - v)) -
          (t (c - h) + t (h - v)) := by abel
    _ = (t (c - h) + t h) -
          (t (c - h) + t (h - v)) := by rw [← hp]
    _ = t h - t (h - v) := by abel

/-- If `t` is anti-invariant under the affine reflection, its anti-sum is
identically zero and hence periodic. -/
theorem antiInvariant
    {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (c v : G) (t : G → A)
    (hanti : ∀ h : G, t (c - h) = -t h) :
    (∀ h : G,
      t (c - h) + t h = t (c - (h - v)) + t (h - v)) ∧
      (∀ h : G, t (c - h) + t h = 0) := by
  constructor
  · intro h
    have h₁ := hanti h
    have h₂ := hanti (h - v)
    rw [h₁, h₂]
    abel
  · intro h
    rw [hanti h]
    abel

end MathlibPlus.Algebra.Claim33443
