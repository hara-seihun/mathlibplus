import MathlibPlus.Basic

namespace MathlibPlus.Algebra.InwardDirectionalDepth

/-- The two oriented pendant evaluations used in the affine cherry symbol. -/
def pendantSplit {R : Type*} [CommRing R]
    (F : R → R → R → R → R) (u v : R) : R :=
  F u 0 u v + F v 0 v u

/-- The affine transport state `τ = X + A - M`.  The `B` argument is
present so that the state can be evaluated by `pendantSplit`. -/
def transportState {R : Type*} [CommRing R] (X A _B M : R) : R :=
  X + A - M

/-- A split state is compatible when its two oriented pendant evaluations
cancel identically. -/
def pendantCompatible {R : Type*} [CommRing R]
    (F : R → R → R → R → R) : Prop :=
  ∀ u v : R, pendantSplit F u v = 0

/-- The one-step formulation of zero inward pendant depth: the state cancels,
but multiplication by the entering variable `X` does not. -/
def inwardDirectionalDepthZero {R : Type*} [CommRing R]
    (F : R → R → R → R → R) : Prop :=
  pendantCompatible F ∧
    ¬ pendantCompatible (fun X A B M => X * F X A B M)

/-- Claim 5427: the affine transport state cancels between the two split
orientations. -/
theorem transportState_pendant_cancellation
    {R : Type*} [CommRing R] [Nontrivial R] :
    pendantCompatible (R := R) (transportState (R := R)) := by
  intro u v
  simp [pendantSplit, transportState]

/-- Multiplication by the entering edge gives the displayed nonzero residual. -/
theorem entering_transportState_residual
    {R : Type*} [CommRing R] (u v : R) :
    pendantSplit (fun X A B M => X * transportState X A B M) u v =
      (u - v) ^ 2 := by
  simp [pendantSplit, transportState] <;> ring

/-- Consequently the affine transport state has zero inward pendant depth. -/
theorem transportState_inwardDirectionalDepth_zero
    {R : Type*} [CommRing R] [Nontrivial R] :
    inwardDirectionalDepthZero (R := R) (transportState (R := R)) := by
  constructor
  · exact transportState_pendant_cancellation
  · intro hcompat
    have h := hcompat 1 0
    rw [entering_transportState_residual (R := R)] at h
    norm_num at h

end MathlibPlus.Algebra.InwardDirectionalDepth
