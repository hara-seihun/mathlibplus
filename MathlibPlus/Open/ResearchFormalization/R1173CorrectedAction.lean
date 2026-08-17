import MathlibPlus.Open.Research.QuadraticBatch

namespace MathlibPlus.Open.ResearchFormalization.R1173CorrectedAction

noncomputable section

open MathlibPlus.Open.Research.QuadraticBatch

abbrev BasisChoice := Fin 4

def basisVector : BasisChoice → Fiber :=
  ![![0, 0, 0], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]

/-- The state `(v,z)` over plane point `x`, in the original `(z,x,u)`
coordinates with `v = u - Q(x)`. -/
def fiberCoordinate (x : Plane) (v : Fiber) (z : F3) : Omega :=
  (z, x, v + fixedShift x)

/-- The point stabilizer of the displayed generated pair. -/
def pointStabilizer (H : Plane → F3) (m : Fiber → F3) : Set (Equiv.Perm Omega) :=
  {q | q ∈ generatedPair H m ∧ q (0, 0, 0) = (0, 0, 0)}

/-- The corrected action's exact state-coordinate target. -/
def correctedStateTarget
    (H : Plane → F3) (m : Fiber → F3)
    (x s : Plane) (w : BasisChoice) (v : Fiber) (z : F3) : Fiber × F3 :=
  (v + bilinearCorrection s x,
    z + (H (x + s) - H x) * m v +
      H (x + s) * polarForm m v (basisVector w) +
      (H (x + s) - H s) * m (basisVector w))

/-- Claim 41640: for every homogeneous form, the corrected point-stabilizer
entries indexed by `s` and `w` have the displayed action on every state over a
fixed plane point. -/
def correctedPointStabilizerAction_claim41640 : Prop :=
  ∀ (H : Plane → F3) (m : Fiber → F3), IsHomogeneousQuadratic m →
    ∀ x : Plane, ∀ s : Plane, ∀ w : BasisChoice,
      ∃ q : Equiv.Perm Omega,
        q ∈ pointStabilizer H m ∧
          ∀ (v : Fiber) (z : F3),
            q (fiberCoordinate x v z) =
              let target := correctedStateTarget H m x s w v z
              fiberCoordinate x target.1 target.2

end

end MathlibPlus.Open.ResearchFormalization.R1173CorrectedAction
