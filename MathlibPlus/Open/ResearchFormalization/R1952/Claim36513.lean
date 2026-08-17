import Mathlib

noncomputable section
open scoped BigOperators

namespace MathlibPlus.Open.ResearchFormalization.R1952

abbrev ReplayScalar := FractionRing (MvPolynomial (Fin 9) ℚ)

def replayVariable (i : Fin 9) : ReplayScalar :=
  algebraMap (MvPolynomial (Fin 9) ℚ) ReplayScalar (MvPolynomial.X i)

abbrev p : ReplayScalar := replayVariable 0
abbrev q : ReplayScalar := replayVariable 1
abbrev r : ReplayScalar := replayVariable 2
abbrev s : ReplayScalar := replayVariable 3
abbrev a : ReplayScalar := replayVariable 4
abbrev b : ReplayScalar := replayVariable 5
abbrev c : ReplayScalar := replayVariable 6
abbrev d : ReplayScalar := replayVariable 7
abbrev z : ReplayScalar := replayVariable 8

def crossedDifference : ReplayScalar := p * q - r * s

def Kpr : ReplayScalar :=
  z * crossedDifference + p * (b - c) + r * (a - d)
def Kps : ReplayScalar :=
  z * crossedDifference + p * (b - d) + s * (a - c)
def Kqr : ReplayScalar :=
  z * crossedDifference + q * (a - c) + r * (b - d)
def Kqs : ReplayScalar :=
  z * crossedDifference + q * (a - d) + s * (b - c)

def replayMatrix : Matrix (Fin 4) (Fin 4) ReplayScalar :=
  !![b - c, b - d, 0, 0;
     0, 0, a - c, a - d;
     a - d, 0, b - d, 0;
     0, a - c, 0, b - c]

def replayKernel : Fin 4 → ReplayScalar :=
  ![b - d, c - b, d - a, a - c]

def replayMinorRows : Fin 3 → Fin 4 := ![2, 1, 3]
def replayMinorColumns : Fin 3 → Fin 4 := ![1, 2, 3]

def replayMinor : Matrix (Fin 3) (Fin 3) ReplayScalar :=
  fun i j => replayMatrix (replayMinorRows i) (replayMinorColumns j)

def replayKernelIdentity : Prop :=
  Matrix.mulVec replayMatrix replayKernel = 0

def replayKernelUniqueness : Prop :=
  ∀ x : Fin 4 → ReplayScalar,
    Matrix.mulVec replayMatrix x = 0 →
      ∃ t : ReplayScalar, x = t • replayKernel

def replayCoordinateSum : Prop :=
  (replayKernel 0 + replayKernel 1 + replayKernel 2 + replayKernel 3) = 0

def replaySyzygy : Prop :=
  replayKernel 0 * Kpr + replayKernel 1 * Kps +
      replayKernel 2 * Kqr + replayKernel 3 * Kqs = 0

/-- Claim 36513: the all-order replay uses the four physical crossed-swap
 normalizations, the generic rank-three matrix/minor, its unique kernel,
 zero total-factor coefficient, and the induced exact syzygy. -/
def exactCrossedSwapReplayEvidence_claim36513 : Prop :=
  replayMatrix.rank = 3 ∧
    Matrix.det replayMinor =
      (a - c) * (a - d) * (b - d) ∧
      (a - c) * (a - d) * (b - d) ≠ 0 ∧
        replayKernelIdentity ∧ replayKernelUniqueness ∧
          replayCoordinateSum ∧ replaySyzygy

end MathlibPlus.Open.ResearchFormalization.R1952
