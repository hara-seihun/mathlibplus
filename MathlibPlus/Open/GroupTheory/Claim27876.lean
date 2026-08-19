import Mathlib

namespace MathlibPlus.Open.GroupTheory.Claim27876

abbrev Plane (p : ℕ) := ZMod p × ZMod p
abbrev Fiber (p : ℕ) := ZMod p × ZMod p × ZMod p
abbrev H (p : ℕ) := Plane p × Fiber p

def quadraticF (p : ℕ) (u : Plane p) : Fiber p :=
  (u.1 * (u.1 - 1),
    ((2 : ZMod p) * u.1 - 1) * u.2,
    u.2 ^ 2)

def displacementPlane (p : ℕ) (u : Plane p) :
    Submodule (ZMod p) (Fiber p) :=
  Submodule.span (ZMod p)
    ({(u.1, u.2, 0), (0, u.1, u.2)} : Set (Fiber p))

def affineDisplacementPlane (p : ℕ) (u : Plane p) : Set (Fiber p) :=
  {w | ∃ z : Fiber p,
    z ∈ displacementPlane p u ∧ w = quadraticF p u + z}

def orbitalDisplacementIdentity (p : ℕ) : Prop :=
  ∀ u v : Plane p, u ≠ 0 →
    quadraticF p (v + u) - quadraticF p v =
        (2 * v.1 + u.1 - 1) • (u.1, u.2, 0) +
          (2 * v.2 + u.2) • (0, u.1, u.2) ∧
      quadraticF p (v + u) - quadraticF p v ∈
        affineDisplacementPlane p u

def fiberShiftPermutation (p : ℕ) (s : Plane p → Fiber p) :
    Equiv.Perm (H p) :=
  ((Equiv.sigmaEquivProd (Plane p) (Fiber p)).symm.trans
      (Equiv.sigmaCongrRight
        (fun u : Plane p => Equiv.addRight (s u)))).trans
    (Equiv.sigmaEquivProd (Plane p) (Fiber p))

def rankFiveXGenerator (p : ℕ) : Equiv.Perm (H p) :=
  fiberShiftPermutation p (fun u => (u.1, u.2, 0))

def rankFiveYGenerator (p : ℕ) : Equiv.Perm (H p) :=
  fiberShiftPermutation p (fun u => (0, u.1, u.2))

def rankFiveQuadraticPermutation (p : ℕ) : Equiv.Perm (H p) :=
  fiberShiftPermutation p (quadraticF p)

def rankFiveTranslationGroup (p : ℕ) :
    Subgroup (Equiv.Perm (H p)) :=
  Subgroup.closure
    (Set.range (Equiv.addRight : H p → Equiv.Perm (H p)))

def rankFiveXGroup (p : ℕ) : Subgroup (Equiv.Perm (H p)) :=
  Subgroup.closure
    ((rankFiveTranslationGroup p : Set (Equiv.Perm (H p))) ∪
      ({rankFiveXGenerator p, rankFiveYGenerator p} :
        Set (Equiv.Perm (H p))))

def orderedOrbital {Ω : Type*}
    (X : Subgroup (Equiv.Perm Ω)) (pair : Ω × Ω) : Set (Ω × Ω) :=
  {q | ∃ k : Equiv.Perm Ω,
    k ∈ X ∧ q = (k pair.1, k pair.2)}

def preservesEveryOrbital {Ω : Type*}
    (X : Subgroup (Equiv.Perm Ω)) (q : Equiv.Perm Ω) : Prop :=
  ∀ pair : Ω × Ω,
    Set.image (fun r : Ω × Ω => (q r.1, q r.2))
        (orderedOrbital X pair) = orderedOrbital X pair

def twoClosure {Ω : Type*}
    (X : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {q | preservesEveryOrbital X q}

/-- Claim 27876: for every odd prime, the displayed quadratic permutation
preserves the genuine orbitals of the displayed rank-five group and therefore
belongs to its ordered-pair (quotient) 2-closure. -/
def claim27876 : Prop :=
  ∀ p : ℕ, Nat.Prime p → Odd p →
    orbitalDisplacementIdentity p →
      let X := rankFiveXGroup p
      let g := rankFiveQuadraticPermutation p
      preservesEveryOrbital X g ∧ g ∈ twoClosure X

end MathlibPlus.Open.GroupTheory.Claim27876
