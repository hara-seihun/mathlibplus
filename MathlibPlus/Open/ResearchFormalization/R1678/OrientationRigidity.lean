import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1678Orientation

noncomputable section

abbrev Point (p : ℕ) := Fin 6 → ZMod p
abbrev InvariantCoordinates (p : ℕ) := ZMod p × ZMod p

def binomTwo {p : ℕ} (x : ZMod p) : ZMod p :=
  x * (x - 1) * (2 : ZMod p)⁻¹

def deltaDeltaPointAction
    (p : ℕ) (r u v s t : ZMod p) (x : Point p) : Point p :=
  ![x 0,
    x 1 + r * x 0,
    x 2 + r * x 1 + binomTwo r * x 0 +
      u * (x 0 + x 4) + v * x 3 +
        (v ^ 2 * (2 : ZMod p)⁻¹) * x 4,
    x 3 + v * x 4,
    x 4,
    x 5 + u * x 0 + s * x 3 + t * x 4]

def deltaDeltaStabilizerStep
    (p : ℕ) (x y : Point p) : Prop :=
  ∃ r u v s t : ZMod p,
    deltaDeltaPointAction p r u v s t 0 = 0 ∧
      deltaDeltaPointAction p r u v s t x = y

def canonicalRelationColor (p : ℕ) (x : Point p) : Set (Point p) :=
  {y | Relation.ReflTransGen (deltaDeltaStabilizerStep p) x y}

def canonicalRelationColorFinset
    (p : ℕ) (hp : Nat.Prime p) (x : Point p) : Finset (Point p) := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : DecidablePred (fun y : Point p => y ∈ canonicalRelationColor p x) :=
    Classical.decPred _
  exact Finset.univ.filter (fun y => y ∈ canonicalRelationColor p x)

def pairedColor {p : ℕ} (C : Finset (Point p)) : Finset (Point p) := by
  classical
  exact C ∪ C.image (fun x => -x)

def schemeColor
    (p : ℕ) (hp : Nat.Prime p) (x : Point p) : Finset (Point p) :=
  pairedColor (canonicalRelationColorFinset p hp x)

def invariantCoordinates
    {p : ℕ} (x : Point p) : InvariantCoordinates p :=
  (x 0, x 4)

def symmetricColoredSchemeAutomorphism
    (p : ℕ) (hp : Nat.Prime p) (φ : Equiv.Perm (Point p)) : Prop :=
  φ 0 = 0 ∧
    ∀ x y : Point p,
      schemeColor p hp (y - x) =
        schemeColor p hp (φ y - φ x)

def inducesInvariantMap
    {p : ℕ} (φ : Equiv.Perm (Point p))
    (q : InvariantCoordinates p → InvariantCoordinates p) : Prop :=
  ∀ x : Point p, q (invariantCoordinates x) = invariantCoordinates (φ x)

def orientationDifferenceSign
    {p : ℕ} (q : InvariantCoordinates p → InvariantCoordinates p) : Prop :=
  ∃ ε : ZMod p,
    (ε = 1 ∨ ε = -1) ∧
      ∀ x y : InvariantCoordinates p,
        q y - q x = ε • (y - x)

/-- Claim 33209: a zero-fixing automorphism of the symmetric colored scheme
has one global orientation sign on `(a,e)`, and after output inversion the
positive orientation has the stated `B` and `D` coordinate form. -/
def claim33209_globalOrientationRigidity : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p) (φ : Equiv.Perm (Point p)),
    symmetricColoredSchemeAutomorphism p hp φ →
    ∃ ε : ZMod p,
      (ε = 1 ∨ ε = -1) ∧
        (∃ q : InvariantCoordinates p → InvariantCoordinates p,
          inducesInvariantMap φ q ∧
            ∀ x y : InvariantCoordinates p,
              q y - q x = ε • (y - x)) ∧
        ∃ φ' : Equiv.Perm (Point p),
          ∃ q' : InvariantCoordinates p → InvariantCoordinates p,
            ∃ g k : ZMod p → ZMod p,
              ((ε = 1 ∧ φ' = φ) ∨
                (ε = -1 ∧
                  φ' = φ.trans (Equiv.neg (Point p)))) ∧
              inducesInvariantMap φ' q' ∧
              (∀ x y : InvariantCoordinates p,
                q' y - q' x = y - x) ∧
              (∀ x : Point p,
                φ' x 1 = x 1 + g (x 0) ∧
                  φ' x 3 = x 3 + k (x 4))

end

end MathlibPlus.Open.ResearchFormalization.R1678Orientation
