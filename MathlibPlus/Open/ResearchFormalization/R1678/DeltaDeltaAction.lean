import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1678Action

noncomputable section

abbrev Point (p : ℕ) := Fin 6 → ZMod p

def binomTwo {p : ℕ} (x : ZMod p) : ZMod p :=
  x * (x - 1) * (2 : ZMod p)⁻¹

/-- The full-product delta-delta point action, with the displayed
`(v^2/2)e` term kept distinct from `binom(v,2)e`. -/
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

def inversePairedColor
    (p : ℕ) (hp : Nat.Prime p) (x : Point p) : Finset (Point p) := by
  classical
  exact (canonicalRelationColorFinset p hp x).image (fun y => -y)

/-- Claim 33206: the canonical colors are the point-stabilizer orbit colors
of the displayed full-product action, and inverse pairs are obtained by
negating the directed color. -/
def claim33206_fullProductDeltaDeltaPointAction : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    canonicalRelationColorFinset p hp 0 = {0} ∧
      ∀ x : Point p,
        inversePairedColor p hp x =
          canonicalRelationColorFinset p hp (-x)

end

end MathlibPlus.Open.ResearchFormalization.R1678Action
