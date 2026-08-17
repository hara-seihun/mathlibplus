import Mathlib

namespace MathlibPlus.Open.ResearchFormalization.R1678Rank

noncomputable section

abbrev Point (p : ℕ) := Fin 6 → ZMod p

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

def pairedColors
    (p : ℕ) (hp : Nat.Prime p) : Finset (Finset (Point p)) := by
  classical
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  exact (Finset.univ.image (canonicalRelationColorFinset p hp)).image pairedColor

def identityPairedColor
    (p : ℕ) (hp : Nat.Prime p) : Finset (Point p) :=
  pairedColor (canonicalRelationColorFinset p hp 0)

def pairedRank (p : ℕ) (hp : Nat.Prime p) : ℕ := by
  classical
  exact ((pairedColors p hp).filter
      (fun C => C ≠ identityPairedColor p hp)).card + 1

/-- Claim 33208: the eight inverse-paired families, with the diagonal
relation included, have the stated paired rank. -/
def claim33208_pairedRank : Prop :=
  ∀ (p : ℕ) (hp : Nat.Prime p),
    pairedRank p hp = 4 * p ^ 2 - 5 * p + 2

end

end MathlibPlus.Open.ResearchFormalization.R1678Rank
